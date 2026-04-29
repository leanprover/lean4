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
extern lean_object* l_Lean_backward_defeqAttrib_useBackward;
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
lean_dec_ref(v___x_200_);
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_s_192_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_ctor_set(v___x_202_, 2, v___x_194_);
v___x_203_ = l_String_Slice_isNat(v___x_202_);
lean_dec_ref(v___x_202_);
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
lean_dec_ref(v_name_251_);
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
lean_dec_ref(v___x_259_);
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
lean_dec_ref(v_fst_263_);
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
lean_object* v___x_286_; uint8_t v_isModule_287_; 
v___x_286_ = l_Lean_Environment_header(v_env_280_);
v_isModule_287_ = lean_ctor_get_uint8(v___x_286_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_286_);
if (v_isModule_287_ == 0)
{
lean_object* v_name_288_; 
lean_dec_ref(v_env_280_);
v_name_288_ = l_Lean_Name_str___override(v_declName_281_, v_suffix_282_);
return v_name_288_;
}
else
{
uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = 0;
lean_inc_ref(v_env_280_);
v___x_290_ = l_Lean_Environment_setExporting(v_env_280_, v_isModule_287_);
lean_inc(v_declName_281_);
v___x_291_ = l_Lean_Environment_find_x3f(v___x_290_, v_declName_281_, v___x_289_);
if (lean_obj_tag(v___x_291_) == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v_val_292_; uint8_t v___x_293_; 
v_val_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_292_);
lean_dec_ref(v___x_291_);
v___x_293_ = l_Lean_ConstantInfo_hasValue(v_val_292_, v___x_289_);
lean_dec(v_val_292_);
if (v___x_293_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v_name_294_; 
lean_dec_ref(v_env_280_);
v_name_294_ = l_Lean_Name_str___override(v_declName_281_, v_suffix_282_);
return v_name_294_;
}
}
}
v___jp_283_:
{
lean_object* v_name_284_; lean_object* v___x_285_; 
v_name_284_ = l_Lean_Name_str___override(v_declName_281_, v_suffix_282_);
v___x_285_ = l_Lean_mkPrivateName(v_env_280_, v_name_284_);
lean_dec_ref(v_env_280_);
return v___x_285_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_295_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
lean_ctor_set(v___x_300_, 2, v___x_299_);
lean_ctor_set(v___x_300_, 3, v___x_299_);
lean_ctor_set(v___x_300_, 4, v___x_298_);
lean_ctor_set(v___x_300_, 5, v___x_298_);
lean_ctor_set(v___x_300_, 6, v___x_298_);
lean_ctor_set(v___x_300_, 7, v___x_298_);
lean_ctor_set(v___x_300_, 8, v___x_298_);
lean_ctor_set(v___x_300_, 9, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_unsigned_to_nat(32u);
v___x_302_ = lean_mk_empty_array_with_capacity(v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_304_ = ((size_t)5ULL);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_unsigned_to_nat(32u);
v___x_307_ = lean_mk_empty_array_with_capacity(v___x_306_);
v___x_308_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_309_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_305_);
lean_ctor_set(v___x_309_, 3, v___x_305_);
lean_ctor_set_usize(v___x_309_, 4, v___x_304_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_box(1);
v___x_311_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_312_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_310_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; lean_object* v_env_319_; lean_object* v_options_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_318_ = lean_st_ref_get(v___y_316_);
v_env_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc_ref(v_env_319_);
lean_dec(v___x_318_);
v_options_320_ = lean_ctor_get(v___y_315_, 2);
v___x_321_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_322_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_320_);
v___x_323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_323_, 0, v_env_319_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
lean_ctor_set(v___x_323_, 3, v_options_320_);
v___x_324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_msgData_314_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_ref_335_; lean_object* v___x_336_; lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
v_ref_335_ = lean_ctor_get(v___y_332_, 5);
v___x_336_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_331_, v___y_332_, v___y_333_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_345_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_inc(v_ref_335_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_ref_335_);
lean_ctor_set(v___x_341_, 1, v_a_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 1);
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_350_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_360_, lean_object* v_reservedName_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_365_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_366_ = 0;
v___x_367_ = l_Lean_MessageData_ofConstName(v_declName_360_, v___x_366_);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_365_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = 1;
v___x_372_ = l_Lean_MessageData_ofConstName(v_reservedName_361_, v___x_371_);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_370_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_375_, v___y_362_, v___y_363_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_377_, lean_object* v_reservedName_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_377_, v_reservedName_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_383_, lean_object* v_suffix_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v_env_389_; lean_object* v_reservedName_390_; uint8_t v___x_391_; uint8_t v___x_392_; 
v___x_388_ = lean_st_ref_get(v___y_386_);
v_env_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_388_);
lean_inc(v_declName_383_);
v_reservedName_390_ = l_Lean_Name_str___override(v_declName_383_, v_suffix_384_);
v___x_391_ = 1;
lean_inc(v_reservedName_390_);
v___x_392_ = l_Lean_Environment_contains(v_env_389_, v_reservedName_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_reservedName_390_);
lean_dec(v_declName_383_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_383_, v_reservedName_390_, v___y_385_, v___y_386_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_396_, lean_object* v_suffix_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_396_, v_suffix_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_402_);
v___x_407_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_402_, v___x_406_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v___x_407_);
v___x_408_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_402_);
v___x_409_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_402_, v___x_408_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref(v___x_409_);
v___x_410_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_411_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_402_, v___x_410_, v_a_403_, v_a_404_);
return v___x_411_;
}
else
{
lean_dec(v_declName_402_);
return v___x_409_;
}
}
else
{
lean_dec(v_declName_402_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_417_, lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_418_, v___y_419_, v___y_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_423_, lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_423_, v_msg_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_429_, lean_object* v_n_430_){
_start:
{
lean_object* v___x_431_; 
lean_inc(v_n_430_);
lean_inc_ref(v_env_429_);
v___x_431_ = l_Lean_Meta_declFromEqLikeName(v_env_429_, v_n_430_);
if (lean_obj_tag(v___x_431_) == 1)
{
lean_object* v_val_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_val_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_432_);
lean_dec_ref(v___x_431_);
v_fst_433_ = lean_ctor_get(v_val_432_, 0);
lean_inc(v_fst_433_);
v_snd_434_ = lean_ctor_get(v_val_432_, 1);
lean_inc(v_snd_434_);
lean_dec(v_val_432_);
v___x_435_ = l_Lean_Meta_mkEqLikeNameFor(v_env_429_, v_fst_433_, v_snd_434_);
v___x_436_ = lean_name_eq(v_n_430_, v___x_435_);
lean_dec(v___x_435_);
lean_dec(v_n_430_);
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
lean_dec(v___x_431_);
lean_dec(v_n_430_);
lean_dec_ref(v_env_429_);
v___x_437_ = 0;
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_438_, lean_object* v_n_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_438_, v_n_439_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; 
v___f_444_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_445_ = l_Lean_registerReservedNamePredicate(v___f_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_box(0);
v___x_450_ = lean_st_mk_ref(v___x_449_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_453_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_456_ = lean_mk_io_user_error(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_initializing();
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_476_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_476_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
uint8_t v___x_464_; 
v___x_464_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_467_; 
lean_dec_ref(v_f_457_);
v___x_465_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_463_ == 0)
{
lean_ctor_set_tag(v___x_462_, 1);
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_469_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_470_ = lean_st_ref_take(v___x_469_);
v___x_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_471_, 0, v_f_457_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_st_ref_set(v___x_469_, v___x_471_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_472_);
v___x_474_ = v___x_462_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec_ref(v_f_457_);
v_a_477_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_459_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_459_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Meta_registerGetEqnsFn(v_f_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_498_; lean_object* v_env_499_; uint8_t v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_st_ref_get(v_a_492_);
v_env_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_env_499_);
lean_dec(v___x_498_);
v___x_500_ = 0;
lean_inc(v_declName_488_);
v___x_501_ = l_Lean_Environment_findAsync_x3f(v_env_499_, v_declName_488_, v___x_500_);
if (lean_obj_tag(v___x_501_) == 1)
{
lean_object* v_val_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_533_; 
v_val_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_533_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_533_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_val_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_533_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v_kind_506_; 
v_kind_506_ = lean_ctor_get_uint8(v_val_502_, sizeof(void*)*3);
if (v_kind_506_ == 0)
{
lean_object* v_sig_507_; lean_object* v___x_508_; lean_object* v_env_509_; uint8_t v___x_510_; 
v_sig_507_ = lean_ctor_get(v_val_502_, 1);
lean_inc_ref(v_sig_507_);
lean_dec(v_val_502_);
v___x_508_ = lean_st_ref_get(v_a_492_);
v_env_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc_ref(v_env_509_);
lean_dec(v___x_508_);
v___x_510_ = lean_is_matcher(v_env_509_, v_declName_488_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v_type_512_; lean_object* v___x_513_; 
lean_del_object(v___x_504_);
v___x_511_ = lean_task_get_own(v_sig_507_);
v_type_512_ = lean_ctor_get(v___x_511_, 2);
lean_inc_ref(v_type_512_);
lean_dec(v___x_511_);
v___x_513_ = l_Lean_Meta_isProp(v_type_512_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_528_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_528_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_528_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_528_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = lean_unbox(v_a_514_);
lean_dec(v_a_514_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = 1;
v___x_520_ = lean_box(v___x_519_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_520_);
v___x_522_ = v___x_516_;
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
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_box(v___x_510_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_524_);
v___x_526_ = v___x_516_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
return v___x_513_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_531_; 
lean_dec_ref(v_sig_507_);
v___x_529_ = lean_box(v___x_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 0);
lean_ctor_set(v___x_504_, 0, v___x_529_);
v___x_531_ = v___x_504_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_del_object(v___x_504_);
lean_dec(v_val_502_);
lean_dec(v_declName_488_);
goto v___jp_494_;
}
}
}
else
{
lean_dec(v___x_501_);
lean_dec(v_declName_488_);
goto v___jp_494_;
}
v___jp_494_:
{
uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = 0;
v___x_496_ = lean_box(v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_540_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_549_);
return v_res_551_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_552_; lean_object* v___f_553_; 
v___x_552_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_553_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_553_, 0, v___x_552_);
return v___f_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___f_555_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_box(1);
v___x_558_ = l_Lean_registerEnvExtension___redArg(v___f_555_, v___x_556_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_561_, lean_object* v_opt_562_){
_start:
{
lean_object* v_name_563_; lean_object* v_defValue_564_; lean_object* v_map_565_; lean_object* v___x_566_; 
v_name_563_ = lean_ctor_get(v_opt_562_, 0);
v_defValue_564_ = lean_ctor_get(v_opt_562_, 1);
v_map_565_ = lean_ctor_get(v_opts_561_, 0);
v___x_566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_565_, v_name_563_);
if (lean_obj_tag(v___x_566_) == 0)
{
uint8_t v___x_567_; 
v___x_567_ = lean_unbox(v_defValue_564_);
return v___x_567_;
}
else
{
lean_object* v_val_568_; 
v_val_568_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_val_568_);
lean_dec_ref(v___x_566_);
if (lean_obj_tag(v_val_568_) == 1)
{
uint8_t v_v_569_; 
v_v_569_ = lean_ctor_get_uint8(v_val_568_, 0);
lean_dec_ref(v_val_568_);
return v_v_569_;
}
else
{
uint8_t v___x_570_; 
lean_dec(v_val_568_);
v___x_570_ = lean_unbox(v_defValue_564_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_571_, lean_object* v_opt_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_571_, v_opt_572_);
lean_dec_ref(v_opt_572_);
lean_dec_ref(v_opts_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_opts_575_, lean_object* v_opt_576_){
_start:
{
lean_object* v_name_577_; lean_object* v_defValue_578_; lean_object* v_map_579_; lean_object* v___x_580_; 
v_name_577_ = lean_ctor_get(v_opt_576_, 0);
v_defValue_578_ = lean_ctor_get(v_opt_576_, 1);
v_map_579_ = lean_ctor_get(v_opts_575_, 0);
v___x_580_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_579_, v_name_577_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_inc(v_defValue_578_);
return v_defValue_578_;
}
else
{
lean_object* v_val_581_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v___x_580_);
if (lean_obj_tag(v_val_581_) == 3)
{
lean_object* v_v_582_; 
v_v_582_ = lean_ctor_get(v_val_581_, 0);
lean_inc(v_v_582_);
lean_dec_ref(v_val_581_);
return v_v_582_;
}
else
{
lean_dec(v_val_581_);
lean_inc(v_defValue_578_);
return v_defValue_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_opts_583_, lean_object* v_opt_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_583_, v_opt_584_);
lean_dec_ref(v_opt_584_);
lean_dec_ref(v_opts_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_589_, size_t v_sz_590_, size_t v_i_591_, lean_object* v_b_592_){
_start:
{
lean_object* v_a_594_; uint8_t v___x_598_; 
v___x_598_ = lean_usize_dec_lt(v_i_591_, v_sz_590_);
if (v___x_598_ == 0)
{
return v_b_592_;
}
else
{
lean_object* v_a_599_; lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v_map_602_; uint8_t v_hasTrace_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_616_; 
v_a_599_ = lean_array_uget_borrowed(v_as_589_, v_i_591_);
v_fst_600_ = lean_ctor_get(v_a_599_, 0);
v_snd_601_ = lean_ctor_get(v_a_599_, 1);
v_map_602_ = lean_ctor_get(v_b_592_, 0);
v_hasTrace_603_ = lean_ctor_get_uint8(v_b_592_, sizeof(void*)*1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_b_592_);
if (v_isSharedCheck_616_ == 0)
{
v___x_605_ = v_b_592_;
v_isShared_606_ = v_isSharedCheck_616_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_map_602_);
lean_dec(v_b_592_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_616_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; 
lean_inc(v_snd_601_);
lean_inc(v_fst_600_);
v___x_607_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_600_, v_snd_601_, v_map_602_);
if (v_hasTrace_603_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_611_; 
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_609_ = l_Lean_Name_isPrefixOf(v___x_608_, v_fst_600_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_607_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*1, v___x_609_);
v_a_594_ = v___x_611_;
goto v___jp_593_;
}
}
else
{
lean_object* v___x_614_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_614_ = v___x_605_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_607_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*1, v_hasTrace_603_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v_a_594_ = v___x_614_;
goto v___jp_593_;
}
}
}
}
v___jp_593_:
{
size_t v___x_595_; size_t v___x_596_; 
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_591_, v___x_595_);
v_i_591_ = v___x_596_;
v_b_592_ = v_a_594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_617_, lean_object* v_sz_618_, lean_object* v_i_619_, lean_object* v_b_620_){
_start:
{
size_t v_sz_boxed_621_; size_t v_i_boxed_622_; lean_object* v_res_623_; 
v_sz_boxed_621_ = lean_unbox_usize(v_sz_618_);
lean_dec(v_sz_618_);
v_i_boxed_622_ = lean_unbox_usize(v_i_619_);
lean_dec(v_i_619_);
v_res_623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_617_, v_sz_boxed_621_, v_i_boxed_622_, v_b_620_);
lean_dec_ref(v_as_617_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_624_, lean_object* v_k_625_, uint8_t v_v_626_){
_start:
{
lean_object* v_map_627_; uint8_t v_hasTrace_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_642_; 
v_map_627_ = lean_ctor_get(v_o_624_, 0);
v_hasTrace_628_ = lean_ctor_get_uint8(v_o_624_, sizeof(void*)*1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_o_624_);
if (v_isSharedCheck_642_ == 0)
{
v___x_630_ = v_o_624_;
v_isShared_631_ = v_isSharedCheck_642_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_map_627_);
lean_dec(v_o_624_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_642_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_632_, 0, v_v_626_);
lean_inc(v_k_625_);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_625_, v___x_632_, v_map_627_);
if (v_hasTrace_628_ == 0)
{
lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_637_; 
v___x_634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_635_ = l_Lean_Name_isPrefixOf(v___x_634_, v_k_625_);
lean_dec(v_k_625_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_633_);
v___x_637_ = v___x_630_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_633_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*1, v___x_635_);
return v___x_637_;
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v_k_625_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_633_);
v___x_640_ = v___x_630_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_633_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, sizeof(void*)*1, v_hasTrace_628_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_643_, lean_object* v_k_644_, lean_object* v_v_645_){
_start:
{
uint8_t v_v_boxed_646_; lean_object* v_res_647_; 
v_v_boxed_646_ = lean_unbox(v_v_645_);
v_res_647_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_643_, v_k_644_, v_v_boxed_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_648_, lean_object* v_opt_649_, uint8_t v_val_650_){
_start:
{
lean_object* v_name_651_; lean_object* v___x_652_; 
v_name_651_ = lean_ctor_get(v_opt_649_, 0);
lean_inc(v_name_651_);
lean_dec_ref(v_opt_649_);
v___x_652_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_648_, v_name_651_, v_val_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_653_, lean_object* v_opt_654_, lean_object* v_val_655_){
_start:
{
uint8_t v_val_boxed_656_; lean_object* v_res_657_; 
v_val_boxed_656_ = lean_unbox(v_val_655_);
v_res_657_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_653_, v_opt_654_, v_val_boxed_656_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object* v_as_658_, size_t v_i_659_, size_t v_stop_660_, lean_object* v_b_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_eq(v_i_659_, v_stop_660_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v_defValue_664_; uint8_t v___x_665_; lean_object* v___x_666_; size_t v___x_667_; size_t v___x_668_; 
v___x_663_ = lean_array_uget_borrowed(v_as_658_, v_i_659_);
v_defValue_664_ = lean_ctor_get(v___x_663_, 1);
v___x_665_ = lean_unbox(v_defValue_664_);
lean_inc(v___x_663_);
v___x_666_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_661_, v___x_663_, v___x_665_);
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_add(v_i_659_, v___x_667_);
v_i_659_ = v___x_668_;
v_b_661_ = v___x_666_;
goto _start;
}
else
{
return v_b_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object* v_as_670_, lean_object* v_i_671_, lean_object* v_stop_672_, lean_object* v_b_673_){
_start:
{
size_t v_i_boxed_674_; size_t v_stop_boxed_675_; lean_object* v_res_676_; 
v_i_boxed_674_ = lean_unbox_usize(v_i_671_);
lean_dec(v_i_671_);
v_stop_boxed_675_ = lean_unbox_usize(v_stop_672_);
lean_dec(v_stop_672_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_670_, v_i_boxed_674_, v_stop_boxed_675_, v_b_673_);
lean_dec_ref(v_as_670_);
return v_res_676_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Array_instInhabited(lean_box(0));
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l_Lean_Meta_eqnAffectingOptions;
v___x_684_ = lean_array_get_size(v___x_683_);
return v___x_684_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_nat_dec_lt(v___x_686_, v___x_685_);
return v___x_687_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_689_ = lean_nat_dec_le(v___x_688_, v___x_688_);
return v___x_689_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__7(void){
_start:
{
lean_object* v___x_690_; size_t v___x_691_; 
v___x_690_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_691_ = lean_usize_of_nat(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_692_, lean_object* v_act_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___y_700_; uint8_t v___y_701_; lean_object* v_fileName_702_; lean_object* v_fileMap_703_; lean_object* v_currRecDepth_704_; lean_object* v_ref_705_; lean_object* v_currNamespace_706_; lean_object* v_openDecls_707_; lean_object* v_initHeartbeats_708_; lean_object* v_maxHeartbeats_709_; lean_object* v_quotContext_710_; lean_object* v_currMacroScope_711_; lean_object* v_cancelTk_x3f_712_; uint8_t v_suppressElabErrors_713_; lean_object* v_inheritedTraceOptions_714_; lean_object* v___y_715_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_env_722_; lean_object* v___x_723_; lean_object* v_toEnvExtension_724_; lean_object* v_asyncMode_725_; lean_object* v_fileName_726_; lean_object* v_fileMap_727_; lean_object* v_options_728_; lean_object* v_currRecDepth_729_; lean_object* v_ref_730_; lean_object* v_currNamespace_731_; lean_object* v_openDecls_732_; lean_object* v_initHeartbeats_733_; lean_object* v_maxHeartbeats_734_; lean_object* v_quotContext_735_; lean_object* v_currMacroScope_736_; lean_object* v_cancelTk_x3f_737_; uint8_t v_suppressElabErrors_738_; lean_object* v_inheritedTraceOptions_739_; lean_object* v___y_741_; uint8_t v___y_742_; uint8_t v___y_743_; lean_object* v___y_765_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; 
v___x_720_ = lean_st_ref_get(v_a_697_);
v___x_721_ = lean_st_ref_get(v_a_697_);
v_env_722_ = lean_ctor_get(v___x_720_, 0);
lean_inc_ref(v_env_722_);
lean_dec(v___x_720_);
v___x_723_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_724_ = lean_ctor_get(v___x_723_, 0);
v_asyncMode_725_ = lean_ctor_get(v_toEnvExtension_724_, 2);
v_fileName_726_ = lean_ctor_get(v_a_696_, 0);
v_fileMap_727_ = lean_ctor_get(v_a_696_, 1);
v_options_728_ = lean_ctor_get(v_a_696_, 2);
v_currRecDepth_729_ = lean_ctor_get(v_a_696_, 3);
v_ref_730_ = lean_ctor_get(v_a_696_, 5);
v_currNamespace_731_ = lean_ctor_get(v_a_696_, 6);
v_openDecls_732_ = lean_ctor_get(v_a_696_, 7);
v_initHeartbeats_733_ = lean_ctor_get(v_a_696_, 8);
v_maxHeartbeats_734_ = lean_ctor_get(v_a_696_, 9);
v_quotContext_735_ = lean_ctor_get(v_a_696_, 10);
v_currMacroScope_736_ = lean_ctor_get(v_a_696_, 11);
v_cancelTk_x3f_737_ = lean_ctor_get(v_a_696_, 12);
v_suppressElabErrors_738_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_739_ = lean_ctor_get(v_a_696_, 13);
v___x_770_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_771_ = 0;
v___x_772_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_770_, v___x_723_, v_env_722_, v_declName_692_, v_asyncMode_725_, v___x_771_);
if (lean_obj_tag(v___x_772_) == 1)
{
lean_object* v_val_773_; lean_object* v___y_775_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_val_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_773_);
lean_dec_ref(v___x_772_);
v___x_779_ = l_Lean_Meta_eqnAffectingOptions;
v___x_780_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_780_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_775_ = v_options_728_;
goto v___jp_774_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_781_ == 0)
{
if (v___x_780_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_775_ = v_options_728_;
goto v___jp_774_;
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_779_, v___x_782_, v___x_783_, v_options_728_);
v___y_775_ = v___x_784_;
goto v___jp_774_;
}
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_779_, v___x_785_, v___x_786_, v_options_728_);
v___y_775_ = v___x_787_;
goto v___jp_774_;
}
}
v___jp_774_:
{
size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
v_sz_776_ = lean_array_size(v_val_773_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_773_, v_sz_776_, v___x_777_, v___y_775_);
lean_dec(v_val_773_);
v___y_765_ = v___x_778_;
goto v___jp_764_;
}
}
else
{
lean_object* v___x_788_; uint8_t v___x_789_; 
lean_dec(v___x_772_);
v___x_788_ = l_Lean_Meta_eqnAffectingOptions;
v___x_789_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_789_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_765_ = v_options_728_;
goto v___jp_764_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_790_ == 0)
{
if (v___x_789_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_765_ = v_options_728_;
goto v___jp_764_;
}
else
{
size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
v___x_791_ = ((size_t)0ULL);
v___x_792_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_788_, v___x_791_, v___x_792_, v_options_728_);
v___y_765_ = v___x_793_;
goto v___jp_764_;
}
}
else
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((size_t)0ULL);
v___x_795_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_788_, v___x_794_, v___x_795_, v_options_728_);
v___y_765_ = v___x_796_;
goto v___jp_764_;
}
}
}
v___jp_699_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = l_Lean_maxRecDepth;
v___x_717_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_700_, v___x_716_);
lean_inc_ref(v_inheritedTraceOptions_714_);
lean_inc(v_cancelTk_x3f_712_);
lean_inc(v_currMacroScope_711_);
lean_inc(v_quotContext_710_);
lean_inc(v_maxHeartbeats_709_);
lean_inc(v_initHeartbeats_708_);
lean_inc(v_openDecls_707_);
lean_inc(v_currNamespace_706_);
lean_inc(v_ref_705_);
lean_inc(v_currRecDepth_704_);
lean_inc_ref(v_fileMap_703_);
lean_inc_ref(v_fileName_702_);
v___x_718_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_718_, 0, v_fileName_702_);
lean_ctor_set(v___x_718_, 1, v_fileMap_703_);
lean_ctor_set(v___x_718_, 2, v___y_700_);
lean_ctor_set(v___x_718_, 3, v_currRecDepth_704_);
lean_ctor_set(v___x_718_, 4, v___x_717_);
lean_ctor_set(v___x_718_, 5, v_ref_705_);
lean_ctor_set(v___x_718_, 6, v_currNamespace_706_);
lean_ctor_set(v___x_718_, 7, v_openDecls_707_);
lean_ctor_set(v___x_718_, 8, v_initHeartbeats_708_);
lean_ctor_set(v___x_718_, 9, v_maxHeartbeats_709_);
lean_ctor_set(v___x_718_, 10, v_quotContext_710_);
lean_ctor_set(v___x_718_, 11, v_currMacroScope_711_);
lean_ctor_set(v___x_718_, 12, v_cancelTk_x3f_712_);
lean_ctor_set(v___x_718_, 13, v_inheritedTraceOptions_714_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*14, v___y_701_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*14 + 1, v_suppressElabErrors_713_);
lean_inc(v___y_715_);
lean_inc(v_a_695_);
lean_inc_ref(v_a_694_);
v___x_719_ = lean_apply_5(v_act_693_, v_a_694_, v_a_695_, v___x_718_, v___y_715_, lean_box(0));
return v___x_719_;
}
v___jp_740_:
{
if (v___y_743_ == 0)
{
lean_object* v___x_744_; lean_object* v_env_745_; lean_object* v_nextMacroScope_746_; lean_object* v_ngen_747_; lean_object* v_auxDeclNGen_748_; lean_object* v_traceState_749_; lean_object* v_messages_750_; lean_object* v_infoState_751_; lean_object* v_snapshotTasks_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_762_; 
v___x_744_ = lean_st_ref_take(v_a_697_);
v_env_745_ = lean_ctor_get(v___x_744_, 0);
v_nextMacroScope_746_ = lean_ctor_get(v___x_744_, 1);
v_ngen_747_ = lean_ctor_get(v___x_744_, 2);
v_auxDeclNGen_748_ = lean_ctor_get(v___x_744_, 3);
v_traceState_749_ = lean_ctor_get(v___x_744_, 4);
v_messages_750_ = lean_ctor_get(v___x_744_, 6);
v_infoState_751_ = lean_ctor_get(v___x_744_, 7);
v_snapshotTasks_752_ = lean_ctor_get(v___x_744_, 8);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_744_, 5);
lean_dec(v_unused_763_);
v___x_754_ = v___x_744_;
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_snapshotTasks_752_);
lean_inc(v_infoState_751_);
lean_inc(v_messages_750_);
lean_inc(v_traceState_749_);
lean_inc(v_auxDeclNGen_748_);
lean_inc(v_ngen_747_);
lean_inc(v_nextMacroScope_746_);
lean_inc(v_env_745_);
lean_dec(v___x_744_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_756_ = l_Lean_Kernel_enableDiag(v_env_745_, v___y_742_);
v___x_757_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 5, v___x_757_);
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_759_ = v___x_754_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_nextMacroScope_746_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_ngen_747_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_auxDeclNGen_748_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_traceState_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 5, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_761_, 6, v_messages_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 7, v_infoState_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 8, v_snapshotTasks_752_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
v___x_760_ = lean_st_ref_set(v_a_697_, v___x_759_);
v___y_700_ = v___y_741_;
v___y_701_ = v___y_742_;
v_fileName_702_ = v_fileName_726_;
v_fileMap_703_ = v_fileMap_727_;
v_currRecDepth_704_ = v_currRecDepth_729_;
v_ref_705_ = v_ref_730_;
v_currNamespace_706_ = v_currNamespace_731_;
v_openDecls_707_ = v_openDecls_732_;
v_initHeartbeats_708_ = v_initHeartbeats_733_;
v_maxHeartbeats_709_ = v_maxHeartbeats_734_;
v_quotContext_710_ = v_quotContext_735_;
v_currMacroScope_711_ = v_currMacroScope_736_;
v_cancelTk_x3f_712_ = v_cancelTk_x3f_737_;
v_suppressElabErrors_713_ = v_suppressElabErrors_738_;
v_inheritedTraceOptions_714_ = v_inheritedTraceOptions_739_;
v___y_715_ = v_a_697_;
goto v___jp_699_;
}
}
}
else
{
v___y_700_ = v___y_741_;
v___y_701_ = v___y_742_;
v_fileName_702_ = v_fileName_726_;
v_fileMap_703_ = v_fileMap_727_;
v_currRecDepth_704_ = v_currRecDepth_729_;
v_ref_705_ = v_ref_730_;
v_currNamespace_706_ = v_currNamespace_731_;
v_openDecls_707_ = v_openDecls_732_;
v_initHeartbeats_708_ = v_initHeartbeats_733_;
v_maxHeartbeats_709_ = v_maxHeartbeats_734_;
v_quotContext_710_ = v_quotContext_735_;
v_currMacroScope_711_ = v_currMacroScope_736_;
v_cancelTk_x3f_712_ = v_cancelTk_x3f_737_;
v_suppressElabErrors_713_ = v_suppressElabErrors_738_;
v_inheritedTraceOptions_714_ = v_inheritedTraceOptions_739_;
v___y_715_ = v_a_697_;
goto v___jp_699_;
}
}
v___jp_764_:
{
lean_object* v_env_766_; lean_object* v___x_767_; uint8_t v___x_768_; uint8_t v___x_769_; 
v_env_766_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_env_766_);
lean_dec(v___x_721_);
v___x_767_ = l_Lean_diagnostics;
v___x_768_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_765_, v___x_767_);
v___x_769_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_766_);
lean_dec_ref(v_env_766_);
if (v___x_769_ == 0)
{
if (v___x_768_ == 0)
{
v___y_700_ = v___y_765_;
v___y_701_ = v___x_768_;
v_fileName_702_ = v_fileName_726_;
v_fileMap_703_ = v_fileMap_727_;
v_currRecDepth_704_ = v_currRecDepth_729_;
v_ref_705_ = v_ref_730_;
v_currNamespace_706_ = v_currNamespace_731_;
v_openDecls_707_ = v_openDecls_732_;
v_initHeartbeats_708_ = v_initHeartbeats_733_;
v_maxHeartbeats_709_ = v_maxHeartbeats_734_;
v_quotContext_710_ = v_quotContext_735_;
v_currMacroScope_711_ = v_currMacroScope_736_;
v_cancelTk_x3f_712_ = v_cancelTk_x3f_737_;
v_suppressElabErrors_713_ = v_suppressElabErrors_738_;
v_inheritedTraceOptions_714_ = v_inheritedTraceOptions_739_;
v___y_715_ = v_a_697_;
goto v___jp_699_;
}
else
{
v___y_741_ = v___y_765_;
v___y_742_ = v___x_768_;
v___y_743_ = v___x_769_;
goto v___jp_740_;
}
}
else
{
v___y_741_ = v___y_765_;
v___y_742_ = v___x_768_;
v___y_743_ = v___x_768_;
goto v___jp_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_797_, lean_object* v_act_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_797_, v_act_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_805_, lean_object* v_declName_806_, lean_object* v_act_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_806_, v_act_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_814_, lean_object* v_declName_815_, lean_object* v_act_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_814_, v_declName_815_, v_act_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v_env_827_; lean_object* v_toConstantVal_828_; lean_object* v_value_829_; lean_object* v_all_830_; uint8_t v___y_832_; lean_object* v_type_840_; uint8_t v___x_841_; 
v___x_826_ = lean_st_ref_get(v___y_824_);
v_env_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_ref_n(v_env_827_, 2);
lean_dec(v___x_826_);
v_toConstantVal_828_ = lean_ctor_get(v_thm_823_, 0);
v_value_829_ = lean_ctor_get(v_thm_823_, 1);
v_all_830_ = lean_ctor_get(v_thm_823_, 2);
v_type_840_ = lean_ctor_get(v_toConstantVal_828_, 2);
v___x_841_ = l_Lean_Environment_hasUnsafe(v_env_827_, v_type_840_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_Environment_hasUnsafe(v_env_827_, v_value_829_);
v___y_832_ = v___x_842_;
goto v___jp_831_;
}
else
{
lean_dec_ref(v_env_827_);
v___y_832_ = v___x_841_;
goto v___jp_831_;
}
v___jp_831_:
{
if (v___y_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_833_, 0, v_thm_823_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_inc(v_all_830_);
lean_inc_ref(v_value_829_);
lean_inc_ref(v_toConstantVal_828_);
lean_dec_ref(v_thm_823_);
v___x_835_ = lean_box(0);
v___x_836_ = 0;
v___x_837_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_837_, 0, v_toConstantVal_828_);
lean_ctor_set(v___x_837_, 1, v_value_829_);
lean_ctor_set(v___x_837_, 2, v___x_835_);
lean_ctor_set(v___x_837_, 3, v_all_830_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*4, v___x_836_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_843_, v___y_844_);
lean_dec(v___y_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_847_, v___y_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_861_, lean_object* v_b_862_, lean_object* v_c_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
v___x_869_ = lean_apply_7(v_k_861_, v_b_862_, v_c_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_870_, lean_object* v_b_871_, lean_object* v_c_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_870_, v_b_871_, v_c_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_879_, lean_object* v_k_880_, uint8_t v_cleanupAnnotations_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___f_887_; uint8_t v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___f_887_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_887_, 0, v_k_880_);
v___x_888_ = 1;
v___x_889_ = 0;
v___x_890_ = lean_box(0);
v___x_891_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_879_, v___x_888_, v___x_889_, v___x_888_, v___x_889_, v___x_890_, v___f_887_, v_cleanupAnnotations_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_a_900_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_891_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_891_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_908_, lean_object* v_k_909_, lean_object* v_cleanupAnnotations_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_916_; lean_object* v_res_917_; 
v_cleanupAnnotations_boxed_916_ = lean_unbox(v_cleanupAnnotations_910_);
v_res_917_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_908_, v_k_909_, v_cleanupAnnotations_boxed_916_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_918_, lean_object* v_e_919_, lean_object* v_k_920_, uint8_t v_cleanupAnnotations_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_919_, v_k_920_, v_cleanupAnnotations_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_928_, lean_object* v_e_929_, lean_object* v_k_930_, lean_object* v_cleanupAnnotations_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_937_; lean_object* v_res_938_; 
v_cleanupAnnotations_boxed_937_ = lean_unbox(v_cleanupAnnotations_931_);
v_res_938_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_928_, v_e_929_, v_k_930_, v_cleanupAnnotations_boxed_937_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
if (lean_obj_tag(v_a_939_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = l_List_reverse___redArg(v_a_940_);
return v___x_941_;
}
else
{
lean_object* v_head_942_; lean_object* v_tail_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_952_; 
v_head_942_ = lean_ctor_get(v_a_939_, 0);
v_tail_943_ = lean_ctor_get(v_a_939_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_952_ == 0)
{
v___x_945_ = v_a_939_;
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_tail_943_);
lean_inc(v_head_942_);
lean_dec(v_a_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = l_Lean_mkLevelParam(v_head_942_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_a_940_);
lean_ctor_set(v___x_945_, 0, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_940_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
v_a_939_ = v_tail_943_;
v_a_940_ = v___x_949_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_953_, lean_object* v_name_954_, lean_object* v_xs_955_, lean_object* v_body_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_name_962_; lean_object* v_levelParams_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1033_; 
v_name_962_ = lean_ctor_get(v_toConstantVal_953_, 0);
v_levelParams_963_ = lean_ctor_get(v_toConstantVal_953_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_toConstantVal_953_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_toConstantVal_953_, 2);
lean_dec(v_unused_1034_);
v___x_965_ = v_toConstantVal_953_;
v_isShared_966_ = v_isSharedCheck_1033_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_levelParams_963_);
lean_inc(v_name_962_);
lean_dec(v_toConstantVal_953_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1033_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_lhs_970_; lean_object* v___x_971_; 
v___x_967_ = lean_box(0);
lean_inc(v_levelParams_963_);
v___x_968_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_963_, v___x_967_);
v___x_969_ = l_Lean_mkConst(v_name_962_, v___x_968_);
v_lhs_970_ = l_Lean_mkAppN(v___x_969_, v_xs_955_);
lean_inc_ref(v_lhs_970_);
v___x_971_ = l_Lean_Meta_mkEq(v_lhs_970_, v_body_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = 0;
v___x_974_ = 1;
v___x_975_ = 1;
v___x_976_ = l_Lean_Meta_mkForallFVars(v_xs_955_, v_a_972_, v___x_973_, v___x_974_, v___x_974_, v___x_975_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref(v___x_976_);
v___x_978_ = l_Lean_Meta_letToHave(v_a_977_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref(v___x_978_);
v___x_980_ = l_Lean_Meta_mkEqRefl(v_lhs_970_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = l_Lean_Meta_mkLambdaFVars(v_xs_955_, v_a_981_, v___x_973_, v___x_974_, v___x_973_, v___x_974_, v___x_975_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_982_);
lean_inc(v_name_954_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v_a_979_);
lean_ctor_set(v___x_965_, 0, v_name_954_);
v___x_985_ = v___x_965_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_name_954_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_levelParams_963_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_a_979_);
v___x_985_ = v_reuseFailAlloc_992_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_a_989_; lean_object* v___x_990_; 
lean_inc(v_name_954_);
v___x_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_986_, 0, v_name_954_);
lean_ctor_set(v___x_986_, 1, v___x_967_);
v___x_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v_a_983_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
v___x_988_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_987_, v___y_960_);
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref(v___x_988_);
v___x_990_ = l_Lean_addDecl(v_a_989_, v___x_973_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; 
lean_dec_ref(v___x_990_);
v___x_991_ = l_Lean_inferDefEqAttr(v_name_954_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_991_;
}
else
{
lean_dec(v_name_954_);
return v___x_990_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_a_979_);
lean_del_object(v___x_965_);
lean_dec(v_levelParams_963_);
lean_dec(v_name_954_);
v_a_993_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_982_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_982_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_a_979_);
lean_del_object(v___x_965_);
lean_dec(v_levelParams_963_);
lean_dec(v_name_954_);
v_a_1001_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_980_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_980_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_lhs_970_);
lean_del_object(v___x_965_);
lean_dec(v_levelParams_963_);
lean_dec(v_name_954_);
v_a_1009_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_978_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_978_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_lhs_970_);
lean_del_object(v___x_965_);
lean_dec(v_levelParams_963_);
lean_dec(v_name_954_);
v_a_1017_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_976_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_976_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec_ref(v_lhs_970_);
lean_del_object(v___x_965_);
lean_dec(v_levelParams_963_);
lean_dec(v_name_954_);
v_a_1025_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_971_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_971_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1035_, lean_object* v_name_1036_, lean_object* v_xs_1037_, lean_object* v_body_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1035_, v_name_1036_, v_xs_1037_, v_body_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v_xs_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1045_, lean_object* v_info_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_toConstantVal_1052_; lean_object* v_value_1053_; lean_object* v___f_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; 
v_toConstantVal_1052_ = lean_ctor_get(v_info_1046_, 0);
lean_inc_ref(v_toConstantVal_1052_);
v_value_1053_ = lean_ctor_get(v_info_1046_, 1);
lean_inc_ref(v_value_1053_);
lean_dec_ref(v_info_1046_);
v___f_1054_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1054_, 0, v_toConstantVal_1052_);
lean_closure_set(v___f_1054_, 1, v_name_1045_);
v___x_1055_ = 1;
v___x_1056_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1053_, v___f_1054_, v___x_1055_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1057_, lean_object* v_info_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1057_, v_info_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1065_, lean_object* v_name_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1075_; lean_object* v_env_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = lean_st_ref_get(v_a_1070_);
v_env_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_env_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = 0;
lean_inc(v_declName_1065_);
v___x_1078_ = l_Lean_Environment_find_x3f(v_env_1076_, v_declName_1065_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 1)
{
lean_object* v_val_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1106_; 
v_val_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1106_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_val_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1106_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
if (lean_obj_tag(v_val_1079_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_val_1083_ = lean_ctor_get(v_val_1079_, 0);
lean_inc_ref(v_val_1083_);
lean_dec_ref(v_val_1079_);
lean_inc_n(v_name_1066_, 2);
v___x_1084_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1084_, 0, v_name_1066_);
lean_closure_set(v___x_1084_, 1, v_val_1083_);
lean_inc(v_declName_1065_);
v___x_1085_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1085_, 0, lean_box(0));
lean_closure_set(v___x_1085_, 1, v_declName_1065_);
lean_closure_set(v___x_1085_, 2, v___x_1084_);
v___x_1086_ = l_Lean_Meta_realizeConst(v_declName_1065_, v_name_1066_, v___x_1085_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1097_);
v___x_1088_ = v___x_1086_;
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v___x_1086_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_name_1066_);
v___x_1091_ = v___x_1081_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_name_1066_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_del_object(v___x_1081_);
lean_dec(v_name_1066_);
v_a_1098_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1086_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1086_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_del_object(v___x_1081_);
lean_dec(v_val_1079_);
lean_dec(v_name_1066_);
lean_dec(v_declName_1065_);
goto v___jp_1072_;
}
}
}
else
{
lean_dec(v___x_1078_);
lean_dec(v_name_1066_);
lean_dec(v_declName_1065_);
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1107_, lean_object* v_name_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1107_, v_name_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1115_, lean_object* v_vals_1116_, lean_object* v_i_1117_, lean_object* v_k_1118_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_array_get_size(v_keys_1115_);
v___x_1120_ = lean_nat_dec_lt(v_i_1117_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_dec(v_i_1117_);
v___x_1121_ = lean_box(0);
return v___x_1121_;
}
else
{
lean_object* v_k_x27_1122_; uint8_t v___x_1123_; 
v_k_x27_1122_ = lean_array_fget_borrowed(v_keys_1115_, v_i_1117_);
v___x_1123_ = lean_name_eq(v_k_1118_, v_k_x27_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_i_1117_, v___x_1124_);
lean_dec(v_i_1117_);
v_i_1117_ = v___x_1125_;
goto _start;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_array_fget_borrowed(v_vals_1116_, v_i_1117_);
lean_dec(v_i_1117_);
lean_inc(v___x_1127_);
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1129_, lean_object* v_vals_1130_, lean_object* v_i_1131_, lean_object* v_k_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1129_, v_vals_1130_, v_i_1131_, v_k_1132_);
lean_dec(v_k_1132_);
lean_dec_ref(v_vals_1130_);
lean_dec_ref(v_keys_1129_);
return v_res_1133_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; 
v___x_1134_ = ((size_t)5ULL);
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_shift_left(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; 
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_1139_ = lean_usize_sub(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1140_, size_t v_x_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
lean_object* v_es_1143_; lean_object* v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; lean_object* v_j_1148_; lean_object* v___x_1149_; 
v_es_1143_ = lean_ctor_get(v_x_1140_, 0);
v___x_1144_ = lean_box(2);
v___x_1145_ = ((size_t)5ULL);
v___x_1146_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1147_ = lean_usize_land(v_x_1141_, v___x_1146_);
v_j_1148_ = lean_usize_to_nat(v___x_1147_);
v___x_1149_ = lean_array_get_borrowed(v___x_1144_, v_es_1143_, v_j_1148_);
lean_dec(v_j_1148_);
switch(lean_obj_tag(v___x_1149_))
{
case 0:
{
lean_object* v_key_1150_; lean_object* v_val_1151_; uint8_t v___x_1152_; 
v_key_1150_ = lean_ctor_get(v___x_1149_, 0);
v_val_1151_ = lean_ctor_get(v___x_1149_, 1);
v___x_1152_ = lean_name_eq(v_x_1142_, v_key_1150_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; 
lean_inc(v_val_1151_);
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_val_1151_);
return v___x_1154_;
}
}
case 1:
{
lean_object* v_node_1155_; size_t v___x_1156_; 
v_node_1155_ = lean_ctor_get(v___x_1149_, 0);
v___x_1156_ = lean_usize_shift_right(v_x_1141_, v___x_1145_);
v_x_1140_ = v_node_1155_;
v_x_1141_ = v___x_1156_;
goto _start;
}
default: 
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_box(0);
return v___x_1158_;
}
}
}
else
{
lean_object* v_ks_1159_; lean_object* v_vs_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_ks_1159_ = lean_ctor_get(v_x_1140_, 0);
v_vs_1160_ = lean_ctor_get(v_x_1140_, 1);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1159_, v_vs_1160_, v___x_1161_, v_x_1142_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
size_t v_x_355__boxed_1166_; lean_object* v_res_1167_; 
v_x_355__boxed_1166_ = lean_unbox_usize(v_x_1164_);
lean_dec(v_x_1164_);
v_res_1167_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1163_, v_x_355__boxed_1166_, v_x_1165_);
lean_dec(v_x_1165_);
lean_dec_ref(v_x_1163_);
return v_res_1167_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1168_; uint64_t v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(1723u);
v___x_1169_ = lean_uint64_of_nat(v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
uint64_t v___y_1173_; 
if (lean_obj_tag(v_x_1171_) == 0)
{
uint64_t v___x_1176_; 
v___x_1176_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1173_ = v___x_1176_;
goto v___jp_1172_;
}
else
{
uint64_t v_hash_1177_; 
v_hash_1177_ = lean_ctor_get_uint64(v_x_1171_, sizeof(void*)*2);
v___y_1173_ = v_hash_1177_;
goto v___jp_1172_;
}
v___jp_1172_:
{
size_t v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_uint64_to_usize(v___y_1173_);
v___x_1175_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1170_, v___x_1174_, v_x_1171_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1178_, v_x_1179_);
lean_dec(v_x_1179_);
lean_dec_ref(v_x_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v_env_1185_; lean_object* v___x_1186_; lean_object* v_asyncMode_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1184_ = lean_st_ref_get(v_a_1182_);
v_env_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc_ref(v_env_1185_);
lean_dec(v___x_1184_);
v___x_1186_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1187_ = lean_ctor_get(v___x_1186_, 2);
v___x_1188_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1189_ = lean_box(0);
v___x_1190_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1188_, v___x_1186_, v_env_1185_, v_asyncMode_1187_, v___x_1189_);
v___x_1191_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1190_, v_thmName_1181_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec(v_thmName_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1197_, v_a_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_thmName_1202_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1208_, v_x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1211_, v_x_1212_, v_x_1213_);
lean_dec(v_x_1213_);
lean_dec_ref(v_x_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1215_, lean_object* v_x_1216_, size_t v_x_1217_, lean_object* v_x_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1216_, v_x_1217_, v_x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
size_t v_x_460__boxed_1224_; lean_object* v_res_1225_; 
v_x_460__boxed_1224_ = lean_unbox_usize(v_x_1222_);
lean_dec(v_x_1222_);
v_res_1225_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1220_, v_x_1221_, v_x_460__boxed_1224_, v_x_1223_);
lean_dec(v_x_1223_);
lean_dec_ref(v_x_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1226_, lean_object* v_keys_1227_, lean_object* v_vals_1228_, lean_object* v_heq_1229_, lean_object* v_i_1230_, lean_object* v_k_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1227_, v_vals_1228_, v_i_1230_, v_k_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1233_, lean_object* v_keys_1234_, lean_object* v_vals_1235_, lean_object* v_heq_1236_, lean_object* v_i_1237_, lean_object* v_k_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1233_, v_keys_1234_, v_vals_1235_, v_heq_1236_, v_i_1237_, v_k_1238_);
lean_dec(v_k_1238_);
lean_dec_ref(v_vals_1235_);
lean_dec_ref(v_keys_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1240_, lean_object* v_i_1241_, lean_object* v_k_1242_){
_start:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_array_get_size(v_keys_1240_);
v___x_1244_ = lean_nat_dec_lt(v_i_1241_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec(v_i_1241_);
return v___x_1244_;
}
else
{
lean_object* v_k_x27_1245_; uint8_t v___x_1246_; 
v_k_x27_1245_ = lean_array_fget_borrowed(v_keys_1240_, v_i_1241_);
v___x_1246_ = lean_name_eq(v_k_1242_, v_k_x27_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_i_1241_, v___x_1247_);
lean_dec(v_i_1241_);
v_i_1241_ = v___x_1248_;
goto _start;
}
else
{
lean_dec(v_i_1241_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1250_, lean_object* v_i_1251_, lean_object* v_k_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1250_, v_i_1251_, v_k_1252_);
lean_dec(v_k_1252_);
lean_dec_ref(v_keys_1250_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1255_, size_t v_x_1256_, lean_object* v_x_1257_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 0)
{
lean_object* v_es_1258_; lean_object* v___x_1259_; size_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v_j_1263_; lean_object* v___x_1264_; 
v_es_1258_ = lean_ctor_get(v_x_1255_, 0);
v___x_1259_ = lean_box(2);
v___x_1260_ = ((size_t)5ULL);
v___x_1261_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1262_ = lean_usize_land(v_x_1256_, v___x_1261_);
v_j_1263_ = lean_usize_to_nat(v___x_1262_);
v___x_1264_ = lean_array_get_borrowed(v___x_1259_, v_es_1258_, v_j_1263_);
lean_dec(v_j_1263_);
switch(lean_obj_tag(v___x_1264_))
{
case 0:
{
lean_object* v_key_1265_; uint8_t v___x_1266_; 
v_key_1265_ = lean_ctor_get(v___x_1264_, 0);
v___x_1266_ = lean_name_eq(v_x_1257_, v_key_1265_);
return v___x_1266_;
}
case 1:
{
lean_object* v_node_1267_; size_t v___x_1268_; 
v_node_1267_ = lean_ctor_get(v___x_1264_, 0);
v___x_1268_ = lean_usize_shift_right(v_x_1256_, v___x_1260_);
v_x_1255_ = v_node_1267_;
v_x_1256_ = v___x_1268_;
goto _start;
}
default: 
{
uint8_t v___x_1270_; 
v___x_1270_ = 0;
return v___x_1270_;
}
}
}
else
{
lean_object* v_ks_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_ks_1271_ = lean_ctor_get(v_x_1255_, 0);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1271_, v___x_1272_, v_x_1257_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
size_t v_x_335__boxed_1277_; uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_x_335__boxed_1277_ = lean_unbox_usize(v_x_1275_);
lean_dec(v_x_1275_);
v_res_1278_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1274_, v_x_335__boxed_1277_, v_x_1276_);
lean_dec(v_x_1276_);
lean_dec_ref(v_x_1274_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
uint64_t v___y_1283_; 
if (lean_obj_tag(v_x_1281_) == 0)
{
uint64_t v___x_1286_; 
v___x_1286_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1283_ = v___x_1286_;
goto v___jp_1282_;
}
else
{
uint64_t v_hash_1287_; 
v_hash_1287_ = lean_ctor_get_uint64(v_x_1281_, sizeof(void*)*2);
v___y_1283_ = v_hash_1287_;
goto v___jp_1282_;
}
v___jp_1282_:
{
size_t v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_uint64_to_usize(v___y_1283_);
v___x_1285_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1280_, v___x_1284_, v_x_1281_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint8_t v_res_1290_; lean_object* v_r_1291_; 
v_res_1290_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1288_, v_x_1289_);
lean_dec(v_x_1289_);
lean_dec_ref(v_x_1288_);
v_r_1291_ = lean_box(v_res_1290_);
return v_r_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v_env_1296_; lean_object* v___x_1297_; lean_object* v_asyncMode_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1295_ = lean_st_ref_get(v_a_1293_);
v_env_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc_ref(v_env_1296_);
lean_dec(v___x_1295_);
v___x_1297_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1298_ = lean_ctor_get(v___x_1297_, 2);
v___x_1299_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1300_ = lean_box(0);
v___x_1301_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1299_, v___x_1297_, v_env_1296_, v_asyncMode_1298_, v___x_1300_);
v___x_1302_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1301_, v_thmName_1292_);
lean_dec(v___x_1301_);
v___x_1303_ = lean_box(v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec(v_thmName_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1309_, v_a_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Meta_isEqnThm(v_thmName_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_thmName_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1320_, v_x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1323_, v_x_1324_, v_x_1325_);
lean_dec(v_x_1325_);
lean_dec_ref(v_x_1324_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1328_, lean_object* v_x_1329_, size_t v_x_1330_, lean_object* v_x_1331_){
_start:
{
uint8_t v___x_1332_; 
v___x_1332_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1329_, v_x_1330_, v_x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v_x_429__boxed_1337_; uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_x_429__boxed_1337_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_res_1338_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1333_, v_x_1334_, v_x_429__boxed_1337_, v_x_1336_);
lean_dec(v_x_1336_);
lean_dec_ref(v_x_1334_);
v_r_1339_ = lean_box(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1340_, lean_object* v_keys_1341_, lean_object* v_vals_1342_, lean_object* v_heq_1343_, lean_object* v_i_1344_, lean_object* v_k_1345_){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1341_, v_i_1344_, v_k_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1347_, lean_object* v_keys_1348_, lean_object* v_vals_1349_, lean_object* v_heq_1350_, lean_object* v_i_1351_, lean_object* v_k_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1347_, v_keys_1348_, v_vals_1349_, v_heq_1350_, v_i_1351_, v_k_1352_);
lean_dec(v_k_1352_);
lean_dec_ref(v_vals_1349_);
lean_dec_ref(v_keys_1348_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v_ks_1359_; lean_object* v_vs_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1384_; 
v_ks_1359_ = lean_ctor_get(v_x_1355_, 0);
v_vs_1360_ = lean_ctor_get(v_x_1355_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_x_1355_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1362_ = v_x_1355_;
v_isShared_1363_ = v_isSharedCheck_1384_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_vs_1360_);
lean_inc(v_ks_1359_);
lean_dec(v_x_1355_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1384_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_array_get_size(v_ks_1359_);
v___x_1365_ = lean_nat_dec_lt(v_x_1356_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_dec(v_x_1356_);
v___x_1366_ = lean_array_push(v_ks_1359_, v_x_1357_);
v___x_1367_ = lean_array_push(v_vs_1360_, v_x_1358_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1367_);
lean_ctor_set(v___x_1362_, 0, v___x_1366_);
v___x_1369_ = v___x_1362_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v_k_x27_1371_; uint8_t v___x_1372_; 
v_k_x27_1371_ = lean_array_fget_borrowed(v_ks_1359_, v_x_1356_);
v___x_1372_ = lean_name_eq(v_x_1357_, v_k_x27_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1374_; 
if (v_isShared_1363_ == 0)
{
v___x_1374_ = v___x_1362_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_ks_1359_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_vs_1360_);
v___x_1374_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_nat_add(v_x_1356_, v___x_1375_);
lean_dec(v_x_1356_);
v_x_1355_ = v___x_1374_;
v_x_1356_ = v___x_1376_;
goto _start;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_array_fset(v_ks_1359_, v_x_1356_, v_x_1357_);
v___x_1380_ = lean_array_fset(v_vs_1360_, v_x_1356_, v_x_1358_);
lean_dec(v_x_1356_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1380_);
lean_ctor_set(v___x_1362_, 0, v___x_1379_);
v___x_1382_ = v___x_1362_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1385_, lean_object* v_k_1386_, lean_object* v_v_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1385_, v___x_1388_, v_k_1386_, v_v_1387_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1391_, size_t v_x_1392_, size_t v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v_es_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v_j_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_es_1396_ = lean_ctor_get(v_x_1391_, 0);
v___x_1397_ = ((size_t)5ULL);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1400_ = lean_usize_land(v_x_1392_, v___x_1399_);
v_j_1401_ = lean_usize_to_nat(v___x_1400_);
v___x_1402_ = lean_array_get_size(v_es_1396_);
v___x_1403_ = lean_nat_dec_lt(v_j_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_dec(v_j_1401_);
lean_dec(v_x_1395_);
lean_dec(v_x_1394_);
return v_x_1391_;
}
else
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1440_; 
lean_inc_ref(v_es_1396_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_x_1391_, 0);
lean_dec(v_unused_1441_);
v___x_1405_ = v_x_1391_;
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v_x_1391_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_v_1407_; lean_object* v___x_1408_; lean_object* v_xs_x27_1409_; lean_object* v___y_1411_; 
v_v_1407_ = lean_array_fget(v_es_1396_, v_j_1401_);
v___x_1408_ = lean_box(0);
v_xs_x27_1409_ = lean_array_fset(v_es_1396_, v_j_1401_, v___x_1408_);
switch(lean_obj_tag(v_v_1407_))
{
case 0:
{
lean_object* v_key_1416_; lean_object* v_val_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1427_; 
v_key_1416_ = lean_ctor_get(v_v_1407_, 0);
v_val_1417_ = lean_ctor_get(v_v_1407_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1419_ = v_v_1407_;
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_val_1417_);
lean_inc(v_key_1416_);
lean_dec(v_v_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_name_eq(v_x_1394_, v_key_1416_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_del_object(v___x_1419_);
v___x_1422_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1416_, v_val_1417_, v_x_1394_, v_x_1395_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
v___y_1411_ = v___x_1423_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_val_1417_);
lean_dec(v_key_1416_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v_x_1395_);
lean_ctor_set(v___x_1419_, 0, v_x_1394_);
v___x_1425_ = v___x_1419_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_x_1394_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_x_1395_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
v___y_1411_ = v___x_1425_;
goto v___jp_1410_;
}
}
}
}
case 1:
{
lean_object* v_node_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1438_; 
v_node_1428_ = lean_ctor_get(v_v_1407_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1430_ = v_v_1407_;
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_node_1428_);
lean_dec(v_v_1407_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1432_ = lean_usize_shift_right(v_x_1392_, v___x_1397_);
v___x_1433_ = lean_usize_add(v_x_1393_, v___x_1398_);
v___x_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1428_, v___x_1432_, v___x_1433_, v_x_1394_, v_x_1395_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v___y_1411_ = v___x_1436_;
goto v___jp_1410_;
}
}
}
default: 
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_x_1394_);
lean_ctor_set(v___x_1439_, 1, v_x_1395_);
v___y_1411_ = v___x_1439_;
goto v___jp_1410_;
}
}
v___jp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_array_fset(v_xs_x27_1409_, v_j_1401_, v___y_1411_);
lean_dec(v_j_1401_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1412_);
v___x_1414_ = v___x_1405_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_ks_1442_; lean_object* v_vs_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1463_; 
v_ks_1442_ = lean_ctor_get(v_x_1391_, 0);
v_vs_1443_ = lean_ctor_get(v_x_1391_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1445_ = v_x_1391_;
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_vs_1443_);
lean_inc(v_ks_1442_);
lean_dec(v_x_1391_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_ks_1442_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_vs_1443_);
v___x_1448_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v_newNode_1449_; uint8_t v___y_1451_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_newNode_1449_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1448_, v_x_1394_, v_x_1395_);
v___x_1457_ = ((size_t)7ULL);
v___x_1458_ = lean_usize_dec_le(v___x_1457_, v_x_1393_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1459_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1449_);
v___x_1460_ = lean_unsigned_to_nat(4u);
v___x_1461_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
v___y_1451_ = v___x_1461_;
goto v___jp_1450_;
}
else
{
v___y_1451_ = v___x_1458_;
goto v___jp_1450_;
}
v___jp_1450_:
{
if (v___y_1451_ == 0)
{
lean_object* v_ks_1452_; lean_object* v_vs_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_ks_1452_ = lean_ctor_get(v_newNode_1449_, 0);
lean_inc_ref(v_ks_1452_);
v_vs_1453_ = lean_ctor_get(v_newNode_1449_, 1);
lean_inc_ref(v_vs_1453_);
lean_dec_ref(v_newNode_1449_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1393_, v_ks_1452_, v_vs_1453_, v___x_1454_, v___x_1455_);
lean_dec_ref(v_vs_1453_);
lean_dec_ref(v_ks_1452_);
return v___x_1456_;
}
else
{
return v_newNode_1449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_i_1467_, lean_object* v_entries_1468_){
_start:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = lean_array_get_size(v_keys_1465_);
v___x_1470_ = lean_nat_dec_lt(v_i_1467_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec(v_i_1467_);
return v_entries_1468_;
}
else
{
lean_object* v_k_1471_; lean_object* v_v_1472_; uint64_t v___y_1474_; 
v_k_1471_ = lean_array_fget_borrowed(v_keys_1465_, v_i_1467_);
v_v_1472_ = lean_array_fget_borrowed(v_vals_1466_, v_i_1467_);
if (lean_obj_tag(v_k_1471_) == 0)
{
uint64_t v___x_1485_; 
v___x_1485_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1474_ = v___x_1485_;
goto v___jp_1473_;
}
else
{
uint64_t v_hash_1486_; 
v_hash_1486_ = lean_ctor_get_uint64(v_k_1471_, sizeof(void*)*2);
v___y_1474_ = v_hash_1486_;
goto v___jp_1473_;
}
v___jp_1473_:
{
size_t v_h_1475_; size_t v___x_1476_; lean_object* v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v_h_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_h_1475_ = lean_uint64_to_usize(v___y_1474_);
v___x_1476_ = ((size_t)5ULL);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = ((size_t)1ULL);
v___x_1479_ = lean_usize_sub(v_depth_1464_, v___x_1478_);
v___x_1480_ = lean_usize_mul(v___x_1476_, v___x_1479_);
v_h_1481_ = lean_usize_shift_right(v_h_1475_, v___x_1480_);
v___x_1482_ = lean_nat_add(v_i_1467_, v___x_1477_);
lean_dec(v_i_1467_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
v___x_1483_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1468_, v_h_1481_, v_depth_1464_, v_k_1471_, v_v_1472_);
v_i_1467_ = v___x_1482_;
v_entries_1468_ = v___x_1483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1487_, lean_object* v_keys_1488_, lean_object* v_vals_1489_, lean_object* v_i_1490_, lean_object* v_entries_1491_){
_start:
{
size_t v_depth_boxed_1492_; lean_object* v_res_1493_; 
v_depth_boxed_1492_ = lean_unbox_usize(v_depth_1487_);
lean_dec(v_depth_1487_);
v_res_1493_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1492_, v_keys_1488_, v_vals_1489_, v_i_1490_, v_entries_1491_);
lean_dec_ref(v_vals_1489_);
lean_dec_ref(v_keys_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
size_t v_x_634__boxed_1499_; size_t v_x_635__boxed_1500_; lean_object* v_res_1501_; 
v_x_634__boxed_1499_ = lean_unbox_usize(v_x_1495_);
lean_dec(v_x_1495_);
v_x_635__boxed_1500_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_res_1501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1494_, v_x_634__boxed_1499_, v_x_635__boxed_1500_, v_x_1497_, v_x_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
uint64_t v___y_1506_; 
if (lean_obj_tag(v_x_1503_) == 0)
{
uint64_t v___x_1510_; 
v___x_1510_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1506_ = v___x_1510_;
goto v___jp_1505_;
}
else
{
uint64_t v_hash_1511_; 
v_hash_1511_ = lean_ctor_get_uint64(v_x_1503_, sizeof(void*)*2);
v___y_1506_ = v_hash_1511_;
goto v___jp_1505_;
}
v___jp_1505_:
{
size_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_uint64_to_usize(v___y_1506_);
v___x_1508_ = ((size_t)1ULL);
v___x_1509_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1502_, v___x_1507_, v___x_1508_, v_x_1503_, v_x_1504_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1512_, lean_object* v_as_1513_, size_t v_i_1514_, size_t v_stop_1515_, lean_object* v_b_1516_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_usize_dec_eq(v_i_1514_, v_stop_1515_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; size_t v___x_1520_; size_t v___x_1521_; 
v___x_1518_ = lean_array_uget_borrowed(v_as_1513_, v_i_1514_);
lean_inc(v_declName_1512_);
lean_inc(v___x_1518_);
v___x_1519_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1516_, v___x_1518_, v_declName_1512_);
v___x_1520_ = ((size_t)1ULL);
v___x_1521_ = lean_usize_add(v_i_1514_, v___x_1520_);
v_i_1514_ = v___x_1521_;
v_b_1516_ = v___x_1519_;
goto _start;
}
else
{
lean_dec(v_declName_1512_);
return v_b_1516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1523_, lean_object* v_as_1524_, lean_object* v_i_1525_, lean_object* v_stop_1526_, lean_object* v_b_1527_){
_start:
{
size_t v_i_boxed_1528_; size_t v_stop_boxed_1529_; lean_object* v_res_1530_; 
v_i_boxed_1528_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_stop_boxed_1529_ = lean_unbox_usize(v_stop_1526_);
lean_dec(v_stop_1526_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1523_, v_as_1524_, v_i_boxed_1528_, v_stop_boxed_1529_, v_b_1527_);
lean_dec_ref(v_as_1524_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1531_, lean_object* v_declName_1532_, lean_object* v_s_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_array_get_size(v_eqThms_1531_);
v___x_1536_ = lean_nat_dec_lt(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec(v_declName_1532_);
return v_s_1533_;
}
else
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_nat_dec_le(v___x_1535_, v___x_1535_);
if (v___x_1537_ == 0)
{
if (v___x_1536_ == 0)
{
lean_dec(v_declName_1532_);
return v_s_1533_;
}
else
{
size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = lean_usize_of_nat(v___x_1535_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1532_, v_eqThms_1531_, v___x_1538_, v___x_1539_, v_s_1533_);
return v___x_1540_;
}
}
else
{
size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = lean_usize_of_nat(v___x_1535_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1532_, v_eqThms_1531_, v___x_1541_, v___x_1542_, v_s_1533_);
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1544_, lean_object* v_declName_1545_, lean_object* v_s_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1544_, v_declName_1545_, v_s_1546_);
lean_dec_ref(v_eqThms_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1548_, lean_object* v_eqThms_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v_env_1553_; lean_object* v_nextMacroScope_1554_; lean_object* v_ngen_1555_; lean_object* v_auxDeclNGen_1556_; lean_object* v_traceState_1557_; lean_object* v_messages_1558_; lean_object* v_infoState_1559_; lean_object* v_snapshotTasks_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1576_; 
v___x_1552_ = lean_st_ref_take(v_a_1550_);
v_env_1553_ = lean_ctor_get(v___x_1552_, 0);
v_nextMacroScope_1554_ = lean_ctor_get(v___x_1552_, 1);
v_ngen_1555_ = lean_ctor_get(v___x_1552_, 2);
v_auxDeclNGen_1556_ = lean_ctor_get(v___x_1552_, 3);
v_traceState_1557_ = lean_ctor_get(v___x_1552_, 4);
v_messages_1558_ = lean_ctor_get(v___x_1552_, 6);
v_infoState_1559_ = lean_ctor_get(v___x_1552_, 7);
v_snapshotTasks_1560_ = lean_ctor_get(v___x_1552_, 8);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v___x_1552_, 5);
lean_dec(v_unused_1577_);
v___x_1562_ = v___x_1552_;
v_isShared_1563_ = v_isSharedCheck_1576_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snapshotTasks_1560_);
lean_inc(v_infoState_1559_);
lean_inc(v_messages_1558_);
lean_inc(v_traceState_1557_);
lean_inc(v_auxDeclNGen_1556_);
lean_inc(v_ngen_1555_);
lean_inc(v_nextMacroScope_1554_);
lean_inc(v_env_1553_);
lean_dec(v___x_1552_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1576_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v_asyncMode_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1564_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1565_ = lean_ctor_get(v___x_1564_, 2);
v___f_1566_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1566_, 0, v_eqThms_1549_);
lean_closure_set(v___f_1566_, 1, v_declName_1548_);
v___x_1567_ = lean_box(0);
v___x_1568_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1564_, v_env_1553_, v___f_1566_, v_asyncMode_1565_, v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 5, v___x_1569_);
lean_ctor_set(v___x_1562_, 0, v___x_1568_);
v___x_1571_ = v___x_1562_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_nextMacroScope_1554_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_ngen_1555_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_auxDeclNGen_1556_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_traceState_1557_);
lean_ctor_set(v_reuseFailAlloc_1575_, 5, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1575_, 6, v_messages_1558_);
lean_ctor_set(v_reuseFailAlloc_1575_, 7, v_infoState_1559_);
lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_snapshotTasks_1560_);
v___x_1571_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = lean_st_ref_set(v_a_1550_, v___x_1571_);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1578_, lean_object* v_eqThms_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1578_, v_eqThms_1579_, v_a_1580_);
lean_dec(v_a_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1583_, lean_object* v_eqThms_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1583_, v_eqThms_1584_, v_a_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1589_, lean_object* v_eqThms_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1589_, v_eqThms_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1596_, v_x_1597_, v_x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1600_, lean_object* v_x_1601_, size_t v_x_1602_, size_t v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1601_, v_x_1602_, v_x_1603_, v_x_1604_, v_x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_){
_start:
{
size_t v_x_903__boxed_1613_; size_t v_x_904__boxed_1614_; lean_object* v_res_1615_; 
v_x_903__boxed_1613_ = lean_unbox_usize(v_x_1609_);
lean_dec(v_x_1609_);
v_x_904__boxed_1614_ = lean_unbox_usize(v_x_1610_);
lean_dec(v_x_1610_);
v_res_1615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1607_, v_x_1608_, v_x_903__boxed_1613_, v_x_904__boxed_1614_, v_x_1611_, v_x_1612_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1616_, lean_object* v_n_1617_, lean_object* v_k_1618_, lean_object* v_v_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1617_, v_k_1618_, v_v_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1621_, size_t v_depth_1622_, lean_object* v_keys_1623_, lean_object* v_vals_1624_, lean_object* v_heq_1625_, lean_object* v_i_1626_, lean_object* v_entries_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1622_, v_keys_1623_, v_vals_1624_, v_i_1626_, v_entries_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1629_, lean_object* v_depth_1630_, lean_object* v_keys_1631_, lean_object* v_vals_1632_, lean_object* v_heq_1633_, lean_object* v_i_1634_, lean_object* v_entries_1635_){
_start:
{
size_t v_depth_boxed_1636_; lean_object* v_res_1637_; 
v_depth_boxed_1636_ = lean_unbox_usize(v_depth_1630_);
lean_dec(v_depth_1630_);
v_res_1637_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1629_, v_depth_boxed_1636_, v_keys_1631_, v_vals_1632_, v_heq_1633_, v_i_1634_, v_entries_1635_);
lean_dec_ref(v_vals_1632_);
lean_dec_ref(v_keys_1631_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1639_, v_x_1640_, v_x_1641_, v_x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1644_, lean_object* v_env_1645_, lean_object* v_idx_1646_, lean_object* v_eqs_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_nextEq_1654_; uint8_t v___x_1655_; 
v___x_1649_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_nat_add(v_idx_1646_, v___x_1650_);
lean_dec(v_idx_1646_);
lean_inc(v___x_1651_);
v___x_1652_ = l_Nat_reprFast(v___x_1651_);
v___x_1653_ = lean_string_append(v___x_1649_, v___x_1652_);
lean_dec_ref(v___x_1652_);
lean_inc(v_declName_1644_);
lean_inc_ref(v_env_1645_);
v_nextEq_1654_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1645_, v_declName_1644_, v___x_1653_);
v___x_1655_ = l_Lean_Environment_containsOnBranch(v_env_1645_, v_nextEq_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec(v_nextEq_1654_);
lean_dec(v___x_1651_);
lean_dec_ref(v_env_1645_);
lean_dec(v_declName_1644_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_eqs_1647_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_array_push(v_eqs_1647_, v_nextEq_1654_);
v_idx_1646_ = v___x_1651_;
v_eqs_1647_ = v___x_1657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1659_, lean_object* v_env_1660_, lean_object* v_idx_1661_, lean_object* v_eqs_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1659_, v_env_1660_, v_idx_1661_, v_eqs_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1665_, lean_object* v_env_1666_, lean_object* v_idx_1667_, lean_object* v_eqs_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1665_, v_env_1666_, v_idx_1667_, v_eqs_1668_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1675_, lean_object* v_env_1676_, lean_object* v_idx_1677_, lean_object* v_eqs_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1675_, v_env_1676_, v_idx_1677_, v_eqs_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v_env_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; uint8_t v___x_1693_; 
v___x_1688_ = lean_st_ref_get(v_a_1686_);
v_env_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc_ref_n(v_env_1689_, 3);
lean_dec(v___x_1688_);
v___x_1690_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1685_);
v___x_1691_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1689_, v_declName_1685_, v___x_1690_);
v___x_1692_ = 1;
lean_inc(v___x_1691_);
v___x_1693_ = l_Lean_Environment_contains(v_env_1689_, v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v___x_1691_);
lean_dec_ref(v_env_1689_);
lean_dec(v_declName_1685_);
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_mk_empty_array_with_capacity(v___x_1696_);
v___x_1698_ = lean_array_push(v___x_1697_, v___x_1691_);
lean_inc(v_declName_1685_);
v___x_1699_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1685_, v_env_1689_, v___x_1696_, v___x_1698_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1709_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc_n(v_a_1700_, 2);
lean_dec_ref(v___x_1699_);
v___x_1701_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1685_, v_a_1700_, v_a_1686_);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v___x_1701_, 0);
lean_dec(v_unused_1710_);
v___x_1703_ = v___x_1701_;
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v___x_1701_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1700_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_declName_1685_);
v_a_1711_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1699_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1699_);
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
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1719_, v_a_1720_);
lean_dec(v_a_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1723_, v_a_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1737_, lean_object* v_localInsts_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1737_, v_localInsts_1738_, v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1745_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1745_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1762_, lean_object* v_localInsts_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1762_, v_localInsts_1763_, v_x_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1771_, lean_object* v_lctx_1772_, lean_object* v_localInsts_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1772_, v_localInsts_1773_, v_x_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1781_, lean_object* v_lctx_1782_, lean_object* v_localInsts_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1781_, v_lctx_1782_, v_localInsts_1783_, v_x_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1794_, lean_object* v_as_x27_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
if (lean_obj_tag(v_as_x27_1795_) == 0)
{
lean_object* v___x_1802_; 
lean_dec(v_declName_1794_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_b_1796_);
return v___x_1802_;
}
else
{
lean_object* v_head_1803_; lean_object* v_tail_1804_; lean_object* v___x_1805_; 
lean_dec_ref(v_b_1796_);
v_head_1803_ = lean_ctor_get(v_as_x27_1795_, 0);
v_tail_1804_ = lean_ctor_get(v_as_x27_1795_, 1);
lean_inc(v_head_1803_);
lean_inc(v___y_1800_);
lean_inc_ref(v___y_1799_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v_declName_1794_);
v___x_1805_ = lean_apply_6(v_head_1803_, v_declName_1794_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, lean_box(0));
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = lean_box(0);
if (lean_obj_tag(v_a_1806_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
v_val_1808_ = lean_ctor_get(v_a_1806_, 0);
lean_inc(v_val_1808_);
v___x_1809_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1794_, v_val_1808_, v___y_1800_);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1819_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1806_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v___x_1807_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1814_);
v___x_1816_ = v___x_1811_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v___x_1820_; 
lean_dec(v_a_1806_);
v___x_1820_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1795_ = v_tail_1804_;
v_b_1796_ = v___x_1820_;
goto _start;
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_declName_1794_);
v_a_1822_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1805_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1805_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1830_, lean_object* v_as_x27_1831_, lean_object* v_b_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1830_, v_as_x27_1831_, v_b_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v_as_x27_1831_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
lean_inc(v_declName_1839_);
v___x_1845_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1883_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1883_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1883_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_unbox(v_a_1846_);
lean_dec(v_a_1846_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec(v_declName_1839_);
v___x_1851_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1851_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
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
lean_object* v___x_1855_; 
lean_del_object(v___x_1848_);
lean_inc(v_declName_1839_);
v___x_1855_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1839_, v___y_1843_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
if (lean_obj_tag(v_a_1856_) == 1)
{
lean_dec_ref(v_a_1856_);
lean_dec(v_declName_1839_);
return v___x_1855_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec(v_a_1856_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1858_ = lean_st_ref_get(v___x_1857_);
v___x_1859_ = lean_box(0);
v___x_1860_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1861_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1839_, v___x_1858_, v___x_1860_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___x_1858_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1874_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1874_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1874_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_fst_1866_; 
v_fst_1866_ = lean_ctor_get(v_a_1862_, 0);
lean_inc(v_fst_1866_);
lean_dec(v_a_1862_);
if (lean_obj_tag(v_fst_1866_) == 0)
{
lean_object* v___x_1868_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1859_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1859_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
else
{
lean_object* v_val_1870_; lean_object* v___x_1872_; 
v_val_1870_ = lean_ctor_get(v_fst_1866_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v_fst_1866_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_val_1870_);
v___x_1872_ = v___x_1864_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_val_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1861_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1861_);
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
else
{
lean_dec(v_declName_1839_);
return v___x_1855_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_declName_1839_);
v_a_1884_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1845_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1845_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = lean_box(1);
v___x_1903_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1904_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1903_);
lean_ctor_set(v___x_1905_, 2, v___x_1902_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___f_1914_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1914_, 0, v_declName_1908_);
v___x_1915_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1917_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1915_, v___x_1916_, v___f_1914_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1925_, lean_object* v_as_1926_, lean_object* v_as_x27_1927_, lean_object* v_b_1928_, lean_object* v_a_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1925_, v_as_x27_1927_, v_b_1928_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1936_, lean_object* v_as_1937_, lean_object* v_as_x27_1938_, lean_object* v_b_1939_, lean_object* v_a_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1936_, v_as_1937_, v_as_x27_1938_, v_b_1939_, v_a_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v_as_x27_1938_);
lean_dec(v_as_1937_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1953_ = lean_unsigned_to_nat(32u);
v___x_1954_ = lean_mk_empty_array_with_capacity(v___x_1953_);
lean_dec_ref(v___x_1954_);
v___x_1955_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1956_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1947_);
v___x_1957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1957_, 0, v_declName_1947_);
v___x_1958_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1958_, 0, lean_box(0));
lean_closure_set(v___x_1958_, 1, v_declName_1947_);
lean_closure_set(v___x_1958_, 2, v___x_1957_);
v___x_1959_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1955_, v___x_1956_, v___x_1958_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; lean_object* v_env_1974_; lean_object* v___x_1975_; lean_object* v_mctx_1976_; lean_object* v_lctx_1977_; lean_object* v_options_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1973_ = lean_st_ref_get(v___y_1971_);
v_env_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc_ref(v_env_1974_);
lean_dec(v___x_1973_);
v___x_1975_ = lean_st_ref_get(v___y_1969_);
v_mctx_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_ref(v_mctx_1976_);
lean_dec(v___x_1975_);
v_lctx_1977_ = lean_ctor_get(v___y_1968_, 2);
v_options_1978_ = lean_ctor_get(v___y_1970_, 2);
lean_inc_ref(v_options_1978_);
lean_inc_ref(v_lctx_1977_);
v___x_1979_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1979_, 0, v_env_1974_);
lean_ctor_set(v___x_1979_, 1, v_mctx_1976_);
lean_ctor_set(v___x_1979_, 2, v_lctx_1977_);
lean_ctor_set(v___x_1979_, 3, v_options_1978_);
v___x_1980_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v_msgData_1967_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1988_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1989_; double v___x_1990_; 
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_float_of_nat(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1994_, lean_object* v_msg_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_ref_2001_; lean_object* v___x_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2047_; 
v_ref_2001_ = lean_ctor_get(v___y_1998_, 5);
v___x_2002_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2047_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2047_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v_traceState_2008_; lean_object* v_env_2009_; lean_object* v_nextMacroScope_2010_; lean_object* v_ngen_2011_; lean_object* v_auxDeclNGen_2012_; lean_object* v_cache_2013_; lean_object* v_messages_2014_; lean_object* v_infoState_2015_; lean_object* v_snapshotTasks_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2046_; 
v___x_2007_ = lean_st_ref_take(v___y_1999_);
v_traceState_2008_ = lean_ctor_get(v___x_2007_, 4);
v_env_2009_ = lean_ctor_get(v___x_2007_, 0);
v_nextMacroScope_2010_ = lean_ctor_get(v___x_2007_, 1);
v_ngen_2011_ = lean_ctor_get(v___x_2007_, 2);
v_auxDeclNGen_2012_ = lean_ctor_get(v___x_2007_, 3);
v_cache_2013_ = lean_ctor_get(v___x_2007_, 5);
v_messages_2014_ = lean_ctor_get(v___x_2007_, 6);
v_infoState_2015_ = lean_ctor_get(v___x_2007_, 7);
v_snapshotTasks_2016_ = lean_ctor_get(v___x_2007_, 8);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2018_ = v___x_2007_;
v_isShared_2019_ = v_isSharedCheck_2046_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snapshotTasks_2016_);
lean_inc(v_infoState_2015_);
lean_inc(v_messages_2014_);
lean_inc(v_cache_2013_);
lean_inc(v_traceState_2008_);
lean_inc(v_auxDeclNGen_2012_);
lean_inc(v_ngen_2011_);
lean_inc(v_nextMacroScope_2010_);
lean_inc(v_env_2009_);
lean_dec(v___x_2007_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2046_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
uint64_t v_tid_2020_; lean_object* v_traces_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2045_; 
v_tid_2020_ = lean_ctor_get_uint64(v_traceState_2008_, sizeof(void*)*1);
v_traces_2021_ = lean_ctor_get(v_traceState_2008_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_traceState_2008_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2023_ = v_traceState_2008_;
v_isShared_2024_ = v_isSharedCheck_2045_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_traces_2021_);
lean_dec(v_traceState_2008_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2045_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; double v___x_2026_; uint8_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_2027_ = 0;
v___x_2028_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_2029_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2029_, 0, v_cls_1994_);
lean_ctor_set(v___x_2029_, 1, v___x_2025_);
lean_ctor_set(v___x_2029_, 2, v___x_2028_);
lean_ctor_set_float(v___x_2029_, sizeof(void*)*3, v___x_2026_);
lean_ctor_set_float(v___x_2029_, sizeof(void*)*3 + 8, v___x_2026_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*3 + 16, v___x_2027_);
v___x_2030_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_2031_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2029_);
lean_ctor_set(v___x_2031_, 1, v_a_2003_);
lean_ctor_set(v___x_2031_, 2, v___x_2030_);
lean_inc(v_ref_2001_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_ref_2001_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_PersistentArray_push___redArg(v_traces_2021_, v___x_2032_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2033_);
v___x_2035_ = v___x_2023_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2033_);
lean_ctor_set_uint64(v_reuseFailAlloc_2044_, sizeof(void*)*1, v_tid_2020_);
v___x_2035_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 4, v___x_2035_);
v___x_2037_ = v___x_2018_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_env_2009_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_nextMacroScope_2010_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_ngen_2011_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_auxDeclNGen_2012_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2043_, 5, v_cache_2013_);
lean_ctor_set(v_reuseFailAlloc_2043_, 6, v_messages_2014_);
lean_ctor_set(v_reuseFailAlloc_2043_, 7, v_infoState_2015_);
lean_ctor_set(v_reuseFailAlloc_2043_, 8, v_snapshotTasks_2016_);
v___x_2037_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = lean_st_ref_set(v___y_1999_, v___x_2037_);
v___x_2039_ = lean_box(0);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2039_);
v___x_2041_ = v___x_2005_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2048_, lean_object* v_msg_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2048_, v_msg_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2056_, lean_object* v_as_2057_, size_t v_sz_2058_, size_t v_i_2059_, lean_object* v_b_2060_){
_start:
{
lean_object* v_a_2063_; uint8_t v___x_2067_; 
v___x_2067_ = lean_usize_dec_lt(v_i_2059_, v_sz_2058_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_b_2060_);
return v___x_2068_;
}
else
{
lean_object* v_a_2069_; lean_object* v_defValue_2070_; uint8_t v___x_2071_; uint8_t v___y_2073_; 
v_a_2069_ = lean_array_uget(v_as_2057_, v_i_2059_);
v_defValue_2070_ = lean_ctor_get(v_a_2069_, 1);
v___x_2071_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2056_, v_a_2069_);
if (v___x_2071_ == 0)
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_unbox(v_defValue_2070_);
if (v___x_2085_ == 0)
{
v___y_2073_ = v___x_2067_;
goto v___jp_2072_;
}
else
{
v___y_2073_ = v___x_2071_;
goto v___jp_2072_;
}
}
else
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_unbox(v_defValue_2070_);
v___y_2073_ = v___x_2086_;
goto v___jp_2072_;
}
v___jp_2072_:
{
if (v___y_2073_ == 0)
{
lean_object* v_name_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2083_; 
v_name_2074_ = lean_ctor_get(v_a_2069_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2069_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_a_2069_, 1);
lean_dec(v_unused_2084_);
v___x_2076_ = v_a_2069_;
v_isShared_2077_ = v_isSharedCheck_2083_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_name_2074_);
lean_dec(v_a_2069_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2083_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2078_, 0, v___x_2071_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_name_2074_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_array_push(v_b_2060_, v___x_2080_);
v_a_2063_ = v___x_2081_;
goto v___jp_2062_;
}
}
}
else
{
lean_dec(v_a_2069_);
v_a_2063_ = v_b_2060_;
goto v___jp_2062_;
}
}
}
v___jp_2062_:
{
size_t v___x_2064_; size_t v___x_2065_; 
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_add(v_i_2059_, v___x_2064_);
v_i_2059_ = v___x_2065_;
v_b_2060_ = v_a_2063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2087_, lean_object* v_as_2088_, lean_object* v_sz_2089_, lean_object* v_i_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_){
_start:
{
size_t v_sz_boxed_2093_; size_t v_i_boxed_2094_; lean_object* v_res_2095_; 
v_sz_boxed_2093_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2094_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2087_, v_as_2088_, v_sz_boxed_2093_, v_i_boxed_2094_, v_b_2091_);
lean_dec_ref(v_as_2088_);
lean_dec_ref(v___x_2087_);
return v_res_2095_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2098_; size_t v_sz_2099_; 
v___x_2098_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2099_ = lean_array_size(v___x_2098_);
return v_sz_2099_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2101_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
lean_ctor_set(v___x_2101_, 2, v___x_2100_);
lean_ctor_set(v___x_2101_, 3, v___x_2100_);
lean_ctor_set(v___x_2101_, 4, v___x_2100_);
lean_ctor_set(v___x_2101_, 5, v___x_2100_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2110_ = l_Lean_Name_append(v___x_2109_, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_options_2120_; lean_object* v_inheritedTraceOptions_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; size_t v_sz_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v_options_2120_ = lean_ctor_get(v_a_2117_, 2);
v_inheritedTraceOptions_2121_ = lean_ctor_get(v_a_2117_, 13);
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2124_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2125_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2120_, v___x_2124_, v_sz_2125_, v___x_2126_, v___x_2123_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2187_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2187_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2187_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2175_ = lean_array_get_size(v_a_2128_);
v___x_2176_ = lean_nat_dec_eq(v___x_2175_, v___x_2122_);
if (v___x_2176_ == 0)
{
uint8_t v_hasTrace_2177_; 
v_hasTrace_2177_ = lean_ctor_get_uint8(v_options_2120_, sizeof(void*)*1);
if (v_hasTrace_2177_ == 0)
{
v___y_2133_ = v_a_2116_;
v___y_2134_ = v_a_2118_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2179_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2180_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2121_, v_options_2120_, v___x_2179_);
if (v___x_2180_ == 0)
{
v___y_2133_ = v_a_2116_;
v___y_2134_ = v_a_2118_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2181_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2114_);
v___x_2182_ = l_Lean_MessageData_ofName(v_declName_2114_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2178_, v___x_2183_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_dec_ref(v___x_2184_);
v___y_2133_ = v_a_2116_;
v___y_2134_ = v_a_2118_;
goto v___jp_2132_;
}
else
{
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
lean_dec(v_declName_2114_);
return v___x_2184_;
}
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
lean_dec(v_declName_2114_);
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
v___jp_2132_:
{
lean_object* v___x_2135_; lean_object* v_env_2136_; lean_object* v_nextMacroScope_2137_; lean_object* v_ngen_2138_; lean_object* v_auxDeclNGen_2139_; lean_object* v_traceState_2140_; lean_object* v_messages_2141_; lean_object* v_infoState_2142_; lean_object* v_snapshotTasks_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2173_; 
v___x_2135_ = lean_st_ref_take(v___y_2134_);
v_env_2136_ = lean_ctor_get(v___x_2135_, 0);
v_nextMacroScope_2137_ = lean_ctor_get(v___x_2135_, 1);
v_ngen_2138_ = lean_ctor_get(v___x_2135_, 2);
v_auxDeclNGen_2139_ = lean_ctor_get(v___x_2135_, 3);
v_traceState_2140_ = lean_ctor_get(v___x_2135_, 4);
v_messages_2141_ = lean_ctor_get(v___x_2135_, 6);
v_infoState_2142_ = lean_ctor_get(v___x_2135_, 7);
v_snapshotTasks_2143_ = lean_ctor_get(v___x_2135_, 8);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; 
v_unused_2174_ = lean_ctor_get(v___x_2135_, 5);
lean_dec(v_unused_2174_);
v___x_2145_ = v___x_2135_;
v_isShared_2146_ = v_isSharedCheck_2173_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_snapshotTasks_2143_);
lean_inc(v_infoState_2142_);
lean_inc(v_messages_2141_);
lean_inc(v_traceState_2140_);
lean_inc(v_auxDeclNGen_2139_);
lean_inc(v_ngen_2138_);
lean_inc(v_nextMacroScope_2137_);
lean_inc(v_env_2136_);
lean_dec(v___x_2135_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2173_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2147_ = l_Lean_Meta_eqnOptionsExt;
v___x_2148_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2147_, v_env_2136_, v_declName_2114_, v_a_2128_);
v___x_2149_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 5, v___x_2149_);
lean_ctor_set(v___x_2145_, 0, v___x_2148_);
v___x_2151_ = v___x_2145_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_nextMacroScope_2137_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_ngen_2138_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_auxDeclNGen_2139_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_traceState_2140_);
lean_ctor_set(v_reuseFailAlloc_2172_, 5, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_messages_2141_);
lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_infoState_2142_);
lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_snapshotTasks_2143_);
v___x_2151_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_mctx_2154_; lean_object* v_zetaDeltaFVarIds_2155_; lean_object* v_postponed_2156_; lean_object* v_diag_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2170_; 
v___x_2152_ = lean_st_ref_set(v___y_2134_, v___x_2151_);
v___x_2153_ = lean_st_ref_take(v___y_2133_);
v_mctx_2154_ = lean_ctor_get(v___x_2153_, 0);
v_zetaDeltaFVarIds_2155_ = lean_ctor_get(v___x_2153_, 2);
v_postponed_2156_ = lean_ctor_get(v___x_2153_, 3);
v_diag_2157_ = lean_ctor_get(v___x_2153_, 4);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2153_, 1);
lean_dec(v_unused_2171_);
v___x_2159_ = v___x_2153_;
v_isShared_2160_ = v_isSharedCheck_2170_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_diag_2157_);
lean_inc(v_postponed_2156_);
lean_inc(v_zetaDeltaFVarIds_2155_);
lean_inc(v_mctx_2154_);
lean_dec(v___x_2153_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2170_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v___x_2161_);
v___x_2163_ = v___x_2159_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_mctx_2154_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_zetaDeltaFVarIds_2155_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_postponed_2156_);
lean_ctor_set(v_reuseFailAlloc_2169_, 4, v_diag_2157_);
v___x_2163_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2164_ = lean_st_ref_set(v___y_2133_, v___x_2163_);
v___x_2165_ = lean_box(0);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2165_);
v___x_2167_ = v___x_2130_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
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
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_declName_2114_);
v_a_2188_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2127_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2127_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2203_, lean_object* v_as_2204_, size_t v_sz_2205_, size_t v_i_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2203_, v_as_2204_, v_sz_2205_, v_i_2206_, v_b_2207_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2214_, lean_object* v_as_2215_, lean_object* v_sz_2216_, lean_object* v_i_2217_, lean_object* v_b_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
size_t v_sz_boxed_2224_; size_t v_i_boxed_2225_; lean_object* v_res_2226_; 
v_sz_boxed_2224_ = lean_unbox_usize(v_sz_2216_);
lean_dec(v_sz_2216_);
v_i_boxed_2225_ = lean_unbox_usize(v_i_2217_);
lean_dec(v_i_2217_);
v_res_2226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2214_, v_as_2215_, v_sz_boxed_2224_, v_i_boxed_2225_, v_b_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec_ref(v_as_2215_);
lean_dec_ref(v___x_2214_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_st_mk_ref(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2252_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2252_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2252_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_unbox(v_a_2236_);
lean_dec(v_a_2236_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_dec_ref(v_f_2233_);
v___x_2241_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 1);
lean_ctor_set(v___x_2238_, 0, v___x_2241_);
v___x_2243_ = v___x_2238_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2245_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2246_ = lean_st_ref_take(v___x_2245_);
v___x_2247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_f_2233_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = lean_st_ref_set(v___x_2245_, v___x_2247_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2248_);
v___x_2250_ = v___x_2238_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v_f_2233_);
v_a_2253_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2235_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2235_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2261_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2267_, lean_object* v_as_x27_2268_, lean_object* v_b_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
if (lean_obj_tag(v_as_x27_2268_) == 0)
{
lean_object* v___x_2275_; 
lean_dec(v_declName_2267_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_b_2269_);
return v___x_2275_;
}
else
{
lean_object* v_head_2276_; lean_object* v_tail_2277_; lean_object* v___x_2278_; 
lean_dec_ref(v_b_2269_);
v_head_2276_ = lean_ctor_get(v_as_x27_2268_, 0);
v_tail_2277_ = lean_ctor_get(v_as_x27_2268_, 1);
lean_inc(v_head_2276_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v_declName_2267_);
v___x_2278_ = lean_apply_6(v_head_2276_, v_declName_2267_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, lean_box(0));
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2291_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2291_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2291_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_box(0);
if (lean_obj_tag(v_a_2279_) == 1)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec(v_declName_2267_);
v___x_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_a_2279_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2283_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2285_);
v___x_2287_ = v___x_2281_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
else
{
lean_object* v___x_2289_; 
lean_del_object(v___x_2281_);
lean_dec(v_a_2279_);
v___x_2289_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2268_ = v_tail_2277_;
v_b_2269_ = v___x_2289_;
goto _start;
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_declName_2267_);
v_a_2292_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2278_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2278_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2300_, lean_object* v_as_x27_2301_, lean_object* v_b_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2300_, v_as_x27_2301_, v_b_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v_as_x27_2301_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2309_, lean_object* v_declName_2310_, uint8_t v_nonRec_2311_, lean_object* v___x_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2321_; lean_object* v_env_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; 
v___x_2321_ = lean_st_ref_get(v___y_2316_);
v_env_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc_ref(v_env_2322_);
lean_dec(v___x_2321_);
v___x_2323_ = 1;
lean_inc(v___x_2309_);
v___x_2324_ = l_Lean_Environment_contains(v_env_2322_, v___x_2309_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; 
lean_dec(v___x_2309_);
lean_inc(v_declName_2310_);
v___x_2325_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2310_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; uint8_t v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v___x_2327_ = lean_unbox(v_a_2326_);
lean_dec(v_a_2326_);
if (v___x_2327_ == 0)
{
lean_dec_ref(v___x_2312_);
lean_dec(v_declName_2310_);
goto v___jp_2318_;
}
else
{
lean_object* v___x_2328_; 
lean_inc(v_declName_2310_);
v___x_2328_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2310_, v___y_2316_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; uint8_t v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = lean_unbox(v_a_2329_);
lean_dec(v_a_2329_);
if (v___x_2330_ == 0)
{
if (v_nonRec_2311_ == 0)
{
lean_dec_ref(v___x_2312_);
lean_dec(v_declName_2310_);
goto v___jp_2318_;
}
else
{
lean_object* v___x_2331_; lean_object* v_env_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2331_ = lean_st_ref_get(v___y_2316_);
v_env_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc_ref(v_env_2332_);
lean_dec(v___x_2331_);
lean_inc(v_declName_2310_);
v___x_2333_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2332_, v_declName_2310_, v___x_2312_);
v___x_2334_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2310_, v___x_2333_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2334_;
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec_ref(v___x_2312_);
v___x_2335_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2336_ = lean_st_ref_get(v___x_2335_);
v___x_2337_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2338_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2310_, v___x_2336_, v___x_2337_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___x_2336_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2348_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2348_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2348_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_fst_2343_; 
v_fst_2343_ = lean_ctor_get(v_a_2339_, 0);
lean_inc(v_fst_2343_);
lean_dec(v_a_2339_);
if (lean_obj_tag(v_fst_2343_) == 0)
{
lean_del_object(v___x_2341_);
goto v___jp_2318_;
}
else
{
lean_object* v_val_2344_; lean_object* v___x_2346_; 
v_val_2344_ = lean_ctor_get(v_fst_2343_, 0);
lean_inc(v_val_2344_);
lean_dec_ref(v_fst_2343_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v_val_2344_);
v___x_2346_ = v___x_2341_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_val_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_a_2349_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2338_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2338_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
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
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v___x_2312_);
lean_dec(v_declName_2310_);
v_a_2357_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2328_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2328_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v___x_2312_);
lean_dec(v_declName_2310_);
v_a_2365_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2325_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2325_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v___x_2312_);
lean_dec(v_declName_2310_);
v___x_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2309_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
v___jp_2318_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_box(0);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
return v___x_2320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2375_, lean_object* v_declName_2376_, lean_object* v_nonRec_2377_, lean_object* v___x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
uint8_t v_nonRec_boxed_2384_; lean_object* v_res_2385_; 
v_nonRec_boxed_2384_ = lean_unbox(v_nonRec_2377_);
v_res_2385_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2375_, v_declName_2376_, v_nonRec_boxed_2384_, v___x_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_ref_2392_; lean_object* v___x_2393_; lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
v_ref_2392_ = lean_ctor_get(v___y_2389_, 5);
v___x_2393_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_inc(v_ref_2392_);
v___x_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_ref_2392_);
lean_ctor_set(v___x_2398_, 1, v_a_2394_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2398_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2410_, uint8_t v_isExporting_2411_, lean_object* v___x_2412_, lean_object* v___y_2413_, lean_object* v___x_2414_, lean_object* v_a_x3f_2415_){
_start:
{
lean_object* v___x_2417_; lean_object* v_env_2418_; lean_object* v_nextMacroScope_2419_; lean_object* v_ngen_2420_; lean_object* v_auxDeclNGen_2421_; lean_object* v_traceState_2422_; lean_object* v_messages_2423_; lean_object* v_infoState_2424_; lean_object* v_snapshotTasks_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2450_; 
v___x_2417_ = lean_st_ref_take(v___y_2410_);
v_env_2418_ = lean_ctor_get(v___x_2417_, 0);
v_nextMacroScope_2419_ = lean_ctor_get(v___x_2417_, 1);
v_ngen_2420_ = lean_ctor_get(v___x_2417_, 2);
v_auxDeclNGen_2421_ = lean_ctor_get(v___x_2417_, 3);
v_traceState_2422_ = lean_ctor_get(v___x_2417_, 4);
v_messages_2423_ = lean_ctor_get(v___x_2417_, 6);
v_infoState_2424_ = lean_ctor_get(v___x_2417_, 7);
v_snapshotTasks_2425_ = lean_ctor_get(v___x_2417_, 8);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2417_, 5);
lean_dec(v_unused_2451_);
v___x_2427_ = v___x_2417_;
v_isShared_2428_ = v_isSharedCheck_2450_;
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
v_isShared_2428_ = v_isSharedCheck_2450_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2429_ = l_Lean_Environment_setExporting(v_env_2418_, v_isExporting_2411_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 5, v___x_2412_);
lean_ctor_set(v___x_2427_, 0, v___x_2429_);
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_nextMacroScope_2419_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_ngen_2420_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_auxDeclNGen_2421_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_traceState_2422_);
lean_ctor_set(v_reuseFailAlloc_2449_, 5, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2449_, 6, v_messages_2423_);
lean_ctor_set(v_reuseFailAlloc_2449_, 7, v_infoState_2424_);
lean_ctor_set(v_reuseFailAlloc_2449_, 8, v_snapshotTasks_2425_);
v___x_2431_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_mctx_2434_; lean_object* v_zetaDeltaFVarIds_2435_; lean_object* v_postponed_2436_; lean_object* v_diag_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2447_; 
v___x_2432_ = lean_st_ref_set(v___y_2410_, v___x_2431_);
v___x_2433_ = lean_st_ref_take(v___y_2413_);
v_mctx_2434_ = lean_ctor_get(v___x_2433_, 0);
v_zetaDeltaFVarIds_2435_ = lean_ctor_get(v___x_2433_, 2);
v_postponed_2436_ = lean_ctor_get(v___x_2433_, 3);
v_diag_2437_ = lean_ctor_get(v___x_2433_, 4);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v___x_2433_, 1);
lean_dec(v_unused_2448_);
v___x_2439_ = v___x_2433_;
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_diag_2437_);
lean_inc(v_postponed_2436_);
lean_inc(v_zetaDeltaFVarIds_2435_);
lean_inc(v_mctx_2434_);
lean_dec(v___x_2433_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v___x_2414_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_mctx_2434_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_zetaDeltaFVarIds_2435_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_postponed_2436_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_diag_2437_);
v___x_2442_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = lean_st_ref_set(v___y_2413_, v___x_2442_);
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2452_, lean_object* v_isExporting_2453_, lean_object* v___x_2454_, lean_object* v___y_2455_, lean_object* v___x_2456_, lean_object* v_a_x3f_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v_isExporting_boxed_2459_; lean_object* v_res_2460_; 
v_isExporting_boxed_2459_ = lean_unbox(v_isExporting_2453_);
v_res_2460_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2452_, v_isExporting_boxed_2459_, v___x_2454_, v___y_2455_, v___x_2456_, v_a_x3f_2457_);
lean_dec(v_a_x3f_2457_);
lean_dec(v___y_2455_);
lean_dec(v___y_2452_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2461_, uint8_t v_isExporting_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; lean_object* v_env_2469_; uint8_t v_isExporting_2470_; lean_object* v___x_2471_; lean_object* v_env_2472_; lean_object* v_nextMacroScope_2473_; lean_object* v_ngen_2474_; lean_object* v_auxDeclNGen_2475_; lean_object* v_traceState_2476_; lean_object* v_messages_2477_; lean_object* v_infoState_2478_; lean_object* v_snapshotTasks_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2533_; 
v___x_2468_ = lean_st_ref_get(v___y_2466_);
v_env_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_env_2469_);
lean_dec(v___x_2468_);
v_isExporting_2470_ = lean_ctor_get_uint8(v_env_2469_, sizeof(void*)*8);
lean_dec_ref(v_env_2469_);
v___x_2471_ = lean_st_ref_take(v___y_2466_);
v_env_2472_ = lean_ctor_get(v___x_2471_, 0);
v_nextMacroScope_2473_ = lean_ctor_get(v___x_2471_, 1);
v_ngen_2474_ = lean_ctor_get(v___x_2471_, 2);
v_auxDeclNGen_2475_ = lean_ctor_get(v___x_2471_, 3);
v_traceState_2476_ = lean_ctor_get(v___x_2471_, 4);
v_messages_2477_ = lean_ctor_get(v___x_2471_, 6);
v_infoState_2478_ = lean_ctor_get(v___x_2471_, 7);
v_snapshotTasks_2479_ = lean_ctor_get(v___x_2471_, 8);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2471_, 5);
lean_dec(v_unused_2534_);
v___x_2481_ = v___x_2471_;
v_isShared_2482_ = v_isSharedCheck_2533_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_snapshotTasks_2479_);
lean_inc(v_infoState_2478_);
lean_inc(v_messages_2477_);
lean_inc(v_traceState_2476_);
lean_inc(v_auxDeclNGen_2475_);
lean_inc(v_ngen_2474_);
lean_inc(v_nextMacroScope_2473_);
lean_inc(v_env_2472_);
lean_dec(v___x_2471_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2533_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2483_ = l_Lean_Environment_setExporting(v_env_2472_, v_isExporting_2462_);
v___x_2484_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 5, v___x_2484_);
lean_ctor_set(v___x_2481_, 0, v___x_2483_);
v___x_2486_ = v___x_2481_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_nextMacroScope_2473_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_ngen_2474_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_auxDeclNGen_2475_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_traceState_2476_);
lean_ctor_set(v_reuseFailAlloc_2532_, 5, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2532_, 6, v_messages_2477_);
lean_ctor_set(v_reuseFailAlloc_2532_, 7, v_infoState_2478_);
lean_ctor_set(v_reuseFailAlloc_2532_, 8, v_snapshotTasks_2479_);
v___x_2486_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_mctx_2489_; lean_object* v_zetaDeltaFVarIds_2490_; lean_object* v_postponed_2491_; lean_object* v_diag_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2530_; 
v___x_2487_ = lean_st_ref_set(v___y_2466_, v___x_2486_);
v___x_2488_ = lean_st_ref_take(v___y_2464_);
v_mctx_2489_ = lean_ctor_get(v___x_2488_, 0);
v_zetaDeltaFVarIds_2490_ = lean_ctor_get(v___x_2488_, 2);
v_postponed_2491_ = lean_ctor_get(v___x_2488_, 3);
v_diag_2492_ = lean_ctor_get(v___x_2488_, 4);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v___x_2488_, 1);
lean_dec(v_unused_2531_);
v___x_2494_ = v___x_2488_;
v_isShared_2495_ = v_isSharedCheck_2530_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_diag_2492_);
lean_inc(v_postponed_2491_);
lean_inc(v_zetaDeltaFVarIds_2490_);
lean_inc(v_mctx_2489_);
lean_dec(v___x_2488_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2530_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2496_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v___x_2496_);
v___x_2498_ = v___x_2494_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_mctx_2489_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_zetaDeltaFVarIds_2490_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_postponed_2491_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_diag_2492_);
v___x_2498_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2499_; lean_object* v_r_2500_; 
v___x_2499_ = lean_st_ref_set(v___y_2464_, v___x_2498_);
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2465_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
v_r_2500_ = lean_apply_5(v_x_2461_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, lean_box(0));
if (lean_obj_tag(v_r_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2517_; 
v_a_2501_ = lean_ctor_get(v_r_2500_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_r_2500_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2503_ = v_r_2500_;
v_isShared_2504_ = v_isSharedCheck_2517_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v_r_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2517_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
lean_inc(v_a_2501_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set_tag(v___x_2503_, 1);
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
v___x_2507_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2466_, v_isExporting_2470_, v___x_2484_, v___y_2464_, v___x_2496_, v___x_2506_);
lean_dec_ref(v___x_2506_);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v___x_2507_, 0);
lean_dec(v_unused_2515_);
v___x_2509_ = v___x_2507_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_dec(v___x_2507_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v_a_2501_);
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2501_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2518_ = lean_ctor_get(v_r_2500_, 0);
lean_inc(v_a_2518_);
lean_dec_ref(v_r_2500_);
v___x_2519_ = lean_box(0);
v___x_2520_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2466_, v_isExporting_2470_, v___x_2484_, v___y_2464_, v___x_2496_, v___x_2519_);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; 
v_unused_2528_ = lean_ctor_get(v___x_2520_, 0);
lean_dec(v_unused_2528_);
v___x_2522_ = v___x_2520_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_dec(v___x_2520_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 1);
lean_ctor_set(v___x_2522_, 0, v_a_2518_);
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2518_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2535_, lean_object* v_isExporting_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
uint8_t v_isExporting_boxed_2542_; lean_object* v_res_2543_; 
v_isExporting_boxed_2542_ = lean_unbox(v_isExporting_2536_);
v_res_2543_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2535_, v_isExporting_boxed_2542_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2544_, uint8_t v_when_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
if (v_when_2545_ == 0)
{
lean_object* v___x_2551_; 
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2548_);
lean_inc(v___y_2547_);
lean_inc_ref(v___y_2546_);
v___x_2551_ = lean_apply_5(v_x_2544_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, lean_box(0));
return v___x_2551_;
}
else
{
uint8_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = 0;
v___x_2553_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2544_, v___x_2552_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2554_, lean_object* v_when_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
uint8_t v_when_boxed_2561_; lean_object* v_res_2562_; 
v_when_boxed_2561_ = lean_unbox(v_when_2555_);
v_res_2562_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2554_, v_when_boxed_2561_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
return v_res_2562_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2565_ = l_Lean_stringToMessageData(v___x_2564_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2568_ = l_Lean_stringToMessageData(v___x_2567_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2571_ = l_Lean_stringToMessageData(v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2572_, uint8_t v_nonRec_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; lean_object* v_env_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2579_ = lean_st_ref_get(v___y_2577_);
v_env_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc_ref(v_env_2580_);
lean_dec(v___x_2579_);
v___x_2581_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2572_);
v___x_2582_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2580_, v_declName_2572_, v___x_2581_);
v___x_2583_ = lean_box(v_nonRec_2573_);
lean_inc(v___x_2582_);
v___f_2584_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2584_, 0, v___x_2582_);
lean_closure_set(v___f_2584_, 1, v_declName_2572_);
lean_closure_set(v___f_2584_, 2, v___x_2583_);
lean_closure_set(v___f_2584_, 3, v___x_2581_);
v___x_2585_ = 1;
v___x_2586_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2584_, v___x_2585_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
if (lean_obj_tag(v_a_2587_) == 1)
{
lean_object* v_val_2588_; uint8_t v___x_2589_; 
v_val_2588_ = lean_ctor_get(v_a_2587_, 0);
lean_inc(v_val_2588_);
lean_dec_ref(v_a_2587_);
v___x_2589_ = lean_name_eq(v_val_2588_, v___x_2582_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v___x_2586_);
v___x_2590_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2591_ = l_Lean_MessageData_ofName(v_val_2588_);
v___x_2592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = l_Lean_MessageData_ofName(v___x_2582_);
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2598_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
else
{
lean_dec(v_val_2588_);
lean_dec(v___x_2582_);
return v___x_2586_;
}
}
else
{
lean_dec(v_a_2587_);
lean_dec(v___x_2582_);
return v___x_2586_;
}
}
else
{
lean_dec(v___x_2582_);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2608_, lean_object* v_nonRec_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
uint8_t v_nonRec_boxed_2615_; lean_object* v_res_2616_; 
v_nonRec_boxed_2615_ = lean_unbox(v_nonRec_2609_);
v_res_2616_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2608_, v_nonRec_boxed_2615_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2617_, uint8_t v_nonRec_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2624_ = lean_box(v_nonRec_2618_);
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2625_, 0, v_declName_2617_);
lean_closure_set(v___f_2625_, 1, v___x_2624_);
v___x_2626_ = lean_unsigned_to_nat(32u);
v___x_2627_ = lean_mk_empty_array_with_capacity(v___x_2626_);
lean_dec_ref(v___x_2627_);
v___x_2628_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2630_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2628_, v___x_2629_, v___f_2625_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2631_, lean_object* v_nonRec_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_nonRec_boxed_2638_; lean_object* v_res_2639_; 
v_nonRec_boxed_2638_ = lean_unbox(v_nonRec_2632_);
v_res_2639_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2631_, v_nonRec_boxed_2638_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2640_, lean_object* v_as_2641_, lean_object* v_as_x27_2642_, lean_object* v_b_2643_, lean_object* v_a_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2640_, v_as_x27_2642_, v_b_2643_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2651_, lean_object* v_as_2652_, lean_object* v_as_x27_2653_, lean_object* v_b_2654_, lean_object* v_a_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2651_, v_as_2652_, v_as_x27_2653_, v_b_2654_, v_a_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v_as_x27_2653_);
lean_dec(v_as_2652_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2662_, lean_object* v_x_2663_, uint8_t v_isExporting_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2663_, v_isExporting_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2671_, lean_object* v_x_2672_, lean_object* v_isExporting_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
uint8_t v_isExporting_boxed_2679_; lean_object* v_res_2680_; 
v_isExporting_boxed_2679_ = lean_unbox(v_isExporting_2673_);
v_res_2680_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2671_, v_x_2672_, v_isExporting_boxed_2679_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2681_, lean_object* v_x_2682_, uint8_t v_when_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2682_, v_when_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2690_, lean_object* v_x_2691_, lean_object* v_when_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v_when_boxed_2698_; lean_object* v_res_2699_; 
v_when_boxed_2698_ = lean_unbox(v_when_2692_);
v_res_2699_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2690_, v_x_2691_, v_when_boxed_2698_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2700_, lean_object* v_msg_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2708_, lean_object* v_msg_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2708_, v_msg_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
return v_res_2715_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_unsigned_to_nat(32u);
v___x_2717_ = lean_mk_empty_array_with_capacity(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2719_ = ((size_t)5ULL);
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = lean_unsigned_to_nat(32u);
v___x_2722_ = lean_mk_empty_array_with_capacity(v___x_2721_);
v___x_2723_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2724_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v___x_2722_);
lean_ctor_set(v___x_2724_, 2, v___x_2720_);
lean_ctor_set(v___x_2724_, 3, v___x_2720_);
lean_ctor_set_usize(v___x_2724_, 4, v___x_2719_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; lean_object* v_traceState_2728_; lean_object* v_traces_2729_; lean_object* v___x_2730_; lean_object* v_traceState_2731_; lean_object* v_env_2732_; lean_object* v_nextMacroScope_2733_; lean_object* v_ngen_2734_; lean_object* v_auxDeclNGen_2735_; lean_object* v_cache_2736_; lean_object* v_messages_2737_; lean_object* v_infoState_2738_; lean_object* v_snapshotTasks_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2758_; 
v___x_2727_ = lean_st_ref_get(v___y_2725_);
v_traceState_2728_ = lean_ctor_get(v___x_2727_, 4);
lean_inc_ref(v_traceState_2728_);
lean_dec(v___x_2727_);
v_traces_2729_ = lean_ctor_get(v_traceState_2728_, 0);
lean_inc_ref(v_traces_2729_);
lean_dec_ref(v_traceState_2728_);
v___x_2730_ = lean_st_ref_take(v___y_2725_);
v_traceState_2731_ = lean_ctor_get(v___x_2730_, 4);
v_env_2732_ = lean_ctor_get(v___x_2730_, 0);
v_nextMacroScope_2733_ = lean_ctor_get(v___x_2730_, 1);
v_ngen_2734_ = lean_ctor_get(v___x_2730_, 2);
v_auxDeclNGen_2735_ = lean_ctor_get(v___x_2730_, 3);
v_cache_2736_ = lean_ctor_get(v___x_2730_, 5);
v_messages_2737_ = lean_ctor_get(v___x_2730_, 6);
v_infoState_2738_ = lean_ctor_get(v___x_2730_, 7);
v_snapshotTasks_2739_ = lean_ctor_get(v___x_2730_, 8);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2741_ = v___x_2730_;
v_isShared_2742_ = v_isSharedCheck_2758_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_snapshotTasks_2739_);
lean_inc(v_infoState_2738_);
lean_inc(v_messages_2737_);
lean_inc(v_cache_2736_);
lean_inc(v_traceState_2731_);
lean_inc(v_auxDeclNGen_2735_);
lean_inc(v_ngen_2734_);
lean_inc(v_nextMacroScope_2733_);
lean_inc(v_env_2732_);
lean_dec(v___x_2730_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2758_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
uint64_t v_tid_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2756_; 
v_tid_2743_ = lean_ctor_get_uint64(v_traceState_2731_, sizeof(void*)*1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_traceState_2731_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; 
v_unused_2757_ = lean_ctor_get(v_traceState_2731_, 0);
lean_dec(v_unused_2757_);
v___x_2745_ = v_traceState_2731_;
v_isShared_2746_ = v_isSharedCheck_2756_;
goto v_resetjp_2744_;
}
else
{
lean_dec(v_traceState_2731_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2756_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2747_);
lean_ctor_set_uint64(v_reuseFailAlloc_2755_, sizeof(void*)*1, v_tid_2743_);
v___x_2749_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2751_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 4, v___x_2749_);
v___x_2751_ = v___x_2741_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_env_2732_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_nextMacroScope_2733_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_ngen_2734_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_auxDeclNGen_2735_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2754_, 5, v_cache_2736_);
lean_ctor_set(v_reuseFailAlloc_2754_, 6, v_messages_2737_);
lean_ctor_set(v_reuseFailAlloc_2754_, 7, v_infoState_2738_);
lean_ctor_set(v_reuseFailAlloc_2754_, 8, v_snapshotTasks_2739_);
v___x_2751_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_st_ref_set(v___y_2725_, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v_traces_2729_);
return v___x_2753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2759_);
lean_dec(v___y_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = 0;
v___x_2775_ = lean_box(v___x_2774_);
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
return v_res_2781_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2784_ = l_Lean_stringToMessageData(v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2785_, lean_object* v_x_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2790_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2791_ = l_Lean_MessageData_ofName(v_name_2785_);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2794_, lean_object* v_x_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2794_, v_x_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec_ref(v_x_2795_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_x_2800_){
_start:
{
if (lean_obj_tag(v_x_2800_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v_x_2800_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_x_2800_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v_x_2800_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v_x_2800_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set_tag(v___x_2804_, 1);
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v_a_2810_ = lean_ctor_get(v_x_2800_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_x_2800_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v_x_2800_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v_x_2800_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 0);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_x_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_2818_);
return v_res_2820_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_e_2821_){
_start:
{
if (lean_obj_tag(v_e_2821_) == 0)
{
uint8_t v___x_2822_; 
v___x_2822_ = 2;
return v___x_2822_;
}
else
{
lean_object* v_a_2823_; uint8_t v___x_2824_; 
v_a_2823_ = lean_ctor_get(v_e_2821_, 0);
v___x_2824_ = lean_unbox(v_a_2823_);
if (v___x_2824_ == 0)
{
uint8_t v___x_2825_; 
v___x_2825_ = 1;
return v___x_2825_;
}
else
{
uint8_t v___x_2826_; 
v___x_2826_ = 0;
return v___x_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_e_2827_){
_start:
{
uint8_t v_res_2828_; lean_object* v_r_2829_; 
v_res_2828_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_e_2827_);
lean_dec_ref(v_e_2827_);
v_r_2829_ = lean_box(v_res_2828_);
return v_r_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(size_t v_sz_2830_, size_t v_i_2831_, lean_object* v_bs_2832_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_usize_dec_lt(v_i_2831_, v_sz_2830_);
if (v___x_2833_ == 0)
{
return v_bs_2832_;
}
else
{
lean_object* v_v_2834_; lean_object* v_msg_2835_; lean_object* v___x_2836_; lean_object* v_bs_x27_2837_; size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v_v_2834_ = lean_array_uget_borrowed(v_bs_2832_, v_i_2831_);
v_msg_2835_ = lean_ctor_get(v_v_2834_, 1);
lean_inc_ref(v_msg_2835_);
v___x_2836_ = lean_unsigned_to_nat(0u);
v_bs_x27_2837_ = lean_array_uset(v_bs_2832_, v_i_2831_, v___x_2836_);
v___x_2838_ = ((size_t)1ULL);
v___x_2839_ = lean_usize_add(v_i_2831_, v___x_2838_);
v___x_2840_ = lean_array_uset(v_bs_x27_2837_, v_i_2831_, v_msg_2835_);
v_i_2831_ = v___x_2839_;
v_bs_2832_ = v___x_2840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_sz_2842_, lean_object* v_i_2843_, lean_object* v_bs_2844_){
_start:
{
size_t v_sz_boxed_2845_; size_t v_i_boxed_2846_; lean_object* v_res_2847_; 
v_sz_boxed_2845_ = lean_unbox_usize(v_sz_2842_);
lean_dec(v_sz_2842_);
v_i_boxed_2846_ = lean_unbox_usize(v_i_2843_);
lean_dec(v_i_2843_);
v_res_2847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_boxed_2845_, v_i_boxed_2846_, v_bs_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_oldTraces_2848_, lean_object* v_data_2849_, lean_object* v_ref_2850_, lean_object* v_msg_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_fileName_2855_; lean_object* v_fileMap_2856_; lean_object* v_options_2857_; lean_object* v_currRecDepth_2858_; lean_object* v_maxRecDepth_2859_; lean_object* v_ref_2860_; lean_object* v_currNamespace_2861_; lean_object* v_openDecls_2862_; lean_object* v_initHeartbeats_2863_; lean_object* v_maxHeartbeats_2864_; lean_object* v_quotContext_2865_; lean_object* v_currMacroScope_2866_; uint8_t v_diag_2867_; lean_object* v_cancelTk_x3f_2868_; uint8_t v_suppressElabErrors_2869_; lean_object* v_inheritedTraceOptions_2870_; lean_object* v___x_2871_; lean_object* v_traceState_2872_; lean_object* v_traces_2873_; lean_object* v_ref_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; size_t v_sz_2877_; size_t v___x_2878_; lean_object* v___x_2879_; lean_object* v_msg_2880_; lean_object* v___x_2881_; lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2919_; 
v_fileName_2855_ = lean_ctor_get(v___y_2852_, 0);
v_fileMap_2856_ = lean_ctor_get(v___y_2852_, 1);
v_options_2857_ = lean_ctor_get(v___y_2852_, 2);
v_currRecDepth_2858_ = lean_ctor_get(v___y_2852_, 3);
v_maxRecDepth_2859_ = lean_ctor_get(v___y_2852_, 4);
v_ref_2860_ = lean_ctor_get(v___y_2852_, 5);
v_currNamespace_2861_ = lean_ctor_get(v___y_2852_, 6);
v_openDecls_2862_ = lean_ctor_get(v___y_2852_, 7);
v_initHeartbeats_2863_ = lean_ctor_get(v___y_2852_, 8);
v_maxHeartbeats_2864_ = lean_ctor_get(v___y_2852_, 9);
v_quotContext_2865_ = lean_ctor_get(v___y_2852_, 10);
v_currMacroScope_2866_ = lean_ctor_get(v___y_2852_, 11);
v_diag_2867_ = lean_ctor_get_uint8(v___y_2852_, sizeof(void*)*14);
v_cancelTk_x3f_2868_ = lean_ctor_get(v___y_2852_, 12);
v_suppressElabErrors_2869_ = lean_ctor_get_uint8(v___y_2852_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2870_ = lean_ctor_get(v___y_2852_, 13);
v___x_2871_ = lean_st_ref_get(v___y_2853_);
v_traceState_2872_ = lean_ctor_get(v___x_2871_, 4);
lean_inc_ref(v_traceState_2872_);
lean_dec(v___x_2871_);
v_traces_2873_ = lean_ctor_get(v_traceState_2872_, 0);
lean_inc_ref(v_traces_2873_);
lean_dec_ref(v_traceState_2872_);
v_ref_2874_ = l_Lean_replaceRef(v_ref_2850_, v_ref_2860_);
lean_inc_ref(v_inheritedTraceOptions_2870_);
lean_inc(v_cancelTk_x3f_2868_);
lean_inc(v_currMacroScope_2866_);
lean_inc(v_quotContext_2865_);
lean_inc(v_maxHeartbeats_2864_);
lean_inc(v_initHeartbeats_2863_);
lean_inc(v_openDecls_2862_);
lean_inc(v_currNamespace_2861_);
lean_inc(v_maxRecDepth_2859_);
lean_inc(v_currRecDepth_2858_);
lean_inc_ref(v_options_2857_);
lean_inc_ref(v_fileMap_2856_);
lean_inc_ref(v_fileName_2855_);
v___x_2875_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2875_, 0, v_fileName_2855_);
lean_ctor_set(v___x_2875_, 1, v_fileMap_2856_);
lean_ctor_set(v___x_2875_, 2, v_options_2857_);
lean_ctor_set(v___x_2875_, 3, v_currRecDepth_2858_);
lean_ctor_set(v___x_2875_, 4, v_maxRecDepth_2859_);
lean_ctor_set(v___x_2875_, 5, v_ref_2874_);
lean_ctor_set(v___x_2875_, 6, v_currNamespace_2861_);
lean_ctor_set(v___x_2875_, 7, v_openDecls_2862_);
lean_ctor_set(v___x_2875_, 8, v_initHeartbeats_2863_);
lean_ctor_set(v___x_2875_, 9, v_maxHeartbeats_2864_);
lean_ctor_set(v___x_2875_, 10, v_quotContext_2865_);
lean_ctor_set(v___x_2875_, 11, v_currMacroScope_2866_);
lean_ctor_set(v___x_2875_, 12, v_cancelTk_x3f_2868_);
lean_ctor_set(v___x_2875_, 13, v_inheritedTraceOptions_2870_);
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*14, v_diag_2867_);
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*14 + 1, v_suppressElabErrors_2869_);
v___x_2876_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2873_);
lean_dec_ref(v_traces_2873_);
v_sz_2877_ = lean_array_size(v___x_2876_);
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_2877_, v___x_2878_, v___x_2876_);
v_msg_2880_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2880_, 0, v_data_2849_);
lean_ctor_set(v_msg_2880_, 1, v_msg_2851_);
lean_ctor_set(v_msg_2880_, 2, v___x_2879_);
v___x_2881_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2880_, v___x_2875_, v___y_2853_);
lean_dec_ref(v___x_2875_);
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2919_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2919_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v_traceState_2887_; lean_object* v_env_2888_; lean_object* v_nextMacroScope_2889_; lean_object* v_ngen_2890_; lean_object* v_auxDeclNGen_2891_; lean_object* v_cache_2892_; lean_object* v_messages_2893_; lean_object* v_infoState_2894_; lean_object* v_snapshotTasks_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2918_; 
v___x_2886_ = lean_st_ref_take(v___y_2853_);
v_traceState_2887_ = lean_ctor_get(v___x_2886_, 4);
v_env_2888_ = lean_ctor_get(v___x_2886_, 0);
v_nextMacroScope_2889_ = lean_ctor_get(v___x_2886_, 1);
v_ngen_2890_ = lean_ctor_get(v___x_2886_, 2);
v_auxDeclNGen_2891_ = lean_ctor_get(v___x_2886_, 3);
v_cache_2892_ = lean_ctor_get(v___x_2886_, 5);
v_messages_2893_ = lean_ctor_get(v___x_2886_, 6);
v_infoState_2894_ = lean_ctor_get(v___x_2886_, 7);
v_snapshotTasks_2895_ = lean_ctor_get(v___x_2886_, 8);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2897_ = v___x_2886_;
v_isShared_2898_ = v_isSharedCheck_2918_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_snapshotTasks_2895_);
lean_inc(v_infoState_2894_);
lean_inc(v_messages_2893_);
lean_inc(v_cache_2892_);
lean_inc(v_traceState_2887_);
lean_inc(v_auxDeclNGen_2891_);
lean_inc(v_ngen_2890_);
lean_inc(v_nextMacroScope_2889_);
lean_inc(v_env_2888_);
lean_dec(v___x_2886_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2918_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
uint64_t v_tid_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2916_; 
v_tid_2899_ = lean_ctor_get_uint64(v_traceState_2887_, sizeof(void*)*1);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_traceState_2887_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v_traceState_2887_, 0);
lean_dec(v_unused_2917_);
v___x_2901_ = v_traceState_2887_;
v_isShared_2902_ = v_isSharedCheck_2916_;
goto v_resetjp_2900_;
}
else
{
lean_dec(v_traceState_2887_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2916_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v_ref_2850_);
lean_ctor_set(v___x_2903_, 1, v_a_2882_);
v___x_2904_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2848_, v___x_2903_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2904_);
v___x_2906_ = v___x_2901_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2904_);
lean_ctor_set_uint64(v_reuseFailAlloc_2915_, sizeof(void*)*1, v_tid_2899_);
v___x_2906_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 4, v___x_2906_);
v___x_2908_ = v___x_2897_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_env_2888_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_nextMacroScope_2889_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_ngen_2890_);
lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_auxDeclNGen_2891_);
lean_ctor_set(v_reuseFailAlloc_2914_, 4, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2914_, 5, v_cache_2892_);
lean_ctor_set(v_reuseFailAlloc_2914_, 6, v_messages_2893_);
lean_ctor_set(v_reuseFailAlloc_2914_, 7, v_infoState_2894_);
lean_ctor_set(v_reuseFailAlloc_2914_, 8, v_snapshotTasks_2895_);
v___x_2908_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2909_ = lean_st_ref_set(v___y_2853_, v___x_2908_);
v___x_2910_ = lean_box(0);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2910_);
v___x_2912_ = v___x_2884_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_oldTraces_2920_, lean_object* v_data_2921_, lean_object* v_ref_2922_, lean_object* v_msg_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2920_, v_data_2921_, v_ref_2922_, v_msg_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2927_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2930_ = l_Lean_stringToMessageData(v___x_2929_);
return v___x_2930_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2));
v___x_2933_ = l_Lean_stringToMessageData(v___x_2932_);
return v___x_2933_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4(void){
_start:
{
lean_object* v___x_2934_; double v___x_2935_; 
v___x_2934_ = lean_unsigned_to_nat(1000u);
v___x_2935_ = lean_float_of_nat(v___x_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2936_, uint8_t v_collapsed_2937_, lean_object* v_tag_2938_, lean_object* v_opts_2939_, uint8_t v_clsEnabled_2940_, lean_object* v_oldTraces_2941_, lean_object* v_msg_2942_, lean_object* v_resStartStop_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_fst_2947_; lean_object* v_snd_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3046_; 
v_fst_2947_ = lean_ctor_get(v_resStartStop_2943_, 0);
v_snd_2948_ = lean_ctor_get(v_resStartStop_2943_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_resStartStop_2943_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_2950_ = v_resStartStop_2943_;
v_isShared_2951_ = v_isSharedCheck_3046_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_snd_2948_);
lean_inc(v_fst_2947_);
lean_dec(v_resStartStop_2943_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3046_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v_data_2955_; lean_object* v_fst_2966_; lean_object* v_snd_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3045_; 
v_fst_2966_ = lean_ctor_get(v_snd_2948_, 0);
v_snd_2967_ = lean_ctor_get(v_snd_2948_, 1);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_snd_2948_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_2969_ = v_snd_2948_;
v_isShared_2970_ = v_isSharedCheck_3045_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_snd_2967_);
lean_inc(v_fst_2966_);
lean_dec(v_snd_2948_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3045_;
goto v_resetjp_2968_;
}
v___jp_2952_:
{
lean_object* v___x_2956_; 
lean_inc(v___y_2953_);
v___x_2956_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2941_, v_data_2955_, v___y_2953_, v___y_2954_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v___x_2957_; 
lean_dec_ref(v___x_2956_);
v___x_2957_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2947_);
return v___x_2957_;
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_fst_2947_);
v_a_2958_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2956_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2956_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; lean_object* v___y_2974_; lean_object* v_a_2975_; uint8_t v___y_2999_; double v___y_3030_; 
v___x_2971_ = l_Lean_trace_profiler;
v___x_2972_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2939_, v___x_2971_);
if (v___x_2972_ == 0)
{
v___y_2999_ = v___x_2972_;
goto v___jp_2998_;
}
else
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3036_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2939_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; double v___x_3039_; double v___x_3040_; double v___x_3041_; 
v___x_3037_ = l_Lean_trace_profiler_threshold;
v___x_3038_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2939_, v___x_3037_);
v___x_3039_ = lean_float_of_nat(v___x_3038_);
v___x_3040_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4);
v___x_3041_ = lean_float_div(v___x_3039_, v___x_3040_);
v___y_3030_ = v___x_3041_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; double v___x_3044_; 
v___x_3042_ = l_Lean_trace_profiler_threshold;
v___x_3043_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2939_, v___x_3042_);
v___x_3044_ = lean_float_of_nat(v___x_3043_);
v___y_3030_ = v___x_3044_;
goto v___jp_3029_;
}
}
v___jp_2973_:
{
uint8_t v_result_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v_result_2976_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_fst_2947_);
v___x_2977_ = l_Lean_TraceResult_toEmoji(v_result_2976_);
v___x_2978_ = l_Lean_stringToMessageData(v___x_2977_);
v___x_2979_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 7);
lean_ctor_set(v___x_2969_, 1, v___x_2979_);
lean_ctor_set(v___x_2969_, 0, v___x_2978_);
v___x_2981_ = v___x_2969_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v_m_2983_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set_tag(v___x_2950_, 7);
lean_ctor_set(v___x_2950_, 1, v_a_2975_);
lean_ctor_set(v___x_2950_, 0, v___x_2981_);
v_m_2983_ = v___x_2950_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_a_2975_);
v_m_2983_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; double v___x_2986_; lean_object* v_data_2987_; 
v___x_2984_ = lean_box(v_result_2976_);
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
v___x_2986_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2938_);
lean_inc_ref(v___x_2985_);
lean_inc(v_cls_2936_);
v_data_2987_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2987_, 0, v_cls_2936_);
lean_ctor_set(v_data_2987_, 1, v___x_2985_);
lean_ctor_set(v_data_2987_, 2, v_tag_2938_);
lean_ctor_set_float(v_data_2987_, sizeof(void*)*3, v___x_2986_);
lean_ctor_set_float(v_data_2987_, sizeof(void*)*3 + 8, v___x_2986_);
lean_ctor_set_uint8(v_data_2987_, sizeof(void*)*3 + 16, v_collapsed_2937_);
if (v___x_2972_ == 0)
{
lean_dec_ref(v___x_2985_);
lean_dec(v_snd_2967_);
lean_dec(v_fst_2966_);
lean_dec_ref(v_tag_2938_);
lean_dec(v_cls_2936_);
v___y_2953_ = v___y_2974_;
v___y_2954_ = v_m_2983_;
v_data_2955_ = v_data_2987_;
goto v___jp_2952_;
}
else
{
lean_object* v_data_2988_; double v___x_2989_; double v___x_2990_; 
lean_dec_ref(v_data_2987_);
v_data_2988_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2988_, 0, v_cls_2936_);
lean_ctor_set(v_data_2988_, 1, v___x_2985_);
lean_ctor_set(v_data_2988_, 2, v_tag_2938_);
v___x_2989_ = lean_unbox_float(v_fst_2966_);
lean_dec(v_fst_2966_);
lean_ctor_set_float(v_data_2988_, sizeof(void*)*3, v___x_2989_);
v___x_2990_ = lean_unbox_float(v_snd_2967_);
lean_dec(v_snd_2967_);
lean_ctor_set_float(v_data_2988_, sizeof(void*)*3 + 8, v___x_2990_);
lean_ctor_set_uint8(v_data_2988_, sizeof(void*)*3 + 16, v_collapsed_2937_);
v___y_2953_ = v___y_2974_;
v___y_2954_ = v_m_2983_;
v_data_2955_ = v_data_2988_;
goto v___jp_2952_;
}
}
}
}
v___jp_2993_:
{
lean_object* v_ref_2994_; lean_object* v___x_2995_; 
v_ref_2994_ = lean_ctor_get(v___y_2944_, 5);
lean_inc(v___y_2945_);
lean_inc_ref(v___y_2944_);
lean_inc(v_fst_2947_);
v___x_2995_ = lean_apply_4(v_msg_2942_, v_fst_2947_, v___y_2944_, v___y_2945_, lean_box(0));
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
v___y_2974_ = v_ref_2994_;
v_a_2975_ = v_a_2996_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_2997_; 
lean_dec_ref(v___x_2995_);
v___x_2997_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3);
v___y_2974_ = v_ref_2994_;
v_a_2975_ = v___x_2997_;
goto v___jp_2973_;
}
}
v___jp_2998_:
{
if (v_clsEnabled_2940_ == 0)
{
if (v___y_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v_traceState_3001_; lean_object* v_env_3002_; lean_object* v_nextMacroScope_3003_; lean_object* v_ngen_3004_; lean_object* v_auxDeclNGen_3005_; lean_object* v_cache_3006_; lean_object* v_messages_3007_; lean_object* v_infoState_3008_; lean_object* v_snapshotTasks_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3028_; 
lean_del_object(v___x_2969_);
lean_dec(v_snd_2967_);
lean_dec(v_fst_2966_);
lean_del_object(v___x_2950_);
lean_dec_ref(v_msg_2942_);
lean_dec_ref(v_tag_2938_);
lean_dec(v_cls_2936_);
v___x_3000_ = lean_st_ref_take(v___y_2945_);
v_traceState_3001_ = lean_ctor_get(v___x_3000_, 4);
v_env_3002_ = lean_ctor_get(v___x_3000_, 0);
v_nextMacroScope_3003_ = lean_ctor_get(v___x_3000_, 1);
v_ngen_3004_ = lean_ctor_get(v___x_3000_, 2);
v_auxDeclNGen_3005_ = lean_ctor_get(v___x_3000_, 3);
v_cache_3006_ = lean_ctor_get(v___x_3000_, 5);
v_messages_3007_ = lean_ctor_get(v___x_3000_, 6);
v_infoState_3008_ = lean_ctor_get(v___x_3000_, 7);
v_snapshotTasks_3009_ = lean_ctor_get(v___x_3000_, 8);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3011_ = v___x_3000_;
v_isShared_3012_ = v_isSharedCheck_3028_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_snapshotTasks_3009_);
lean_inc(v_infoState_3008_);
lean_inc(v_messages_3007_);
lean_inc(v_cache_3006_);
lean_inc(v_traceState_3001_);
lean_inc(v_auxDeclNGen_3005_);
lean_inc(v_ngen_3004_);
lean_inc(v_nextMacroScope_3003_);
lean_inc(v_env_3002_);
lean_dec(v___x_3000_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3028_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
uint64_t v_tid_3013_; lean_object* v_traces_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3027_; 
v_tid_3013_ = lean_ctor_get_uint64(v_traceState_3001_, sizeof(void*)*1);
v_traces_3014_ = lean_ctor_get(v_traceState_3001_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_traceState_3001_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3016_ = v_traceState_3001_;
v_isShared_3017_ = v_isSharedCheck_3027_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_traces_3014_);
lean_dec(v_traceState_3001_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3027_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3018_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2941_, v_traces_3014_);
lean_dec_ref(v_traces_3014_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3018_);
lean_ctor_set_uint64(v_reuseFailAlloc_3026_, sizeof(void*)*1, v_tid_3013_);
v___x_3020_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3022_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 4, v___x_3020_);
v___x_3022_ = v___x_3011_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_env_3002_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_nextMacroScope_3003_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_ngen_3004_);
lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_auxDeclNGen_3005_);
lean_ctor_set(v_reuseFailAlloc_3025_, 4, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3025_, 5, v_cache_3006_);
lean_ctor_set(v_reuseFailAlloc_3025_, 6, v_messages_3007_);
lean_ctor_set(v_reuseFailAlloc_3025_, 7, v_infoState_3008_);
lean_ctor_set(v_reuseFailAlloc_3025_, 8, v_snapshotTasks_3009_);
v___x_3022_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_st_ref_set(v___y_2945_, v___x_3022_);
v___x_3024_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2947_);
return v___x_3024_;
}
}
}
}
}
else
{
goto v___jp_2993_;
}
}
else
{
goto v___jp_2993_;
}
}
v___jp_3029_:
{
double v___x_3031_; double v___x_3032_; double v___x_3033_; uint8_t v___x_3034_; 
v___x_3031_ = lean_unbox_float(v_snd_2967_);
v___x_3032_ = lean_unbox_float(v_fst_2966_);
v___x_3033_ = lean_float_sub(v___x_3031_, v___x_3032_);
v___x_3034_ = lean_float_decLt(v___y_3030_, v___x_3033_);
v___y_2999_ = v___x_3034_;
goto v___jp_2998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3047_, lean_object* v_collapsed_3048_, lean_object* v_tag_3049_, lean_object* v_opts_3050_, lean_object* v_clsEnabled_3051_, lean_object* v_oldTraces_3052_, lean_object* v_msg_3053_, lean_object* v_resStartStop_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
uint8_t v_collapsed_boxed_3058_; uint8_t v_clsEnabled_boxed_3059_; lean_object* v_res_3060_; 
v_collapsed_boxed_3058_ = lean_unbox(v_collapsed_3048_);
v_clsEnabled_boxed_3059_ = lean_unbox(v_clsEnabled_3051_);
v_res_3060_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3047_, v_collapsed_boxed_3058_, v_tag_3049_, v_opts_3050_, v_clsEnabled_boxed_3059_, v_oldTraces_3052_, v_msg_3053_, v_resStartStop_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec_ref(v_opts_3050_);
return v_res_3060_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
lean_ctor_set(v___x_3065_, 2, v___x_3064_);
lean_ctor_set(v___x_3065_, 3, v___x_3064_);
lean_ctor_set(v___x_3065_, 4, v___x_3063_);
lean_ctor_set(v___x_3065_, 5, v___x_3063_);
lean_ctor_set(v___x_3065_, 6, v___x_3063_);
lean_ctor_set(v___x_3065_, 7, v___x_3063_);
lean_ctor_set(v___x_3065_, 8, v___x_3063_);
lean_ctor_set(v___x_3065_, 9, v___x_3063_);
return v___x_3065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3067_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
lean_ctor_set(v___x_3067_, 2, v___x_3066_);
lean_ctor_set(v___x_3067_, 3, v___x_3066_);
lean_ctor_set(v___x_3067_, 4, v___x_3066_);
lean_ctor_set(v___x_3067_, 5, v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
lean_ctor_set(v___x_3069_, 2, v___x_3068_);
lean_ctor_set(v___x_3069_, 3, v___x_3068_);
lean_ctor_set(v___x_3069_, 4, v___x_3068_);
return v___x_3069_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3070_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3071_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3072_ = lean_box(1);
v___x_3073_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3074_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
lean_ctor_set(v___x_3075_, 2, v___x_3072_);
lean_ctor_set(v___x_3075_, 3, v___x_3071_);
lean_ctor_set(v___x_3075_, 4, v___x_3070_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3081_ = l_Lean_Name_append(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3082_; double v___x_3083_; 
v___x_3082_ = lean_unsigned_to_nat(1000000000u);
v___x_3083_ = lean_float_of_nat(v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3084_, lean_object* v_name_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_options_3089_; uint8_t v_hasTrace_3090_; 
v_options_3089_ = lean_ctor_get(v___y_3086_, 2);
v_hasTrace_3090_ = lean_ctor_get_uint8(v_options_3089_, sizeof(void*)*1);
if (v_hasTrace_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v_env_3092_; lean_object* v___x_3093_; 
lean_dec_ref(v___f_3084_);
v___x_3091_ = lean_st_ref_get(v___y_3087_);
v_env_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_ref(v_env_3092_);
lean_dec(v___x_3091_);
lean_inc(v_name_3085_);
v___x_3093_ = l_Lean_Meta_declFromEqLikeName(v_env_3092_, v_name_3085_);
if (lean_obj_tag(v___x_3093_) == 1)
{
lean_object* v_val_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3193_; 
v_val_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3193_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_val_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3193_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_fst_3098_; lean_object* v_snd_3099_; lean_object* v___x_3100_; lean_object* v_env_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_fst_3098_ = lean_ctor_get(v_val_3094_, 0);
lean_inc_n(v_fst_3098_, 2);
v_snd_3099_ = lean_ctor_get(v_val_3094_, 1);
lean_inc_n(v_snd_3099_, 2);
lean_dec(v_val_3094_);
v___x_3100_ = lean_st_ref_get(v___y_3087_);
v_env_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_ref(v_env_3101_);
lean_dec(v___x_3100_);
v___x_3102_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3101_, v_fst_3098_, v_snd_3099_);
v___x_3103_ = lean_name_eq(v_name_3085_, v___x_3102_);
lean_dec(v___x_3102_);
lean_dec(v_name_3085_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_dec(v_snd_3099_);
lean_dec(v_fst_3098_);
v___x_3104_ = lean_box(v_hasTrace_3090_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set_tag(v___x_3096_, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3104_);
v___x_3106_ = v___x_3096_;
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
else
{
uint8_t v___x_3108_; lean_object* v_a_3110_; 
lean_inc(v_snd_3099_);
v___x_3108_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3099_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v_a_3127_; 
lean_del_object(v___x_3096_);
v___x_3124_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3125_ = lean_string_dec_eq(v_snd_3099_, v___x_3124_);
lean_dec(v_snd_3099_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec(v_fst_3098_);
v___x_3139_ = lean_box(v_hasTrace_3090_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
else
{
uint8_t v___x_3141_; uint8_t v___x_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; uint64_t v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3141_ = 1;
v___x_3142_ = 0;
v___x_3143_ = 2;
v___x_3144_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3144_, 0, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3144_, 1, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3144_, 2, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3144_, 3, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3144_, 4, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3144_, 5, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 6, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 7, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3144_, 8, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 9, v___x_3141_);
lean_ctor_set_uint8(v___x_3144_, 10, v___x_3142_);
lean_ctor_set_uint8(v___x_3144_, 11, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 12, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 13, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 14, v___x_3143_);
lean_ctor_set_uint8(v___x_3144_, 15, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 16, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 17, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 18, v___x_3125_);
v___x_3145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3144_);
v___x_3146_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set_uint64(v___x_3146_, sizeof(void*)*1, v___x_3145_);
v___x_3147_ = lean_box(1);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3150_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3152_, 0, v___x_3146_);
lean_ctor_set(v___x_3152_, 1, v___x_3147_);
lean_ctor_set(v___x_3152_, 2, v___x_3149_);
lean_ctor_set(v___x_3152_, 3, v___x_3150_);
lean_ctor_set(v___x_3152_, 4, v___x_3151_);
lean_ctor_set(v___x_3152_, 5, v___x_3148_);
lean_ctor_set(v___x_3152_, 6, v___x_3151_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7 + 1, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7 + 2, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7 + 3, v___x_3103_);
v___x_3153_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3154_ = lean_st_mk_ref(v___x_3153_);
v___x_3155_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3098_, v___x_3103_, v___x_3152_, v___x_3154_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3152_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3157_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref(v___x_3155_);
v___x_3157_ = lean_st_ref_get(v___x_3154_);
lean_dec(v___x_3154_);
lean_dec(v___x_3157_);
v_a_3127_ = v_a_3156_;
goto v___jp_3126_;
}
else
{
lean_dec(v___x_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3158_; 
v_a_3158_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3158_);
lean_dec_ref(v___x_3155_);
v_a_3127_ = v_a_3158_;
goto v___jp_3126_;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_a_3159_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3155_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3155_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
v___jp_3126_:
{
if (lean_obj_tag(v_a_3127_) == 0)
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_box(v_hasTrace_3090_);
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
return v___x_3129_;
}
else
{
lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3137_; 
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3127_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v_a_3127_, 0);
lean_dec(v_unused_3138_);
v___x_3131_ = v_a_3127_;
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
else
{
lean_dec(v_a_3127_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3133_ = lean_box(v___x_3125_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3133_);
v___x_3135_ = v___x_3131_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
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
else
{
uint8_t v___x_3167_; uint8_t v___x_3168_; uint8_t v___x_3169_; lean_object* v___x_3170_; uint64_t v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_dec(v_snd_3099_);
v___x_3167_ = 1;
v___x_3168_ = 0;
v___x_3169_ = 2;
v___x_3170_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3170_, 0, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3170_, 1, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3170_, 2, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3170_, 3, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3170_, 4, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3170_, 5, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 6, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 7, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3170_, 8, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 9, v___x_3167_);
lean_ctor_set_uint8(v___x_3170_, 10, v___x_3168_);
lean_ctor_set_uint8(v___x_3170_, 11, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 12, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 13, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 14, v___x_3169_);
lean_ctor_set_uint8(v___x_3170_, 15, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 16, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 17, v___x_3108_);
lean_ctor_set_uint8(v___x_3170_, 18, v___x_3108_);
v___x_3171_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set_uint64(v___x_3172_, sizeof(void*)*1, v___x_3171_);
v___x_3173_ = lean_box(1);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3176_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3178_, 0, v___x_3172_);
lean_ctor_set(v___x_3178_, 1, v___x_3173_);
lean_ctor_set(v___x_3178_, 2, v___x_3175_);
lean_ctor_set(v___x_3178_, 3, v___x_3176_);
lean_ctor_set(v___x_3178_, 4, v___x_3177_);
lean_ctor_set(v___x_3178_, 5, v___x_3174_);
lean_ctor_set(v___x_3178_, 6, v___x_3177_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*7, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*7 + 1, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*7 + 2, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*7 + 3, v___x_3103_);
v___x_3179_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3180_ = lean_st_mk_ref(v___x_3179_);
v___x_3181_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3098_, v___x_3178_, v___x_3180_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3178_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref(v___x_3181_);
v___x_3183_ = lean_st_ref_get(v___x_3180_);
lean_dec(v___x_3180_);
lean_dec(v___x_3183_);
v_a_3110_ = v_a_3182_;
goto v___jp_3109_;
}
else
{
lean_dec(v___x_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3184_; 
v_a_3184_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3181_);
v_a_3110_ = v_a_3184_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_del_object(v___x_3096_);
v_a_3185_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3181_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3181_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
v___jp_3109_:
{
if (lean_obj_tag(v_a_3110_) == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = lean_box(v_hasTrace_3090_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set_tag(v___x_3096_, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3111_);
v___x_3113_ = v___x_3096_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
else
{
lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3122_; 
lean_del_object(v___x_3096_);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_a_3110_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v_a_3110_, 0);
lean_dec(v_unused_3123_);
v___x_3116_ = v_a_3110_;
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
else
{
lean_dec(v_a_3110_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = lean_box(v___x_3108_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set_tag(v___x_3116_, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3118_);
v___x_3120_ = v___x_3116_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec(v___x_3093_);
lean_dec(v_name_3085_);
v___x_3194_ = lean_box(v_hasTrace_3090_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
return v___x_3195_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3196_; lean_object* v___f_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v_a_3205_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v_a_3220_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v_a_3227_; uint8_t v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v_a_3232_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_a_3241_; lean_object* v___y_3251_; lean_object* v___y_3252_; uint8_t v_a_3253_; uint8_t v___y_3257_; lean_object* v___y_3258_; uint8_t v___y_3259_; lean_object* v___y_3260_; lean_object* v_a_3261_; uint8_t v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v_a_3266_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v_a_3271_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; 
v_inheritedTraceOptions_3196_ = lean_ctor_get(v___y_3086_, 13);
lean_inc(v_name_3085_);
v___f_3197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3197_, 0, v_name_3085_);
v___x_3198_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3199_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3200_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3196_, v_options_3089_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3396_; uint8_t v___x_3397_; lean_object* v_a_3399_; lean_object* v_a_3412_; 
v___x_3396_ = l_Lean_trace_profiler;
v___x_3397_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3089_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3424_; lean_object* v_env_3425_; lean_object* v___x_3426_; 
lean_dec_ref(v___f_3197_);
lean_dec_ref(v___f_3084_);
v___x_3424_ = lean_st_ref_get(v___y_3087_);
v_env_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc_ref(v_env_3425_);
lean_dec(v___x_3424_);
lean_inc(v_name_3085_);
v___x_3426_ = l_Lean_Meta_declFromEqLikeName(v_env_3425_, v_name_3085_);
if (lean_obj_tag(v___x_3426_) == 1)
{
lean_object* v_val_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3500_; 
v_val_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3500_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_val_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3500_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3433_; lean_object* v_env_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v_fst_3431_ = lean_ctor_get(v_val_3427_, 0);
lean_inc_n(v_fst_3431_, 2);
v_snd_3432_ = lean_ctor_get(v_val_3427_, 1);
lean_inc_n(v_snd_3432_, 2);
lean_dec(v_val_3427_);
v___x_3433_ = lean_st_ref_get(v___y_3087_);
v_env_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc_ref(v_env_3434_);
lean_dec(v___x_3433_);
v___x_3435_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3434_, v_fst_3431_, v_snd_3432_);
v___x_3436_ = lean_name_eq(v_name_3085_, v___x_3435_);
lean_dec(v___x_3435_);
lean_dec(v_name_3085_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
v___x_3437_ = lean_box(v___x_3397_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3437_);
v___x_3439_ = v___x_3429_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
else
{
uint8_t v___x_3441_; 
lean_inc(v_snd_3432_);
v___x_3441_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3432_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3443_ = lean_string_dec_eq(v_snd_3432_, v___x_3442_);
lean_dec(v_snd_3432_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_dec(v_fst_3431_);
v___x_3444_ = lean_box(v___x_3397_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3444_);
v___x_3446_ = v___x_3429_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
else
{
uint8_t v___x_3448_; uint8_t v___x_3449_; uint8_t v___x_3450_; lean_object* v___x_3451_; uint64_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_del_object(v___x_3429_);
v___x_3448_ = 1;
v___x_3449_ = 0;
v___x_3450_ = 2;
v___x_3451_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3451_, 0, v___x_3397_);
lean_ctor_set_uint8(v___x_3451_, 1, v___x_3397_);
lean_ctor_set_uint8(v___x_3451_, 2, v___x_3397_);
lean_ctor_set_uint8(v___x_3451_, 3, v___x_3397_);
lean_ctor_set_uint8(v___x_3451_, 4, v___x_3397_);
lean_ctor_set_uint8(v___x_3451_, 5, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 6, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 7, v___x_3397_);
lean_ctor_set_uint8(v___x_3451_, 8, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 9, v___x_3448_);
lean_ctor_set_uint8(v___x_3451_, 10, v___x_3449_);
lean_ctor_set_uint8(v___x_3451_, 11, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 12, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 13, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 14, v___x_3450_);
lean_ctor_set_uint8(v___x_3451_, 15, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 16, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 17, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3451_, 18, v_hasTrace_3090_);
v___x_3452_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3451_);
v___x_3453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set_uint64(v___x_3453_, sizeof(void*)*1, v___x_3452_);
v___x_3454_ = lean_box(1);
v___x_3455_ = lean_unsigned_to_nat(0u);
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3459_, 0, v___x_3453_);
lean_ctor_set(v___x_3459_, 1, v___x_3454_);
lean_ctor_set(v___x_3459_, 2, v___x_3456_);
lean_ctor_set(v___x_3459_, 3, v___x_3457_);
lean_ctor_set(v___x_3459_, 4, v___x_3458_);
lean_ctor_set(v___x_3459_, 5, v___x_3455_);
lean_ctor_set(v___x_3459_, 6, v___x_3458_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7, v___x_3397_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7 + 1, v___x_3397_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7 + 2, v___x_3397_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3460_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3461_ = lean_st_mk_ref(v___x_3460_);
v___x_3462_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3431_, v_hasTrace_3090_, v___x_3459_, v___x_3461_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3459_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3462_);
v___x_3464_ = lean_st_ref_get(v___x_3461_);
lean_dec(v___x_3461_);
lean_dec(v___x_3464_);
v_a_3412_ = v_a_3463_;
goto v___jp_3411_;
}
else
{
lean_dec(v___x_3461_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3465_; 
v_a_3465_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3465_);
lean_dec_ref(v___x_3462_);
v_a_3412_ = v_a_3465_;
goto v___jp_3411_;
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
v_a_3466_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3462_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3462_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
}
else
{
uint8_t v___x_3474_; uint8_t v___x_3475_; uint8_t v___x_3476_; lean_object* v___x_3477_; uint64_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec(v_snd_3432_);
lean_del_object(v___x_3429_);
v___x_3474_ = 1;
v___x_3475_ = 0;
v___x_3476_ = 2;
v___x_3477_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3477_, 0, v___x_3397_);
lean_ctor_set_uint8(v___x_3477_, 1, v___x_3397_);
lean_ctor_set_uint8(v___x_3477_, 2, v___x_3397_);
lean_ctor_set_uint8(v___x_3477_, 3, v___x_3397_);
lean_ctor_set_uint8(v___x_3477_, 4, v___x_3397_);
lean_ctor_set_uint8(v___x_3477_, 5, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 6, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 7, v___x_3397_);
lean_ctor_set_uint8(v___x_3477_, 8, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 9, v___x_3474_);
lean_ctor_set_uint8(v___x_3477_, 10, v___x_3475_);
lean_ctor_set_uint8(v___x_3477_, 11, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 12, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 13, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 14, v___x_3476_);
lean_ctor_set_uint8(v___x_3477_, 15, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 16, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 17, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3477_, 18, v_hasTrace_3090_);
v___x_3478_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3477_);
v___x_3479_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3479_, 0, v___x_3477_);
lean_ctor_set_uint64(v___x_3479_, sizeof(void*)*1, v___x_3478_);
v___x_3480_ = lean_box(1);
v___x_3481_ = lean_unsigned_to_nat(0u);
v___x_3482_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3483_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3485_, 0, v___x_3479_);
lean_ctor_set(v___x_3485_, 1, v___x_3480_);
lean_ctor_set(v___x_3485_, 2, v___x_3482_);
lean_ctor_set(v___x_3485_, 3, v___x_3483_);
lean_ctor_set(v___x_3485_, 4, v___x_3484_);
lean_ctor_set(v___x_3485_, 5, v___x_3481_);
lean_ctor_set(v___x_3485_, 6, v___x_3484_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*7, v___x_3397_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*7 + 1, v___x_3397_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*7 + 2, v___x_3397_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3486_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3487_ = lean_st_mk_ref(v___x_3486_);
v___x_3488_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3431_, v___x_3485_, v___x_3487_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3485_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3488_);
v___x_3490_ = lean_st_ref_get(v___x_3487_);
lean_dec(v___x_3487_);
lean_dec(v___x_3490_);
v_a_3399_ = v_a_3489_;
goto v___jp_3398_;
}
else
{
lean_dec(v___x_3487_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3491_; 
v_a_3491_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3491_);
lean_dec_ref(v___x_3488_);
v_a_3399_ = v_a_3491_;
goto v___jp_3398_;
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
v_a_3492_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3488_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3488_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
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
lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec(v___x_3426_);
lean_dec(v_name_3085_);
v___x_3501_ = lean_box(v___x_3397_);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
}
else
{
goto v___jp_3280_;
}
v___jp_3398_:
{
if (lean_obj_tag(v_a_3399_) == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_box(v___x_3397_);
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
else
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3409_; 
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3399_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v_a_3399_, 0);
lean_dec(v_unused_3410_);
v___x_3403_ = v_a_3399_;
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v_a_3399_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = lean_box(v_hasTrace_3090_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3405_);
v___x_3407_ = v___x_3403_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
v___jp_3411_:
{
if (lean_obj_tag(v_a_3412_) == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_box(v___x_3397_);
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
else
{
lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3422_; 
v_isSharedCheck_3422_ = !lean_is_exclusive(v_a_3412_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; 
v_unused_3423_ = lean_ctor_get(v_a_3412_, 0);
lean_dec(v_unused_3423_);
v___x_3416_ = v_a_3412_;
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
else
{
lean_dec(v_a_3412_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = lean_box(v_hasTrace_3090_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
goto v___jp_3280_;
}
v___jp_3202_:
{
lean_object* v___x_3206_; double v___x_3207_; double v___x_3208_; double v___x_3209_; double v___x_3210_; double v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3206_ = lean_io_mono_nanos_now();
v___x_3207_ = lean_float_of_nat(v___y_3203_);
v___x_3208_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3209_ = lean_float_div(v___x_3207_, v___x_3208_);
v___x_3210_ = lean_float_of_nat(v___x_3206_);
v___x_3211_ = lean_float_div(v___x_3210_, v___x_3208_);
v___x_3212_ = lean_box_float(v___x_3209_);
v___x_3213_ = lean_box_float(v___x_3211_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_a_3205_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3198_, v_hasTrace_3090_, v___x_3199_, v_options_3089_, v___x_3201_, v___y_3204_, v___f_3197_, v___x_3215_, v___y_3086_, v___y_3087_);
return v___x_3216_;
}
v___jp_3217_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_box(v_a_3220_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v___y_3203_ = v___y_3218_;
v___y_3204_ = v___y_3219_;
v_a_3205_ = v___x_3222_;
goto v___jp_3202_;
}
v___jp_3223_:
{
if (lean_obj_tag(v_a_3227_) == 0)
{
v___y_3218_ = v___y_3225_;
v___y_3219_ = v___y_3226_;
v_a_3220_ = v___y_3224_;
goto v___jp_3217_;
}
else
{
lean_dec_ref(v_a_3227_);
v___y_3218_ = v___y_3225_;
v___y_3219_ = v___y_3226_;
v_a_3220_ = v_hasTrace_3090_;
goto v___jp_3217_;
}
}
v___jp_3228_:
{
if (lean_obj_tag(v_a_3232_) == 0)
{
v___y_3218_ = v___y_3230_;
v___y_3219_ = v___y_3231_;
v_a_3220_ = v___y_3229_;
goto v___jp_3217_;
}
else
{
lean_dec_ref(v_a_3232_);
v___y_3218_ = v___y_3230_;
v___y_3219_ = v___y_3231_;
v_a_3220_ = v_hasTrace_3090_;
goto v___jp_3217_;
}
}
v___jp_3233_:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_a_3236_);
v___y_3203_ = v___y_3234_;
v___y_3204_ = v___y_3235_;
v_a_3205_ = v___x_3237_;
goto v___jp_3202_;
}
v___jp_3238_:
{
lean_object* v___x_3242_; double v___x_3243_; double v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3242_ = lean_io_get_num_heartbeats();
v___x_3243_ = lean_float_of_nat(v___y_3239_);
v___x_3244_ = lean_float_of_nat(v___x_3242_);
v___x_3245_ = lean_box_float(v___x_3243_);
v___x_3246_ = lean_box_float(v___x_3244_);
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_a_3241_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3198_, v_hasTrace_3090_, v___x_3199_, v_options_3089_, v___x_3201_, v___y_3240_, v___f_3197_, v___x_3248_, v___y_3086_, v___y_3087_);
return v___x_3249_;
}
v___jp_3250_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_box(v_a_3253_);
v___x_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
v___y_3239_ = v___y_3251_;
v___y_3240_ = v___y_3252_;
v_a_3241_ = v___x_3255_;
goto v___jp_3238_;
}
v___jp_3256_:
{
if (lean_obj_tag(v_a_3261_) == 0)
{
v___y_3251_ = v___y_3258_;
v___y_3252_ = v___y_3260_;
v_a_3253_ = v___y_3259_;
goto v___jp_3250_;
}
else
{
lean_dec_ref(v_a_3261_);
v___y_3251_ = v___y_3258_;
v___y_3252_ = v___y_3260_;
v_a_3253_ = v___y_3257_;
goto v___jp_3250_;
}
}
v___jp_3262_:
{
if (lean_obj_tag(v_a_3266_) == 0)
{
uint8_t v___x_3267_; 
v___x_3267_ = 0;
v___y_3251_ = v___y_3264_;
v___y_3252_ = v___y_3265_;
v_a_3253_ = v___x_3267_;
goto v___jp_3250_;
}
else
{
lean_dec_ref(v_a_3266_);
v___y_3251_ = v___y_3264_;
v___y_3252_ = v___y_3265_;
v_a_3253_ = v___y_3263_;
goto v___jp_3250_;
}
}
v___jp_3268_:
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_a_3271_);
v___y_3239_ = v___y_3269_;
v___y_3240_ = v___y_3270_;
v_a_3241_ = v___x_3272_;
goto v___jp_3238_;
}
v___jp_3273_:
{
if (lean_obj_tag(v___y_3276_) == 0)
{
lean_object* v_a_3277_; uint8_t v___x_3278_; 
v_a_3277_ = lean_ctor_get(v___y_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___y_3276_);
v___x_3278_ = lean_unbox(v_a_3277_);
lean_dec(v_a_3277_);
v___y_3251_ = v___y_3274_;
v___y_3252_ = v___y_3275_;
v_a_3253_ = v___x_3278_;
goto v___jp_3250_;
}
else
{
lean_object* v_a_3279_; 
v_a_3279_ = lean_ctor_get(v___y_3276_, 0);
lean_inc(v_a_3279_);
lean_dec_ref(v___y_3276_);
v___y_3269_ = v___y_3274_;
v___y_3270_ = v___y_3275_;
v_a_3271_ = v_a_3279_;
goto v___jp_3268_;
}
}
v___jp_3280_:
{
lean_object* v___x_3281_; lean_object* v_a_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3281_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3087_);
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3284_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3089_, v___x_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v_env_3287_; lean_object* v___x_3288_; 
lean_dec_ref(v___f_3084_);
v___x_3285_ = lean_io_mono_nanos_now();
v___x_3286_ = lean_st_ref_get(v___y_3087_);
v_env_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc_ref(v_env_3287_);
lean_dec(v___x_3286_);
lean_inc(v_name_3085_);
v___x_3288_ = l_Lean_Meta_declFromEqLikeName(v_env_3287_, v_name_3085_);
if (lean_obj_tag(v___x_3288_) == 1)
{
lean_object* v_val_3289_; lean_object* v_fst_3290_; lean_object* v_snd_3291_; lean_object* v___x_3292_; lean_object* v_env_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v_val_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_val_3289_);
lean_dec_ref(v___x_3288_);
v_fst_3290_ = lean_ctor_get(v_val_3289_, 0);
lean_inc_n(v_fst_3290_, 2);
v_snd_3291_ = lean_ctor_get(v_val_3289_, 1);
lean_inc_n(v_snd_3291_, 2);
lean_dec(v_val_3289_);
v___x_3292_ = lean_st_ref_get(v___y_3087_);
v_env_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc_ref(v_env_3293_);
lean_dec(v___x_3292_);
v___x_3294_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3293_, v_fst_3290_, v_snd_3291_);
v___x_3295_ = lean_name_eq(v_name_3085_, v___x_3294_);
lean_dec(v___x_3294_);
lean_dec(v_name_3085_);
if (v___x_3295_ == 0)
{
lean_dec(v_snd_3291_);
lean_dec(v_fst_3290_);
v___y_3218_ = v___x_3285_;
v___y_3219_ = v_a_3282_;
v_a_3220_ = v___x_3284_;
goto v___jp_3217_;
}
else
{
uint8_t v___x_3296_; 
lean_inc(v_snd_3291_);
v___x_3296_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3291_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3298_ = lean_string_dec_eq(v_snd_3291_, v___x_3297_);
lean_dec(v_snd_3291_);
if (v___x_3298_ == 0)
{
lean_dec(v_fst_3290_);
v___y_3218_ = v___x_3285_;
v___y_3219_ = v_a_3282_;
v_a_3220_ = v___x_3284_;
goto v___jp_3217_;
}
else
{
uint8_t v___x_3299_; uint8_t v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; uint64_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3299_ = 1;
v___x_3300_ = 0;
v___x_3301_ = 2;
v___x_3302_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3302_, 0, v___x_3284_);
lean_ctor_set_uint8(v___x_3302_, 1, v___x_3284_);
lean_ctor_set_uint8(v___x_3302_, 2, v___x_3284_);
lean_ctor_set_uint8(v___x_3302_, 3, v___x_3284_);
lean_ctor_set_uint8(v___x_3302_, 4, v___x_3284_);
lean_ctor_set_uint8(v___x_3302_, 5, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 6, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 7, v___x_3284_);
lean_ctor_set_uint8(v___x_3302_, 8, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 9, v___x_3299_);
lean_ctor_set_uint8(v___x_3302_, 10, v___x_3300_);
lean_ctor_set_uint8(v___x_3302_, 11, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 12, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 13, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 14, v___x_3301_);
lean_ctor_set_uint8(v___x_3302_, 15, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 16, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 17, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3302_, 18, v_hasTrace_3090_);
v___x_3303_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set_uint64(v___x_3304_, sizeof(void*)*1, v___x_3303_);
v___x_3305_ = lean_box(1);
v___x_3306_ = lean_unsigned_to_nat(0u);
v___x_3307_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3310_, 0, v___x_3304_);
lean_ctor_set(v___x_3310_, 1, v___x_3305_);
lean_ctor_set(v___x_3310_, 2, v___x_3307_);
lean_ctor_set(v___x_3310_, 3, v___x_3308_);
lean_ctor_set(v___x_3310_, 4, v___x_3309_);
lean_ctor_set(v___x_3310_, 5, v___x_3306_);
lean_ctor_set(v___x_3310_, 6, v___x_3309_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7, v___x_3284_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 1, v___x_3284_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 2, v___x_3284_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3311_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3312_ = lean_st_mk_ref(v___x_3311_);
v___x_3313_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3290_, v_hasTrace_3090_, v___x_3310_, v___x_3312_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3310_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref(v___x_3313_);
v___x_3315_ = lean_st_ref_get(v___x_3312_);
lean_dec(v___x_3312_);
lean_dec(v___x_3315_);
v___y_3229_ = v___x_3284_;
v___y_3230_ = v___x_3285_;
v___y_3231_ = v_a_3282_;
v_a_3232_ = v_a_3314_;
goto v___jp_3228_;
}
else
{
lean_dec(v___x_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3316_; 
v_a_3316_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3316_);
lean_dec_ref(v___x_3313_);
v___y_3229_ = v___x_3284_;
v___y_3230_ = v___x_3285_;
v___y_3231_ = v_a_3282_;
v_a_3232_ = v_a_3316_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3317_; 
v_a_3317_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3313_);
v___y_3234_ = v___x_3285_;
v___y_3235_ = v_a_3282_;
v_a_3236_ = v_a_3317_;
goto v___jp_3233_;
}
}
}
}
else
{
uint8_t v___x_3318_; uint8_t v___x_3319_; uint8_t v___x_3320_; lean_object* v___x_3321_; uint64_t v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_dec(v_snd_3291_);
v___x_3318_ = 1;
v___x_3319_ = 0;
v___x_3320_ = 2;
v___x_3321_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3321_, 0, v___x_3284_);
lean_ctor_set_uint8(v___x_3321_, 1, v___x_3284_);
lean_ctor_set_uint8(v___x_3321_, 2, v___x_3284_);
lean_ctor_set_uint8(v___x_3321_, 3, v___x_3284_);
lean_ctor_set_uint8(v___x_3321_, 4, v___x_3284_);
lean_ctor_set_uint8(v___x_3321_, 5, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 6, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 7, v___x_3284_);
lean_ctor_set_uint8(v___x_3321_, 8, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 9, v___x_3318_);
lean_ctor_set_uint8(v___x_3321_, 10, v___x_3319_);
lean_ctor_set_uint8(v___x_3321_, 11, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 12, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 13, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 14, v___x_3320_);
lean_ctor_set_uint8(v___x_3321_, 15, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 16, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 17, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3321_, 18, v_hasTrace_3090_);
v___x_3322_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3321_);
v___x_3323_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set_uint64(v___x_3323_, sizeof(void*)*1, v___x_3322_);
v___x_3324_ = lean_box(1);
v___x_3325_ = lean_unsigned_to_nat(0u);
v___x_3326_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3329_, 0, v___x_3323_);
lean_ctor_set(v___x_3329_, 1, v___x_3324_);
lean_ctor_set(v___x_3329_, 2, v___x_3326_);
lean_ctor_set(v___x_3329_, 3, v___x_3327_);
lean_ctor_set(v___x_3329_, 4, v___x_3328_);
lean_ctor_set(v___x_3329_, 5, v___x_3325_);
lean_ctor_set(v___x_3329_, 6, v___x_3328_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7, v___x_3284_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7 + 1, v___x_3284_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7 + 2, v___x_3284_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3330_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3331_ = lean_st_mk_ref(v___x_3330_);
v___x_3332_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3290_, v___x_3329_, v___x_3331_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3329_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = lean_st_ref_get(v___x_3331_);
lean_dec(v___x_3331_);
lean_dec(v___x_3334_);
v___y_3224_ = v___x_3284_;
v___y_3225_ = v___x_3285_;
v___y_3226_ = v_a_3282_;
v_a_3227_ = v_a_3333_;
goto v___jp_3223_;
}
else
{
lean_dec(v___x_3331_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3335_; 
v_a_3335_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3332_);
v___y_3224_ = v___x_3284_;
v___y_3225_ = v___x_3285_;
v___y_3226_ = v_a_3282_;
v_a_3227_ = v_a_3335_;
goto v___jp_3223_;
}
else
{
lean_object* v_a_3336_; 
v_a_3336_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3332_);
v___y_3234_ = v___x_3285_;
v___y_3235_ = v_a_3282_;
v_a_3236_ = v_a_3336_;
goto v___jp_3233_;
}
}
}
}
}
else
{
lean_dec(v___x_3288_);
lean_dec(v_name_3085_);
v___y_3218_ = v___x_3285_;
v___y_3219_ = v_a_3282_;
v_a_3220_ = v___x_3284_;
goto v___jp_3217_;
}
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v_env_3339_; lean_object* v___x_3340_; 
v___x_3337_ = lean_io_get_num_heartbeats();
v___x_3338_ = lean_st_ref_get(v___y_3087_);
v_env_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc_ref(v_env_3339_);
lean_dec(v___x_3338_);
lean_inc(v_name_3085_);
v___x_3340_ = l_Lean_Meta_declFromEqLikeName(v_env_3339_, v_name_3085_);
if (lean_obj_tag(v___x_3340_) == 1)
{
lean_object* v_val_3341_; lean_object* v_fst_3342_; lean_object* v_snd_3343_; lean_object* v___x_3344_; lean_object* v_env_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_val_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_val_3341_);
lean_dec_ref(v___x_3340_);
v_fst_3342_ = lean_ctor_get(v_val_3341_, 0);
lean_inc_n(v_fst_3342_, 2);
v_snd_3343_ = lean_ctor_get(v_val_3341_, 1);
lean_inc_n(v_snd_3343_, 2);
lean_dec(v_val_3341_);
v___x_3344_ = lean_st_ref_get(v___y_3087_);
v_env_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc_ref(v_env_3345_);
lean_dec(v___x_3344_);
v___x_3346_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3345_, v_fst_3342_, v_snd_3343_);
v___x_3347_ = lean_name_eq(v_name_3085_, v___x_3346_);
lean_dec(v___x_3346_);
lean_dec(v_name_3085_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
lean_dec(v_snd_3343_);
lean_dec(v_fst_3342_);
v___x_3348_ = lean_box(0);
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
v___x_3349_ = lean_apply_4(v___f_3084_, v___x_3348_, v___y_3086_, v___y_3087_, lean_box(0));
v___y_3274_ = v___x_3337_;
v___y_3275_ = v_a_3282_;
v___y_3276_ = v___x_3349_;
goto v___jp_3273_;
}
else
{
uint8_t v___x_3350_; 
lean_inc(v_snd_3343_);
v___x_3350_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3343_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3352_ = lean_string_dec_eq(v_snd_3343_, v___x_3351_);
lean_dec(v_snd_3343_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_dec(v_fst_3342_);
v___x_3353_ = lean_box(0);
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
v___x_3354_ = lean_apply_4(v___f_3084_, v___x_3353_, v___y_3086_, v___y_3087_, lean_box(0));
v___y_3274_ = v___x_3337_;
v___y_3275_ = v_a_3282_;
v___y_3276_ = v___x_3354_;
goto v___jp_3273_;
}
else
{
uint8_t v___x_3355_; uint8_t v___x_3356_; uint8_t v___x_3357_; lean_object* v___x_3358_; uint64_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref(v___f_3084_);
v___x_3355_ = 1;
v___x_3356_ = 0;
v___x_3357_ = 2;
v___x_3358_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3358_, 0, v___x_3350_);
lean_ctor_set_uint8(v___x_3358_, 1, v___x_3350_);
lean_ctor_set_uint8(v___x_3358_, 2, v___x_3350_);
lean_ctor_set_uint8(v___x_3358_, 3, v___x_3350_);
lean_ctor_set_uint8(v___x_3358_, 4, v___x_3350_);
lean_ctor_set_uint8(v___x_3358_, 5, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 6, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 7, v___x_3350_);
lean_ctor_set_uint8(v___x_3358_, 8, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 9, v___x_3355_);
lean_ctor_set_uint8(v___x_3358_, 10, v___x_3356_);
lean_ctor_set_uint8(v___x_3358_, 11, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 12, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 13, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 14, v___x_3357_);
lean_ctor_set_uint8(v___x_3358_, 15, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 16, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 17, v___x_3284_);
lean_ctor_set_uint8(v___x_3358_, 18, v___x_3284_);
v___x_3359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3358_);
v___x_3360_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3360_, 0, v___x_3358_);
lean_ctor_set_uint64(v___x_3360_, sizeof(void*)*1, v___x_3359_);
v___x_3361_ = lean_box(1);
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3366_, 0, v___x_3360_);
lean_ctor_set(v___x_3366_, 1, v___x_3361_);
lean_ctor_set(v___x_3366_, 2, v___x_3363_);
lean_ctor_set(v___x_3366_, 3, v___x_3364_);
lean_ctor_set(v___x_3366_, 4, v___x_3365_);
lean_ctor_set(v___x_3366_, 5, v___x_3362_);
lean_ctor_set(v___x_3366_, 6, v___x_3365_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7, v___x_3350_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7 + 1, v___x_3350_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7 + 2, v___x_3350_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7 + 3, v___x_3284_);
v___x_3367_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3368_ = lean_st_mk_ref(v___x_3367_);
v___x_3369_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3342_, v___x_3284_, v___x_3366_, v___x_3368_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3366_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3371_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3369_);
v___x_3371_ = lean_st_ref_get(v___x_3368_);
lean_dec(v___x_3368_);
lean_dec(v___x_3371_);
v___y_3257_ = v___x_3284_;
v___y_3258_ = v___x_3337_;
v___y_3259_ = v___x_3350_;
v___y_3260_ = v_a_3282_;
v_a_3261_ = v_a_3370_;
goto v___jp_3256_;
}
else
{
lean_dec(v___x_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3372_);
lean_dec_ref(v___x_3369_);
v___y_3257_ = v___x_3284_;
v___y_3258_ = v___x_3337_;
v___y_3259_ = v___x_3350_;
v___y_3260_ = v_a_3282_;
v_a_3261_ = v_a_3372_;
goto v___jp_3256_;
}
else
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3373_);
lean_dec_ref(v___x_3369_);
v___y_3269_ = v___x_3337_;
v___y_3270_ = v_a_3282_;
v_a_3271_ = v_a_3373_;
goto v___jp_3268_;
}
}
}
}
else
{
uint8_t v___x_3374_; uint8_t v___x_3375_; uint8_t v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; uint64_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec(v_snd_3343_);
lean_dec_ref(v___f_3084_);
v___x_3374_ = 0;
v___x_3375_ = 1;
v___x_3376_ = 0;
v___x_3377_ = 2;
v___x_3378_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3378_, 0, v___x_3374_);
lean_ctor_set_uint8(v___x_3378_, 1, v___x_3374_);
lean_ctor_set_uint8(v___x_3378_, 2, v___x_3374_);
lean_ctor_set_uint8(v___x_3378_, 3, v___x_3374_);
lean_ctor_set_uint8(v___x_3378_, 4, v___x_3374_);
lean_ctor_set_uint8(v___x_3378_, 5, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 6, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 7, v___x_3374_);
lean_ctor_set_uint8(v___x_3378_, 8, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 9, v___x_3375_);
lean_ctor_set_uint8(v___x_3378_, 10, v___x_3376_);
lean_ctor_set_uint8(v___x_3378_, 11, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 12, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 13, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 14, v___x_3377_);
lean_ctor_set_uint8(v___x_3378_, 15, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 16, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 17, v___x_3284_);
lean_ctor_set_uint8(v___x_3378_, 18, v___x_3284_);
v___x_3379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set_uint64(v___x_3380_, sizeof(void*)*1, v___x_3379_);
v___x_3381_ = lean_box(1);
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3384_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3386_, 0, v___x_3380_);
lean_ctor_set(v___x_3386_, 1, v___x_3381_);
lean_ctor_set(v___x_3386_, 2, v___x_3383_);
lean_ctor_set(v___x_3386_, 3, v___x_3384_);
lean_ctor_set(v___x_3386_, 4, v___x_3385_);
lean_ctor_set(v___x_3386_, 5, v___x_3382_);
lean_ctor_set(v___x_3386_, 6, v___x_3385_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*7, v___x_3374_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*7 + 1, v___x_3374_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*7 + 2, v___x_3374_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*7 + 3, v___x_3284_);
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3388_ = lean_st_mk_ref(v___x_3387_);
v___x_3389_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3342_, v___x_3386_, v___x_3388_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___x_3386_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = lean_st_ref_get(v___x_3388_);
lean_dec(v___x_3388_);
lean_dec(v___x_3391_);
v___y_3263_ = v___x_3284_;
v___y_3264_ = v___x_3337_;
v___y_3265_ = v_a_3282_;
v_a_3266_ = v_a_3390_;
goto v___jp_3262_;
}
else
{
lean_dec(v___x_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3392_);
lean_dec_ref(v___x_3389_);
v___y_3263_ = v___x_3284_;
v___y_3264_ = v___x_3337_;
v___y_3265_ = v_a_3282_;
v_a_3266_ = v_a_3392_;
goto v___jp_3262_;
}
else
{
lean_object* v_a_3393_; 
v_a_3393_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3393_);
lean_dec_ref(v___x_3389_);
v___y_3269_ = v___x_3337_;
v___y_3270_ = v_a_3282_;
v_a_3271_ = v_a_3393_;
goto v___jp_3268_;
}
}
}
}
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec(v___x_3340_);
lean_dec(v_name_3085_);
v___x_3394_ = lean_box(0);
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
v___x_3395_ = lean_apply_4(v___f_3084_, v___x_3394_, v___y_3086_, v___y_3087_, lean_box(0));
v___y_3274_ = v___x_3337_;
v___y_3275_ = v_a_3282_;
v___y_3276_ = v___x_3395_;
goto v___jp_3273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3503_, lean_object* v_name_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3503_, v_name_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
return v_res_3508_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_unsigned_to_nat(3137104340u);
v___x_3553_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3554_ = l_Lean_Name_num___override(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3557_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3558_ = l_Lean_Name_str___override(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3561_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3562_ = l_Lean_Name_str___override(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_unsigned_to_nat(2u);
v___x_3564_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3565_ = l_Lean_Name_num___override(v___x_3564_, v___x_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3567_; lean_object* v___x_3568_; 
v___f_3567_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3568_ = l_Lean_registerReservedNameAction(v___f_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_dec_ref(v___x_3568_);
v___x_3569_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3570_ = 0;
v___x_3571_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3572_ = l_Lean_registerTraceClass(v___x_3569_, v___x_3570_, v___x_3571_);
return v___x_3572_;
}
else
{
return v___x_3568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b1_3575_, lean_object* v_x_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_3576_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b1_3581_, lean_object* v_x_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b1_3581_, v_x_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
return v_res_3586_;
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
