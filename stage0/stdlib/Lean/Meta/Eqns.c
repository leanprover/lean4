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
uint8_t v___y_700_; lean_object* v___y_701_; lean_object* v_fileName_702_; lean_object* v_fileMap_703_; lean_object* v_currRecDepth_704_; lean_object* v_ref_705_; lean_object* v_currNamespace_706_; lean_object* v_openDecls_707_; lean_object* v_initHeartbeats_708_; lean_object* v_maxHeartbeats_709_; lean_object* v_quotContext_710_; lean_object* v_currMacroScope_711_; lean_object* v_cancelTk_x3f_712_; uint8_t v_suppressElabErrors_713_; lean_object* v_inheritedTraceOptions_714_; lean_object* v___y_715_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_env_722_; lean_object* v___x_723_; lean_object* v_toEnvExtension_724_; lean_object* v_asyncMode_725_; lean_object* v_fileName_726_; lean_object* v_fileMap_727_; lean_object* v_options_728_; lean_object* v_currRecDepth_729_; lean_object* v_ref_730_; lean_object* v_currNamespace_731_; lean_object* v_openDecls_732_; lean_object* v_initHeartbeats_733_; lean_object* v_maxHeartbeats_734_; lean_object* v_quotContext_735_; lean_object* v_currMacroScope_736_; lean_object* v_cancelTk_x3f_737_; uint8_t v_suppressElabErrors_738_; lean_object* v_inheritedTraceOptions_739_; uint8_t v___y_741_; lean_object* v___y_742_; uint8_t v___y_743_; lean_object* v___y_766_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; 
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
v___x_771_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_772_ = 0;
v___x_773_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_771_, v___x_723_, v_env_722_, v_declName_692_, v_asyncMode_725_, v___x_772_);
if (lean_obj_tag(v___x_773_) == 1)
{
lean_object* v_val_774_; lean_object* v___y_776_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_val_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_774_);
lean_dec_ref(v___x_773_);
v___x_780_ = l_Lean_Meta_eqnAffectingOptions;
v___x_781_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_781_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_776_ = v_options_728_;
goto v___jp_775_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_782_ == 0)
{
if (v___x_781_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_776_ = v_options_728_;
goto v___jp_775_;
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_780_, v___x_783_, v___x_784_, v_options_728_);
v___y_776_ = v___x_785_;
goto v___jp_775_;
}
}
else
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_780_, v___x_786_, v___x_787_, v_options_728_);
v___y_776_ = v___x_788_;
goto v___jp_775_;
}
}
v___jp_775_:
{
size_t v_sz_777_; size_t v___x_778_; lean_object* v___x_779_; 
v_sz_777_ = lean_array_size(v_val_774_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_774_, v_sz_777_, v___x_778_, v___y_776_);
lean_dec(v_val_774_);
v___y_766_ = v___x_779_;
goto v___jp_765_;
}
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
lean_dec(v___x_773_);
v___x_789_ = l_Lean_Meta_eqnAffectingOptions;
v___x_790_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_790_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_766_ = v_options_728_;
goto v___jp_765_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_791_ == 0)
{
if (v___x_790_ == 0)
{
lean_inc_ref(v_options_728_);
v___y_766_ = v_options_728_;
goto v___jp_765_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_789_, v___x_792_, v___x_793_, v_options_728_);
v___y_766_ = v___x_794_;
goto v___jp_765_;
}
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_728_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_789_, v___x_795_, v___x_796_, v_options_728_);
v___y_766_ = v___x_797_;
goto v___jp_765_;
}
}
}
v___jp_699_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = l_Lean_maxRecDepth;
v___x_717_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_701_, v___x_716_);
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
lean_ctor_set(v___x_718_, 2, v___y_701_);
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
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*14, v___y_700_);
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
lean_object* v___x_744_; lean_object* v_env_745_; lean_object* v_nextMacroScope_746_; lean_object* v_ngen_747_; lean_object* v_auxDeclNGen_748_; lean_object* v_traceState_749_; lean_object* v_messages_750_; lean_object* v_infoState_751_; lean_object* v_snapshotTasks_752_; lean_object* v_newDecls_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_763_; 
v___x_744_ = lean_st_ref_take(v_a_697_);
v_env_745_ = lean_ctor_get(v___x_744_, 0);
v_nextMacroScope_746_ = lean_ctor_get(v___x_744_, 1);
v_ngen_747_ = lean_ctor_get(v___x_744_, 2);
v_auxDeclNGen_748_ = lean_ctor_get(v___x_744_, 3);
v_traceState_749_ = lean_ctor_get(v___x_744_, 4);
v_messages_750_ = lean_ctor_get(v___x_744_, 6);
v_infoState_751_ = lean_ctor_get(v___x_744_, 7);
v_snapshotTasks_752_ = lean_ctor_get(v___x_744_, 8);
v_newDecls_753_ = lean_ctor_get(v___x_744_, 9);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_744_, 5);
lean_dec(v_unused_764_);
v___x_755_ = v___x_744_;
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_newDecls_753_);
lean_inc(v_snapshotTasks_752_);
lean_inc(v_infoState_751_);
lean_inc(v_messages_750_);
lean_inc(v_traceState_749_);
lean_inc(v_auxDeclNGen_748_);
lean_inc(v_ngen_747_);
lean_inc(v_nextMacroScope_746_);
lean_inc(v_env_745_);
lean_dec(v___x_744_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = l_Lean_Kernel_enableDiag(v_env_745_, v___y_741_);
v___x_758_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 5, v___x_758_);
lean_ctor_set(v___x_755_, 0, v___x_757_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_nextMacroScope_746_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_ngen_747_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_auxDeclNGen_748_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_traceState_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 5, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 6, v_messages_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 7, v_infoState_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 8, v_snapshotTasks_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 9, v_newDecls_753_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_st_ref_set(v_a_697_, v___x_760_);
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
v___jp_765_:
{
lean_object* v_env_767_; lean_object* v___x_768_; uint8_t v___x_769_; uint8_t v___x_770_; 
v_env_767_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_env_767_);
lean_dec(v___x_721_);
v___x_768_ = l_Lean_diagnostics;
v___x_769_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_766_, v___x_768_);
v___x_770_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_767_);
lean_dec_ref(v_env_767_);
if (v___x_770_ == 0)
{
if (v___x_769_ == 0)
{
v___y_700_ = v___x_769_;
v___y_701_ = v___y_766_;
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
v___y_741_ = v___x_769_;
v___y_742_ = v___y_766_;
v___y_743_ = v___x_770_;
goto v___jp_740_;
}
}
else
{
v___y_741_ = v___x_769_;
v___y_742_ = v___y_766_;
v___y_743_ = v___x_769_;
goto v___jp_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_798_, lean_object* v_act_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_798_, v_act_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_806_, lean_object* v_declName_807_, lean_object* v_act_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_807_, v_act_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_815_, lean_object* v_declName_816_, lean_object* v_act_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_815_, v_declName_816_, v_act_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; lean_object* v_env_828_; lean_object* v_toConstantVal_829_; lean_object* v_value_830_; lean_object* v_all_831_; uint8_t v___y_833_; lean_object* v_type_841_; uint8_t v___x_842_; 
v___x_827_ = lean_st_ref_get(v___y_825_);
v_env_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref_n(v_env_828_, 2);
lean_dec(v___x_827_);
v_toConstantVal_829_ = lean_ctor_get(v_thm_824_, 0);
v_value_830_ = lean_ctor_get(v_thm_824_, 1);
v_all_831_ = lean_ctor_get(v_thm_824_, 2);
v_type_841_ = lean_ctor_get(v_toConstantVal_829_, 2);
v___x_842_ = l_Lean_Environment_hasUnsafe(v_env_828_, v_type_841_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = l_Lean_Environment_hasUnsafe(v_env_828_, v_value_830_);
v___y_833_ = v___x_843_;
goto v___jp_832_;
}
else
{
lean_dec_ref(v_env_828_);
v___y_833_ = v___x_842_;
goto v___jp_832_;
}
v___jp_832_:
{
if (v___y_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_834_, 0, v_thm_824_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_inc(v_all_831_);
lean_inc_ref(v_value_830_);
lean_inc_ref(v_toConstantVal_829_);
lean_dec_ref(v_thm_824_);
v___x_836_ = lean_box(0);
v___x_837_ = 0;
v___x_838_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_838_, 0, v_toConstantVal_829_);
lean_ctor_set(v___x_838_, 1, v_value_830_);
lean_ctor_set(v___x_838_, 2, v___x_836_);
lean_ctor_set(v___x_838_, 3, v_all_831_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*4, v___x_837_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_844_, v___y_845_);
lean_dec(v___y_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_848_, v___y_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_862_, lean_object* v_b_863_, lean_object* v_c_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
lean_inc(v___y_868_);
lean_inc_ref(v___y_867_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
v___x_870_ = lean_apply_7(v_k_862_, v_b_863_, v_c_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, lean_box(0));
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_871_, lean_object* v_b_872_, lean_object* v_c_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_871_, v_b_872_, v_c_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_880_, lean_object* v_k_881_, uint8_t v_cleanupAnnotations_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___f_888_; uint8_t v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_888_, 0, v_k_881_);
v___x_889_ = 1;
v___x_890_ = 0;
v___x_891_ = lean_box(0);
v___x_892_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_880_, v___x_889_, v___x_890_, v___x_889_, v___x_890_, v___x_891_, v___f_888_, v_cleanupAnnotations_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
v_a_901_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_892_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_892_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_909_, lean_object* v_k_910_, lean_object* v_cleanupAnnotations_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_917_; lean_object* v_res_918_; 
v_cleanupAnnotations_boxed_917_ = lean_unbox(v_cleanupAnnotations_911_);
v_res_918_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_909_, v_k_910_, v_cleanupAnnotations_boxed_917_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_919_, lean_object* v_e_920_, lean_object* v_k_921_, uint8_t v_cleanupAnnotations_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_920_, v_k_921_, v_cleanupAnnotations_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_929_, lean_object* v_e_930_, lean_object* v_k_931_, lean_object* v_cleanupAnnotations_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_938_; lean_object* v_res_939_; 
v_cleanupAnnotations_boxed_938_ = lean_unbox(v_cleanupAnnotations_932_);
v_res_939_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_929_, v_e_930_, v_k_931_, v_cleanupAnnotations_boxed_938_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
if (lean_obj_tag(v_a_940_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = l_List_reverse___redArg(v_a_941_);
return v___x_942_;
}
else
{
lean_object* v_head_943_; lean_object* v_tail_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_953_; 
v_head_943_ = lean_ctor_get(v_a_940_, 0);
v_tail_944_ = lean_ctor_get(v_a_940_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_a_940_);
if (v_isSharedCheck_953_ == 0)
{
v___x_946_ = v_a_940_;
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_tail_944_);
lean_inc(v_head_943_);
lean_dec(v_a_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = l_Lean_mkLevelParam(v_head_943_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v_a_941_);
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_a_941_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v_a_940_ = v_tail_944_;
v_a_941_ = v___x_950_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_954_, lean_object* v_name_955_, lean_object* v_xs_956_, lean_object* v_body_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_name_963_; lean_object* v_levelParams_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1034_; 
v_name_963_ = lean_ctor_get(v_toConstantVal_954_, 0);
v_levelParams_964_ = lean_ctor_get(v_toConstantVal_954_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_toConstantVal_954_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_toConstantVal_954_, 2);
lean_dec(v_unused_1035_);
v___x_966_ = v_toConstantVal_954_;
v_isShared_967_ = v_isSharedCheck_1034_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_levelParams_964_);
lean_inc(v_name_963_);
lean_dec(v_toConstantVal_954_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1034_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_lhs_971_; lean_object* v___x_972_; 
v___x_968_ = lean_box(0);
lean_inc(v_levelParams_964_);
v___x_969_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_964_, v___x_968_);
v___x_970_ = l_Lean_mkConst(v_name_963_, v___x_969_);
v_lhs_971_ = l_Lean_mkAppN(v___x_970_, v_xs_956_);
lean_inc_ref(v_lhs_971_);
v___x_972_ = l_Lean_Meta_mkEq(v_lhs_971_, v_body_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = 0;
v___x_975_ = 1;
v___x_976_ = 1;
v___x_977_ = l_Lean_Meta_mkForallFVars(v_xs_956_, v_a_973_, v___x_974_, v___x_975_, v___x_975_, v___x_976_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = l_Lean_Meta_letToHave(v_a_978_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = l_Lean_Meta_mkEqRefl(v_lhs_971_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
v___x_983_ = l_Lean_Meta_mkLambdaFVars(v_xs_956_, v_a_982_, v___x_974_, v___x_975_, v___x_974_, v___x_975_, v___x_976_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
lean_inc(v_name_955_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 2, v_a_980_);
lean_ctor_set(v___x_966_, 0, v_name_955_);
v___x_986_ = v___x_966_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_name_955_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_levelParams_964_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_a_980_);
v___x_986_ = v_reuseFailAlloc_993_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_991_; 
lean_inc(v_name_955_);
v___x_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_987_, 0, v_name_955_);
lean_ctor_set(v___x_987_, 1, v___x_968_);
v___x_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v_a_984_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
v___x_989_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_988_, v___y_961_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v___x_989_);
v___x_991_ = l_Lean_addDecl(v_a_990_, v___x_974_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v___x_992_; 
lean_dec_ref(v___x_991_);
v___x_992_ = l_Lean_inferDefEqAttr(v_name_955_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_992_;
}
else
{
lean_dec(v_name_955_);
return v___x_991_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_a_980_);
lean_del_object(v___x_966_);
lean_dec(v_levelParams_964_);
lean_dec(v_name_955_);
v_a_994_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_983_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_983_);
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
lean_dec(v_a_980_);
lean_del_object(v___x_966_);
lean_dec(v_levelParams_964_);
lean_dec(v_name_955_);
v_a_1002_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_981_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_981_);
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
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v_lhs_971_);
lean_del_object(v___x_966_);
lean_dec(v_levelParams_964_);
lean_dec(v_name_955_);
v_a_1010_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_979_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_979_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_lhs_971_);
lean_del_object(v___x_966_);
lean_dec(v_levelParams_964_);
lean_dec(v_name_955_);
v_a_1018_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_977_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_977_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_lhs_971_);
lean_del_object(v___x_966_);
lean_dec(v_levelParams_964_);
lean_dec(v_name_955_);
v_a_1026_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_972_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_972_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1036_, lean_object* v_name_1037_, lean_object* v_xs_1038_, lean_object* v_body_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1036_, v_name_1037_, v_xs_1038_, v_body_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec_ref(v_xs_1038_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1046_, lean_object* v_info_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_toConstantVal_1053_; lean_object* v_value_1054_; lean_object* v___f_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; 
v_toConstantVal_1053_ = lean_ctor_get(v_info_1047_, 0);
lean_inc_ref(v_toConstantVal_1053_);
v_value_1054_ = lean_ctor_get(v_info_1047_, 1);
lean_inc_ref(v_value_1054_);
lean_dec_ref(v_info_1047_);
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1055_, 0, v_toConstantVal_1053_);
lean_closure_set(v___f_1055_, 1, v_name_1046_);
v___x_1056_ = 1;
v___x_1057_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1054_, v___f_1055_, v___x_1056_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1058_, lean_object* v_info_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1058_, v_info_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1066_, lean_object* v_name_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1076_; lean_object* v_env_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = lean_st_ref_get(v_a_1071_);
v_env_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_ref(v_env_1077_);
lean_dec(v___x_1076_);
v___x_1078_ = 0;
lean_inc(v_declName_1066_);
v___x_1079_ = l_Lean_Environment_find_x3f(v_env_1077_, v_declName_1066_, v___x_1078_);
if (lean_obj_tag(v___x_1079_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1107_; 
v_val_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1107_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_val_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1107_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
if (lean_obj_tag(v_val_1080_) == 1)
{
lean_object* v_val_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_val_1084_ = lean_ctor_get(v_val_1080_, 0);
lean_inc_ref(v_val_1084_);
lean_dec_ref(v_val_1080_);
lean_inc_n(v_name_1067_, 2);
v___x_1085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1085_, 0, v_name_1067_);
lean_closure_set(v___x_1085_, 1, v_val_1084_);
lean_inc(v_declName_1066_);
v___x_1086_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1086_, 0, lean_box(0));
lean_closure_set(v___x_1086_, 1, v_declName_1066_);
lean_closure_set(v___x_1086_, 2, v___x_1085_);
v___x_1087_ = l_Lean_Meta_realizeConst(v_declName_1066_, v_name_1067_, v___x_1086_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1097_; 
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1098_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v_name_1067_);
v___x_1092_ = v___x_1082_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_name_1067_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
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
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_del_object(v___x_1082_);
lean_dec(v_name_1067_);
v_a_1099_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1087_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1087_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_del_object(v___x_1082_);
lean_dec(v_val_1080_);
lean_dec(v_name_1067_);
lean_dec(v_declName_1066_);
goto v___jp_1073_;
}
}
}
else
{
lean_dec(v___x_1079_);
lean_dec(v_name_1067_);
lean_dec(v_declName_1066_);
goto v___jp_1073_;
}
v___jp_1073_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1108_, lean_object* v_name_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1108_, v_name_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_i_1118_, lean_object* v_k_1119_){
_start:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_array_get_size(v_keys_1116_);
v___x_1121_ = lean_nat_dec_lt(v_i_1118_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec(v_i_1118_);
v___x_1122_ = lean_box(0);
return v___x_1122_;
}
else
{
lean_object* v_k_x27_1123_; uint8_t v___x_1124_; 
v_k_x27_1123_ = lean_array_fget_borrowed(v_keys_1116_, v_i_1118_);
v___x_1124_ = lean_name_eq(v_k_1119_, v_k_x27_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v_i_1118_, v___x_1125_);
lean_dec(v_i_1118_);
v_i_1118_ = v___x_1126_;
goto _start;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_array_fget_borrowed(v_vals_1117_, v_i_1118_);
lean_dec(v_i_1118_);
lean_inc(v___x_1128_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1130_, lean_object* v_vals_1131_, lean_object* v_i_1132_, lean_object* v_k_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1130_, v_vals_1131_, v_i_1132_, v_k_1133_);
lean_dec(v_k_1133_);
lean_dec_ref(v_vals_1131_);
lean_dec_ref(v_keys_1130_);
return v_res_1134_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; 
v___x_1135_ = ((size_t)5ULL);
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_shift_left(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; 
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_1140_ = lean_usize_sub(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1141_, size_t v_x_1142_, lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
lean_object* v_es_1144_; lean_object* v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; size_t v___x_1148_; lean_object* v_j_1149_; lean_object* v___x_1150_; 
v_es_1144_ = lean_ctor_get(v_x_1141_, 0);
v___x_1145_ = lean_box(2);
v___x_1146_ = ((size_t)5ULL);
v___x_1147_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1148_ = lean_usize_land(v_x_1142_, v___x_1147_);
v_j_1149_ = lean_usize_to_nat(v___x_1148_);
v___x_1150_ = lean_array_get_borrowed(v___x_1145_, v_es_1144_, v_j_1149_);
lean_dec(v_j_1149_);
switch(lean_obj_tag(v___x_1150_))
{
case 0:
{
lean_object* v_key_1151_; lean_object* v_val_1152_; uint8_t v___x_1153_; 
v_key_1151_ = lean_ctor_get(v___x_1150_, 0);
v_val_1152_ = lean_ctor_get(v___x_1150_, 1);
v___x_1153_ = lean_name_eq(v_x_1143_, v_key_1151_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
lean_inc(v_val_1152_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_val_1152_);
return v___x_1155_;
}
}
case 1:
{
lean_object* v_node_1156_; size_t v___x_1157_; 
v_node_1156_ = lean_ctor_get(v___x_1150_, 0);
v___x_1157_ = lean_usize_shift_right(v_x_1142_, v___x_1146_);
v_x_1141_ = v_node_1156_;
v_x_1142_ = v___x_1157_;
goto _start;
}
default: 
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
}
}
else
{
lean_object* v_ks_1160_; lean_object* v_vs_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_ks_1160_ = lean_ctor_get(v_x_1141_, 0);
v_vs_1161_ = lean_ctor_get(v_x_1141_, 1);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1160_, v_vs_1161_, v___x_1162_, v_x_1143_);
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
size_t v_x_356__boxed_1167_; lean_object* v_res_1168_; 
v_x_356__boxed_1167_ = lean_unbox_usize(v_x_1165_);
lean_dec(v_x_1165_);
v_res_1168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1164_, v_x_356__boxed_1167_, v_x_1166_);
lean_dec(v_x_1166_);
lean_dec_ref(v_x_1164_);
return v_res_1168_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1169_; uint64_t v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(1723u);
v___x_1170_ = lean_uint64_of_nat(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
uint64_t v___y_1174_; 
if (lean_obj_tag(v_x_1172_) == 0)
{
uint64_t v___x_1177_; 
v___x_1177_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1174_ = v___x_1177_;
goto v___jp_1173_;
}
else
{
uint64_t v_hash_1178_; 
v_hash_1178_ = lean_ctor_get_uint64(v_x_1172_, sizeof(void*)*2);
v___y_1174_ = v_hash_1178_;
goto v___jp_1173_;
}
v___jp_1173_:
{
size_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_uint64_to_usize(v___y_1174_);
v___x_1176_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1171_, v___x_1175_, v_x_1172_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1179_, v_x_1180_);
lean_dec(v_x_1180_);
lean_dec_ref(v_x_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v___x_1187_; lean_object* v_asyncMode_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1185_ = lean_st_ref_get(v_a_1183_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1187_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1188_ = lean_ctor_get(v___x_1187_, 2);
v___x_1189_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1190_ = lean_box(0);
v___x_1191_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1189_, v___x_1187_, v_env_1186_, v_asyncMode_1188_, v___x_1190_);
v___x_1192_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1191_, v_thmName_1182_);
lean_dec(v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec(v_thmName_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1198_, v_a_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_thmName_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1209_, v_x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1212_, lean_object* v_x_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1212_, v_x_1213_, v_x_1214_);
lean_dec(v_x_1214_);
lean_dec_ref(v_x_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1216_, lean_object* v_x_1217_, size_t v_x_1218_, lean_object* v_x_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1217_, v_x_1218_, v_x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
size_t v_x_461__boxed_1225_; lean_object* v_res_1226_; 
v_x_461__boxed_1225_ = lean_unbox_usize(v_x_1223_);
lean_dec(v_x_1223_);
v_res_1226_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1221_, v_x_1222_, v_x_461__boxed_1225_, v_x_1224_);
lean_dec(v_x_1224_);
lean_dec_ref(v_x_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1227_, lean_object* v_keys_1228_, lean_object* v_vals_1229_, lean_object* v_heq_1230_, lean_object* v_i_1231_, lean_object* v_k_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1228_, v_vals_1229_, v_i_1231_, v_k_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1234_, lean_object* v_keys_1235_, lean_object* v_vals_1236_, lean_object* v_heq_1237_, lean_object* v_i_1238_, lean_object* v_k_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1234_, v_keys_1235_, v_vals_1236_, v_heq_1237_, v_i_1238_, v_k_1239_);
lean_dec(v_k_1239_);
lean_dec_ref(v_vals_1236_);
lean_dec_ref(v_keys_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1241_, lean_object* v_i_1242_, lean_object* v_k_1243_){
_start:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_array_get_size(v_keys_1241_);
v___x_1245_ = lean_nat_dec_lt(v_i_1242_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_dec(v_i_1242_);
return v___x_1245_;
}
else
{
lean_object* v_k_x27_1246_; uint8_t v___x_1247_; 
v_k_x27_1246_ = lean_array_fget_borrowed(v_keys_1241_, v_i_1242_);
v___x_1247_ = lean_name_eq(v_k_1243_, v_k_x27_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_i_1242_, v___x_1248_);
lean_dec(v_i_1242_);
v_i_1242_ = v___x_1249_;
goto _start;
}
else
{
lean_dec(v_i_1242_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1251_, lean_object* v_i_1252_, lean_object* v_k_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1251_, v_i_1252_, v_k_1253_);
lean_dec(v_k_1253_);
lean_dec_ref(v_keys_1251_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1256_, size_t v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_object* v_es_1259_; lean_object* v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; lean_object* v_j_1264_; lean_object* v___x_1265_; 
v_es_1259_ = lean_ctor_get(v_x_1256_, 0);
v___x_1260_ = lean_box(2);
v___x_1261_ = ((size_t)5ULL);
v___x_1262_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1263_ = lean_usize_land(v_x_1257_, v___x_1262_);
v_j_1264_ = lean_usize_to_nat(v___x_1263_);
v___x_1265_ = lean_array_get_borrowed(v___x_1260_, v_es_1259_, v_j_1264_);
lean_dec(v_j_1264_);
switch(lean_obj_tag(v___x_1265_))
{
case 0:
{
lean_object* v_key_1266_; uint8_t v___x_1267_; 
v_key_1266_ = lean_ctor_get(v___x_1265_, 0);
v___x_1267_ = lean_name_eq(v_x_1258_, v_key_1266_);
return v___x_1267_;
}
case 1:
{
lean_object* v_node_1268_; size_t v___x_1269_; 
v_node_1268_ = lean_ctor_get(v___x_1265_, 0);
v___x_1269_ = lean_usize_shift_right(v_x_1257_, v___x_1261_);
v_x_1256_ = v_node_1268_;
v_x_1257_ = v___x_1269_;
goto _start;
}
default: 
{
uint8_t v___x_1271_; 
v___x_1271_ = 0;
return v___x_1271_;
}
}
}
else
{
lean_object* v_ks_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v_ks_1272_ = lean_ctor_get(v_x_1256_, 0);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1272_, v___x_1273_, v_x_1258_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
size_t v_x_336__boxed_1278_; uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_x_336__boxed_1278_ = lean_unbox_usize(v_x_1276_);
lean_dec(v_x_1276_);
v_res_1279_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1275_, v_x_336__boxed_1278_, v_x_1277_);
lean_dec(v_x_1277_);
lean_dec_ref(v_x_1275_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
uint64_t v___y_1284_; 
if (lean_obj_tag(v_x_1282_) == 0)
{
uint64_t v___x_1287_; 
v___x_1287_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1284_ = v___x_1287_;
goto v___jp_1283_;
}
else
{
uint64_t v_hash_1288_; 
v_hash_1288_ = lean_ctor_get_uint64(v_x_1282_, sizeof(void*)*2);
v___y_1284_ = v_hash_1288_;
goto v___jp_1283_;
}
v___jp_1283_:
{
size_t v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = lean_uint64_to_usize(v___y_1284_);
v___x_1286_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1281_, v___x_1285_, v_x_1282_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1289_, v_x_1290_);
lean_dec(v_x_1290_);
lean_dec_ref(v_x_1289_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v_env_1297_; lean_object* v___x_1298_; lean_object* v_asyncMode_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1296_ = lean_st_ref_get(v_a_1294_);
v_env_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref(v_env_1297_);
lean_dec(v___x_1296_);
v___x_1298_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1299_ = lean_ctor_get(v___x_1298_, 2);
v___x_1300_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1301_ = lean_box(0);
v___x_1302_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1300_, v___x_1298_, v_env_1297_, v_asyncMode_1299_, v___x_1301_);
v___x_1303_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1302_, v_thmName_1293_);
lean_dec(v___x_1302_);
v___x_1304_ = lean_box(v___x_1303_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec(v_thmName_1306_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1310_, v_a_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Meta_isEqnThm(v_thmName_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_thmName_1315_);
return v_res_1319_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1321_, v_x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1324_, v_x_1325_, v_x_1326_);
lean_dec(v_x_1326_);
lean_dec_ref(v_x_1325_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1329_, lean_object* v_x_1330_, size_t v_x_1331_, lean_object* v_x_1332_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1330_, v_x_1331_, v_x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
size_t v_x_430__boxed_1338_; uint8_t v_res_1339_; lean_object* v_r_1340_; 
v_x_430__boxed_1338_ = lean_unbox_usize(v_x_1336_);
lean_dec(v_x_1336_);
v_res_1339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1334_, v_x_1335_, v_x_430__boxed_1338_, v_x_1337_);
lean_dec(v_x_1337_);
lean_dec_ref(v_x_1335_);
v_r_1340_ = lean_box(v_res_1339_);
return v_r_1340_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1341_, lean_object* v_keys_1342_, lean_object* v_vals_1343_, lean_object* v_heq_1344_, lean_object* v_i_1345_, lean_object* v_k_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1342_, v_i_1345_, v_k_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1348_, lean_object* v_keys_1349_, lean_object* v_vals_1350_, lean_object* v_heq_1351_, lean_object* v_i_1352_, lean_object* v_k_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1348_, v_keys_1349_, v_vals_1350_, v_heq_1351_, v_i_1352_, v_k_1353_);
lean_dec(v_k_1353_);
lean_dec_ref(v_vals_1350_);
lean_dec_ref(v_keys_1349_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
lean_object* v_ks_1360_; lean_object* v_vs_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1385_; 
v_ks_1360_ = lean_ctor_get(v_x_1356_, 0);
v_vs_1361_ = lean_ctor_get(v_x_1356_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1356_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1363_ = v_x_1356_;
v_isShared_1364_ = v_isSharedCheck_1385_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_vs_1361_);
lean_inc(v_ks_1360_);
lean_dec(v_x_1356_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1385_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = lean_array_get_size(v_ks_1360_);
v___x_1366_ = lean_nat_dec_lt(v_x_1357_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_dec(v_x_1357_);
v___x_1367_ = lean_array_push(v_ks_1360_, v_x_1358_);
v___x_1368_ = lean_array_push(v_vs_1361_, v_x_1359_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1368_);
lean_ctor_set(v___x_1363_, 0, v___x_1367_);
v___x_1370_ = v___x_1363_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v_k_x27_1372_; uint8_t v___x_1373_; 
v_k_x27_1372_ = lean_array_fget_borrowed(v_ks_1360_, v_x_1357_);
v___x_1373_ = lean_name_eq(v_x_1358_, v_k_x27_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1375_; 
if (v_isShared_1364_ == 0)
{
v___x_1375_ = v___x_1363_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_ks_1360_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_vs_1361_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_x_1357_, v___x_1376_);
lean_dec(v_x_1357_);
v_x_1356_ = v___x_1375_;
v_x_1357_ = v___x_1377_;
goto _start;
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1380_ = lean_array_fset(v_ks_1360_, v_x_1357_, v_x_1358_);
v___x_1381_ = lean_array_fset(v_vs_1361_, v_x_1357_, v_x_1359_);
lean_dec(v_x_1357_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1381_);
lean_ctor_set(v___x_1363_, 0, v___x_1380_);
v___x_1383_ = v___x_1363_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1386_, lean_object* v_k_1387_, lean_object* v_v_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1386_, v___x_1389_, v_k_1387_, v_v_1388_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1392_, size_t v_x_1393_, size_t v_x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 0)
{
lean_object* v_es_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v_j_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_es_1397_ = lean_ctor_get(v_x_1392_, 0);
v___x_1398_ = ((size_t)5ULL);
v___x_1399_ = ((size_t)1ULL);
v___x_1400_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1401_ = lean_usize_land(v_x_1393_, v___x_1400_);
v_j_1402_ = lean_usize_to_nat(v___x_1401_);
v___x_1403_ = lean_array_get_size(v_es_1397_);
v___x_1404_ = lean_nat_dec_lt(v_j_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_dec(v_j_1402_);
lean_dec(v_x_1396_);
lean_dec(v_x_1395_);
return v_x_1392_;
}
else
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1441_; 
lean_inc_ref(v_es_1397_);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_x_1392_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_x_1392_, 0);
lean_dec(v_unused_1442_);
v___x_1406_ = v_x_1392_;
v_isShared_1407_ = v_isSharedCheck_1441_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_x_1392_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1441_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_v_1408_; lean_object* v___x_1409_; lean_object* v_xs_x27_1410_; lean_object* v___y_1412_; 
v_v_1408_ = lean_array_fget(v_es_1397_, v_j_1402_);
v___x_1409_ = lean_box(0);
v_xs_x27_1410_ = lean_array_fset(v_es_1397_, v_j_1402_, v___x_1409_);
switch(lean_obj_tag(v_v_1408_))
{
case 0:
{
lean_object* v_key_1417_; lean_object* v_val_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1428_; 
v_key_1417_ = lean_ctor_get(v_v_1408_, 0);
v_val_1418_ = lean_ctor_get(v_v_1408_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_v_1408_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1420_ = v_v_1408_;
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_val_1418_);
lean_inc(v_key_1417_);
lean_dec(v_v_1408_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_name_eq(v_x_1395_, v_key_1417_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_del_object(v___x_1420_);
v___x_1423_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1417_, v_val_1418_, v_x_1395_, v_x_1396_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
v___y_1412_ = v___x_1424_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_val_1418_);
lean_dec(v_key_1417_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_x_1396_);
lean_ctor_set(v___x_1420_, 0, v_x_1395_);
v___x_1426_ = v___x_1420_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_x_1395_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_x_1396_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
v___y_1412_ = v___x_1426_;
goto v___jp_1411_;
}
}
}
}
case 1:
{
lean_object* v_node_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1439_; 
v_node_1429_ = lean_ctor_get(v_v_1408_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_v_1408_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1431_ = v_v_1408_;
v_isShared_1432_ = v_isSharedCheck_1439_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_node_1429_);
lean_dec(v_v_1408_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1439_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1433_ = lean_usize_shift_right(v_x_1393_, v___x_1398_);
v___x_1434_ = lean_usize_add(v_x_1394_, v___x_1399_);
v___x_1435_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1429_, v___x_1433_, v___x_1434_, v_x_1395_, v_x_1396_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1435_);
v___x_1437_ = v___x_1431_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
v___y_1412_ = v___x_1437_;
goto v___jp_1411_;
}
}
}
default: 
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_x_1395_);
lean_ctor_set(v___x_1440_, 1, v_x_1396_);
v___y_1412_ = v___x_1440_;
goto v___jp_1411_;
}
}
v___jp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = lean_array_fset(v_xs_x27_1410_, v_j_1402_, v___y_1412_);
lean_dec(v_j_1402_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1413_);
v___x_1415_ = v___x_1406_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
else
{
lean_object* v_ks_1443_; lean_object* v_vs_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1464_; 
v_ks_1443_ = lean_ctor_get(v_x_1392_, 0);
v_vs_1444_ = lean_ctor_get(v_x_1392_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_x_1392_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1446_ = v_x_1392_;
v_isShared_1447_ = v_isSharedCheck_1464_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_vs_1444_);
lean_inc(v_ks_1443_);
lean_dec(v_x_1392_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1464_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_ks_1443_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_vs_1444_);
v___x_1449_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v_newNode_1450_; uint8_t v___y_1452_; size_t v___x_1458_; uint8_t v___x_1459_; 
v_newNode_1450_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1449_, v_x_1395_, v_x_1396_);
v___x_1458_ = ((size_t)7ULL);
v___x_1459_ = lean_usize_dec_le(v___x_1458_, v_x_1394_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1450_);
v___x_1461_ = lean_unsigned_to_nat(4u);
v___x_1462_ = lean_nat_dec_lt(v___x_1460_, v___x_1461_);
lean_dec(v___x_1460_);
v___y_1452_ = v___x_1462_;
goto v___jp_1451_;
}
else
{
v___y_1452_ = v___x_1459_;
goto v___jp_1451_;
}
v___jp_1451_:
{
if (v___y_1452_ == 0)
{
lean_object* v_ks_1453_; lean_object* v_vs_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_ks_1453_ = lean_ctor_get(v_newNode_1450_, 0);
lean_inc_ref(v_ks_1453_);
v_vs_1454_ = lean_ctor_get(v_newNode_1450_, 1);
lean_inc_ref(v_vs_1454_);
lean_dec_ref(v_newNode_1450_);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1457_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1394_, v_ks_1453_, v_vs_1454_, v___x_1455_, v___x_1456_);
lean_dec_ref(v_vs_1454_);
lean_dec_ref(v_ks_1453_);
return v___x_1457_;
}
else
{
return v_newNode_1450_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1465_, lean_object* v_keys_1466_, lean_object* v_vals_1467_, lean_object* v_i_1468_, lean_object* v_entries_1469_){
_start:
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_array_get_size(v_keys_1466_);
v___x_1471_ = lean_nat_dec_lt(v_i_1468_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_dec(v_i_1468_);
return v_entries_1469_;
}
else
{
lean_object* v_k_1472_; lean_object* v_v_1473_; uint64_t v___y_1475_; 
v_k_1472_ = lean_array_fget_borrowed(v_keys_1466_, v_i_1468_);
v_v_1473_ = lean_array_fget_borrowed(v_vals_1467_, v_i_1468_);
if (lean_obj_tag(v_k_1472_) == 0)
{
uint64_t v___x_1486_; 
v___x_1486_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1475_ = v___x_1486_;
goto v___jp_1474_;
}
else
{
uint64_t v_hash_1487_; 
v_hash_1487_ = lean_ctor_get_uint64(v_k_1472_, sizeof(void*)*2);
v___y_1475_ = v_hash_1487_;
goto v___jp_1474_;
}
v___jp_1474_:
{
size_t v_h_1476_; size_t v___x_1477_; lean_object* v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v_h_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_h_1476_ = lean_uint64_to_usize(v___y_1475_);
v___x_1477_ = ((size_t)5ULL);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_sub(v_depth_1465_, v___x_1479_);
v___x_1481_ = lean_usize_mul(v___x_1477_, v___x_1480_);
v_h_1482_ = lean_usize_shift_right(v_h_1476_, v___x_1481_);
v___x_1483_ = lean_nat_add(v_i_1468_, v___x_1478_);
lean_dec(v_i_1468_);
lean_inc(v_v_1473_);
lean_inc(v_k_1472_);
v___x_1484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1469_, v_h_1482_, v_depth_1465_, v_k_1472_, v_v_1473_);
v_i_1468_ = v___x_1483_;
v_entries_1469_ = v___x_1484_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1488_, lean_object* v_keys_1489_, lean_object* v_vals_1490_, lean_object* v_i_1491_, lean_object* v_entries_1492_){
_start:
{
size_t v_depth_boxed_1493_; lean_object* v_res_1494_; 
v_depth_boxed_1493_ = lean_unbox_usize(v_depth_1488_);
lean_dec(v_depth_1488_);
v_res_1494_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1493_, v_keys_1489_, v_vals_1490_, v_i_1491_, v_entries_1492_);
lean_dec_ref(v_vals_1490_);
lean_dec_ref(v_keys_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
size_t v_x_636__boxed_1500_; size_t v_x_637__boxed_1501_; lean_object* v_res_1502_; 
v_x_636__boxed_1500_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_x_637__boxed_1501_ = lean_unbox_usize(v_x_1497_);
lean_dec(v_x_1497_);
v_res_1502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1495_, v_x_636__boxed_1500_, v_x_637__boxed_1501_, v_x_1498_, v_x_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
uint64_t v___y_1507_; 
if (lean_obj_tag(v_x_1504_) == 0)
{
uint64_t v___x_1511_; 
v___x_1511_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1507_ = v___x_1511_;
goto v___jp_1506_;
}
else
{
uint64_t v_hash_1512_; 
v_hash_1512_ = lean_ctor_get_uint64(v_x_1504_, sizeof(void*)*2);
v___y_1507_ = v_hash_1512_;
goto v___jp_1506_;
}
v___jp_1506_:
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_uint64_to_usize(v___y_1507_);
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1503_, v___x_1508_, v___x_1509_, v_x_1504_, v_x_1505_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1513_, lean_object* v_as_1514_, size_t v_i_1515_, size_t v_stop_1516_, lean_object* v_b_1517_){
_start:
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_usize_dec_eq(v_i_1515_, v_stop_1516_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; size_t v___x_1521_; size_t v___x_1522_; 
v___x_1519_ = lean_array_uget_borrowed(v_as_1514_, v_i_1515_);
lean_inc(v_declName_1513_);
lean_inc(v___x_1519_);
v___x_1520_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1517_, v___x_1519_, v_declName_1513_);
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1515_, v___x_1521_);
v_i_1515_ = v___x_1522_;
v_b_1517_ = v___x_1520_;
goto _start;
}
else
{
lean_dec(v_declName_1513_);
return v_b_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1524_, lean_object* v_as_1525_, lean_object* v_i_1526_, lean_object* v_stop_1527_, lean_object* v_b_1528_){
_start:
{
size_t v_i_boxed_1529_; size_t v_stop_boxed_1530_; lean_object* v_res_1531_; 
v_i_boxed_1529_ = lean_unbox_usize(v_i_1526_);
lean_dec(v_i_1526_);
v_stop_boxed_1530_ = lean_unbox_usize(v_stop_1527_);
lean_dec(v_stop_1527_);
v_res_1531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1524_, v_as_1525_, v_i_boxed_1529_, v_stop_boxed_1530_, v_b_1528_);
lean_dec_ref(v_as_1525_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1532_, lean_object* v_declName_1533_, lean_object* v_s_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_array_get_size(v_eqThms_1532_);
v___x_1537_ = lean_nat_dec_lt(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_dec(v_declName_1533_);
return v_s_1534_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_nat_dec_le(v___x_1536_, v___x_1536_);
if (v___x_1538_ == 0)
{
if (v___x_1537_ == 0)
{
lean_dec(v_declName_1533_);
return v_s_1534_;
}
else
{
size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = ((size_t)0ULL);
v___x_1540_ = lean_usize_of_nat(v___x_1536_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1533_, v_eqThms_1532_, v___x_1539_, v___x_1540_, v_s_1534_);
return v___x_1541_;
}
}
else
{
size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = lean_usize_of_nat(v___x_1536_);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1533_, v_eqThms_1532_, v___x_1542_, v___x_1543_, v_s_1534_);
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1545_, lean_object* v_declName_1546_, lean_object* v_s_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1545_, v_declName_1546_, v_s_1547_);
lean_dec_ref(v_eqThms_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1549_, lean_object* v_eqThms_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v_env_1554_; lean_object* v_nextMacroScope_1555_; lean_object* v_ngen_1556_; lean_object* v_auxDeclNGen_1557_; lean_object* v_traceState_1558_; lean_object* v_messages_1559_; lean_object* v_infoState_1560_; lean_object* v_snapshotTasks_1561_; lean_object* v_newDecls_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1578_; 
v___x_1553_ = lean_st_ref_take(v_a_1551_);
v_env_1554_ = lean_ctor_get(v___x_1553_, 0);
v_nextMacroScope_1555_ = lean_ctor_get(v___x_1553_, 1);
v_ngen_1556_ = lean_ctor_get(v___x_1553_, 2);
v_auxDeclNGen_1557_ = lean_ctor_get(v___x_1553_, 3);
v_traceState_1558_ = lean_ctor_get(v___x_1553_, 4);
v_messages_1559_ = lean_ctor_get(v___x_1553_, 6);
v_infoState_1560_ = lean_ctor_get(v___x_1553_, 7);
v_snapshotTasks_1561_ = lean_ctor_get(v___x_1553_, 8);
v_newDecls_1562_ = lean_ctor_get(v___x_1553_, 9);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v___x_1553_, 5);
lean_dec(v_unused_1579_);
v___x_1564_ = v___x_1553_;
v_isShared_1565_ = v_isSharedCheck_1578_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_newDecls_1562_);
lean_inc(v_snapshotTasks_1561_);
lean_inc(v_infoState_1560_);
lean_inc(v_messages_1559_);
lean_inc(v_traceState_1558_);
lean_inc(v_auxDeclNGen_1557_);
lean_inc(v_ngen_1556_);
lean_inc(v_nextMacroScope_1555_);
lean_inc(v_env_1554_);
lean_dec(v___x_1553_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1578_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v_asyncMode_1567_; lean_object* v___f_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1566_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1567_ = lean_ctor_get(v___x_1566_, 2);
v___f_1568_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1568_, 0, v_eqThms_1550_);
lean_closure_set(v___f_1568_, 1, v_declName_1549_);
v___x_1569_ = lean_box(0);
v___x_1570_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1566_, v_env_1554_, v___f_1568_, v_asyncMode_1567_, v___x_1569_);
v___x_1571_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 5, v___x_1571_);
lean_ctor_set(v___x_1564_, 0, v___x_1570_);
v___x_1573_ = v___x_1564_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_nextMacroScope_1555_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_ngen_1556_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_auxDeclNGen_1557_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v_traceState_1558_);
lean_ctor_set(v_reuseFailAlloc_1577_, 5, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1577_, 6, v_messages_1559_);
lean_ctor_set(v_reuseFailAlloc_1577_, 7, v_infoState_1560_);
lean_ctor_set(v_reuseFailAlloc_1577_, 8, v_snapshotTasks_1561_);
lean_ctor_set(v_reuseFailAlloc_1577_, 9, v_newDecls_1562_);
v___x_1573_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_st_ref_set(v_a_1551_, v___x_1573_);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1580_, lean_object* v_eqThms_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1580_, v_eqThms_1581_, v_a_1582_);
lean_dec(v_a_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1585_, lean_object* v_eqThms_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1585_, v_eqThms_1586_, v_a_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1591_, lean_object* v_eqThms_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1591_, v_eqThms_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1597_, lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1598_, v_x_1599_, v_x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1602_, lean_object* v_x_1603_, size_t v_x_1604_, size_t v_x_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1603_, v_x_1604_, v_x_1605_, v_x_1606_, v_x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
size_t v_x_905__boxed_1615_; size_t v_x_906__boxed_1616_; lean_object* v_res_1617_; 
v_x_905__boxed_1615_ = lean_unbox_usize(v_x_1611_);
lean_dec(v_x_1611_);
v_x_906__boxed_1616_ = lean_unbox_usize(v_x_1612_);
lean_dec(v_x_1612_);
v_res_1617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1609_, v_x_1610_, v_x_905__boxed_1615_, v_x_906__boxed_1616_, v_x_1613_, v_x_1614_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1618_, lean_object* v_n_1619_, lean_object* v_k_1620_, lean_object* v_v_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1619_, v_k_1620_, v_v_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1623_, size_t v_depth_1624_, lean_object* v_keys_1625_, lean_object* v_vals_1626_, lean_object* v_heq_1627_, lean_object* v_i_1628_, lean_object* v_entries_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1624_, v_keys_1625_, v_vals_1626_, v_i_1628_, v_entries_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1631_, lean_object* v_depth_1632_, lean_object* v_keys_1633_, lean_object* v_vals_1634_, lean_object* v_heq_1635_, lean_object* v_i_1636_, lean_object* v_entries_1637_){
_start:
{
size_t v_depth_boxed_1638_; lean_object* v_res_1639_; 
v_depth_boxed_1638_ = lean_unbox_usize(v_depth_1632_);
lean_dec(v_depth_1632_);
v_res_1639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1631_, v_depth_boxed_1638_, v_keys_1633_, v_vals_1634_, v_heq_1635_, v_i_1636_, v_entries_1637_);
lean_dec_ref(v_vals_1634_);
lean_dec_ref(v_keys_1633_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1641_, v_x_1642_, v_x_1643_, v_x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1646_, lean_object* v_env_1647_, lean_object* v_idx_1648_, lean_object* v_eqs_1649_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_nextEq_1656_; uint8_t v___x_1657_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = lean_nat_add(v_idx_1648_, v___x_1652_);
lean_dec(v_idx_1648_);
lean_inc(v___x_1653_);
v___x_1654_ = l_Nat_reprFast(v___x_1653_);
v___x_1655_ = lean_string_append(v___x_1651_, v___x_1654_);
lean_dec_ref(v___x_1654_);
lean_inc(v_declName_1646_);
lean_inc_ref(v_env_1647_);
v_nextEq_1656_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1647_, v_declName_1646_, v___x_1655_);
v___x_1657_ = l_Lean_Environment_containsOnBranch(v_env_1647_, v_nextEq_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec(v_nextEq_1656_);
lean_dec(v___x_1653_);
lean_dec_ref(v_env_1647_);
lean_dec(v_declName_1646_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_eqs_1649_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_array_push(v_eqs_1649_, v_nextEq_1656_);
v_idx_1648_ = v___x_1653_;
v_eqs_1649_ = v___x_1659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1661_, lean_object* v_env_1662_, lean_object* v_idx_1663_, lean_object* v_eqs_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1661_, v_env_1662_, v_idx_1663_, v_eqs_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1667_, lean_object* v_env_1668_, lean_object* v_idx_1669_, lean_object* v_eqs_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1667_, v_env_1668_, v_idx_1669_, v_eqs_1670_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1677_, lean_object* v_env_1678_, lean_object* v_idx_1679_, lean_object* v_eqs_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1677_, v_env_1678_, v_idx_1679_, v_eqs_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v_env_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; uint8_t v___x_1695_; 
v___x_1690_ = lean_st_ref_get(v_a_1688_);
v_env_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc_ref_n(v_env_1691_, 3);
lean_dec(v___x_1690_);
v___x_1692_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1687_);
v___x_1693_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1691_, v_declName_1687_, v___x_1692_);
v___x_1694_ = 1;
lean_inc(v___x_1693_);
v___x_1695_ = l_Lean_Environment_contains(v_env_1691_, v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v___x_1693_);
lean_dec_ref(v_env_1691_);
lean_dec(v_declName_1687_);
v___x_1696_ = lean_box(0);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_unsigned_to_nat(1u);
v___x_1699_ = lean_mk_empty_array_with_capacity(v___x_1698_);
v___x_1700_ = lean_array_push(v___x_1699_, v___x_1693_);
lean_inc(v_declName_1687_);
v___x_1701_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1687_, v_env_1691_, v___x_1698_, v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1711_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc_n(v_a_1702_, 2);
lean_dec_ref(v___x_1701_);
v___x_1703_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1687_, v_a_1702_, v_a_1688_);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v___x_1703_, 0);
lean_dec(v_unused_1712_);
v___x_1705_ = v___x_1703_;
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v___x_1703_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1702_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1707_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_declName_1687_);
v_a_1713_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1701_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1701_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1721_, v_a_1722_);
lean_dec(v_a_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1725_, v_a_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1739_, lean_object* v_localInsts_1740_, lean_object* v_x_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1739_, v_localInsts_1740_, v_x_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
v_a_1756_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1747_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1747_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1764_, lean_object* v_localInsts_1765_, lean_object* v_x_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1764_, v_localInsts_1765_, v_x_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1773_, lean_object* v_lctx_1774_, lean_object* v_localInsts_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1774_, v_localInsts_1775_, v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1783_, lean_object* v_lctx_1784_, lean_object* v_localInsts_1785_, lean_object* v_x_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1783_, v_lctx_1784_, v_localInsts_1785_, v_x_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1796_, lean_object* v_as_x27_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
if (lean_obj_tag(v_as_x27_1797_) == 0)
{
lean_object* v___x_1804_; 
lean_dec(v_declName_1796_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_b_1798_);
return v___x_1804_;
}
else
{
lean_object* v_head_1805_; lean_object* v_tail_1806_; lean_object* v___x_1807_; 
lean_dec_ref(v_b_1798_);
v_head_1805_ = lean_ctor_get(v_as_x27_1797_, 0);
v_tail_1806_ = lean_ctor_get(v_as_x27_1797_, 1);
lean_inc(v_head_1805_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1801_);
lean_inc(v___y_1800_);
lean_inc_ref(v___y_1799_);
lean_inc(v_declName_1796_);
v___x_1807_ = lean_apply_6(v_head_1805_, v_declName_1796_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, lean_box(0));
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = lean_box(0);
if (lean_obj_tag(v_a_1808_) == 1)
{
lean_object* v_val_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1820_; 
v_val_1810_ = lean_ctor_get(v_a_1808_, 0);
lean_inc(v_val_1810_);
v___x_1811_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1796_, v_val_1810_, v___y_1802_);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1811_, 0);
lean_dec(v_unused_1821_);
v___x_1813_ = v___x_1811_;
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
else
{
lean_dec(v___x_1811_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_a_1808_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v___x_1809_);
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
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_a_1808_);
v___x_1822_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1797_ = v_tail_1806_;
v_b_1798_ = v___x_1822_;
goto _start;
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_declName_1796_);
v_a_1824_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1807_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1807_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1832_, lean_object* v_as_x27_1833_, lean_object* v_b_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1832_, v_as_x27_1833_, v_b_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_as_x27_1833_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
lean_inc(v_declName_1841_);
v___x_1847_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1885_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1885_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1885_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_unbox(v_a_1848_);
lean_dec(v_a_1848_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec(v_declName_1841_);
v___x_1853_ = lean_box(0);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1853_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
else
{
lean_object* v___x_1857_; 
lean_del_object(v___x_1850_);
lean_inc(v_declName_1841_);
v___x_1857_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1841_, v___y_1845_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
if (lean_obj_tag(v_a_1858_) == 1)
{
lean_dec_ref(v_a_1858_);
lean_dec(v_declName_1841_);
return v___x_1857_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v_a_1858_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1860_ = lean_st_ref_get(v___x_1859_);
v___x_1861_ = lean_box(0);
v___x_1862_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1863_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1841_, v___x_1860_, v___x_1862_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___x_1860_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1876_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1876_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1876_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v_fst_1868_; 
v_fst_1868_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_fst_1868_);
lean_dec(v_a_1864_);
if (lean_obj_tag(v_fst_1868_) == 0)
{
lean_object* v___x_1870_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1861_);
v___x_1870_ = v___x_1866_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1861_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
else
{
lean_object* v_val_1872_; lean_object* v___x_1874_; 
v_val_1872_ = lean_ctor_get(v_fst_1868_, 0);
lean_inc(v_val_1872_);
lean_dec_ref(v_fst_1868_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v_val_1872_);
v___x_1874_ = v___x_1866_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_val_1872_);
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
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1863_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1863_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_dec(v_declName_1841_);
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_declName_1841_);
v_a_1886_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1847_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1847_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1901_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = lean_box(1);
v___x_1905_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1906_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1905_);
lean_ctor_set(v___x_1907_, 2, v___x_1904_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___f_1916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1916_, 0, v_declName_1910_);
v___x_1917_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1918_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1919_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1917_, v___x_1918_, v___f_1916_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1927_, lean_object* v_as_1928_, lean_object* v_as_x27_1929_, lean_object* v_b_1930_, lean_object* v_a_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1927_, v_as_x27_1929_, v_b_1930_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1938_, lean_object* v_as_1939_, lean_object* v_as_x27_1940_, lean_object* v_b_1941_, lean_object* v_a_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1938_, v_as_1939_, v_as_x27_1940_, v_b_1941_, v_a_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v_as_x27_1940_);
lean_dec(v_as_1939_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1955_ = lean_unsigned_to_nat(32u);
v___x_1956_ = lean_mk_empty_array_with_capacity(v___x_1955_);
lean_dec_ref(v___x_1956_);
v___x_1957_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1958_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1949_);
v___x_1959_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1959_, 0, v_declName_1949_);
v___x_1960_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1960_, 0, lean_box(0));
lean_closure_set(v___x_1960_, 1, v_declName_1949_);
lean_closure_set(v___x_1960_, 2, v___x_1959_);
v___x_1961_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1957_, v___x_1958_, v___x_1960_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v_env_1976_; lean_object* v___x_1977_; lean_object* v_mctx_1978_; lean_object* v_lctx_1979_; lean_object* v_options_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1975_ = lean_st_ref_get(v___y_1973_);
v_env_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_ref(v_env_1976_);
lean_dec(v___x_1975_);
v___x_1977_ = lean_st_ref_get(v___y_1971_);
v_mctx_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc_ref(v_mctx_1978_);
lean_dec(v___x_1977_);
v_lctx_1979_ = lean_ctor_get(v___y_1970_, 2);
v_options_1980_ = lean_ctor_get(v___y_1972_, 2);
lean_inc_ref(v_options_1980_);
lean_inc_ref(v_lctx_1979_);
v___x_1981_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1981_, 0, v_env_1976_);
lean_ctor_set(v___x_1981_, 1, v_mctx_1978_);
lean_ctor_set(v___x_1981_, 2, v_lctx_1979_);
lean_ctor_set(v___x_1981_, 3, v_options_1980_);
v___x_1982_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_msgData_1969_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1990_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1991_; double v___x_1992_; 
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_float_of_nat(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1996_, lean_object* v_msg_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_ref_2003_; lean_object* v___x_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2050_; 
v_ref_2003_ = lean_ctor_get(v___y_2000_, 5);
v___x_2004_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2050_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2050_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v_traceState_2010_; lean_object* v_env_2011_; lean_object* v_nextMacroScope_2012_; lean_object* v_ngen_2013_; lean_object* v_auxDeclNGen_2014_; lean_object* v_cache_2015_; lean_object* v_messages_2016_; lean_object* v_infoState_2017_; lean_object* v_snapshotTasks_2018_; lean_object* v_newDecls_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2049_; 
v___x_2009_ = lean_st_ref_take(v___y_2001_);
v_traceState_2010_ = lean_ctor_get(v___x_2009_, 4);
v_env_2011_ = lean_ctor_get(v___x_2009_, 0);
v_nextMacroScope_2012_ = lean_ctor_get(v___x_2009_, 1);
v_ngen_2013_ = lean_ctor_get(v___x_2009_, 2);
v_auxDeclNGen_2014_ = lean_ctor_get(v___x_2009_, 3);
v_cache_2015_ = lean_ctor_get(v___x_2009_, 5);
v_messages_2016_ = lean_ctor_get(v___x_2009_, 6);
v_infoState_2017_ = lean_ctor_get(v___x_2009_, 7);
v_snapshotTasks_2018_ = lean_ctor_get(v___x_2009_, 8);
v_newDecls_2019_ = lean_ctor_get(v___x_2009_, 9);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2021_ = v___x_2009_;
v_isShared_2022_ = v_isSharedCheck_2049_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_newDecls_2019_);
lean_inc(v_snapshotTasks_2018_);
lean_inc(v_infoState_2017_);
lean_inc(v_messages_2016_);
lean_inc(v_cache_2015_);
lean_inc(v_traceState_2010_);
lean_inc(v_auxDeclNGen_2014_);
lean_inc(v_ngen_2013_);
lean_inc(v_nextMacroScope_2012_);
lean_inc(v_env_2011_);
lean_dec(v___x_2009_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2049_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
uint64_t v_tid_2023_; lean_object* v_traces_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2048_; 
v_tid_2023_ = lean_ctor_get_uint64(v_traceState_2010_, sizeof(void*)*1);
v_traces_2024_ = lean_ctor_get(v_traceState_2010_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_traceState_2010_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2026_ = v_traceState_2010_;
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_traces_2024_);
lean_dec(v_traceState_2010_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; double v___x_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_2030_ = 0;
v___x_2031_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_2032_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2032_, 0, v_cls_1996_);
lean_ctor_set(v___x_2032_, 1, v___x_2028_);
lean_ctor_set(v___x_2032_, 2, v___x_2031_);
lean_ctor_set_float(v___x_2032_, sizeof(void*)*3, v___x_2029_);
lean_ctor_set_float(v___x_2032_, sizeof(void*)*3 + 8, v___x_2029_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*3 + 16, v___x_2030_);
v___x_2033_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_2034_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v_a_2005_);
lean_ctor_set(v___x_2034_, 2, v___x_2033_);
lean_inc(v_ref_2003_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_ref_2003_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_PersistentArray_push___redArg(v_traces_2024_, v___x_2035_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2036_);
v___x_2038_ = v___x_2026_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2036_);
lean_ctor_set_uint64(v_reuseFailAlloc_2047_, sizeof(void*)*1, v_tid_2023_);
v___x_2038_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v___x_2038_);
v___x_2040_ = v___x_2021_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_env_2011_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_nextMacroScope_2012_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_ngen_2013_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_auxDeclNGen_2014_);
lean_ctor_set(v_reuseFailAlloc_2046_, 4, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2046_, 5, v_cache_2015_);
lean_ctor_set(v_reuseFailAlloc_2046_, 6, v_messages_2016_);
lean_ctor_set(v_reuseFailAlloc_2046_, 7, v_infoState_2017_);
lean_ctor_set(v_reuseFailAlloc_2046_, 8, v_snapshotTasks_2018_);
lean_ctor_set(v_reuseFailAlloc_2046_, 9, v_newDecls_2019_);
v___x_2040_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = lean_st_ref_set(v___y_2001_, v___x_2040_);
v___x_2042_ = lean_box(0);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2042_);
v___x_2044_ = v___x_2007_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2051_, lean_object* v_msg_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2051_, v_msg_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2059_, lean_object* v_as_2060_, size_t v_sz_2061_, size_t v_i_2062_, lean_object* v_b_2063_){
_start:
{
lean_object* v_a_2066_; uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_lt(v_i_2062_, v_sz_2061_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_b_2063_);
return v___x_2071_;
}
else
{
lean_object* v_a_2072_; lean_object* v_defValue_2073_; uint8_t v___x_2074_; uint8_t v___y_2076_; 
v_a_2072_ = lean_array_uget(v_as_2060_, v_i_2062_);
v_defValue_2073_ = lean_ctor_get(v_a_2072_, 1);
v___x_2074_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2059_, v_a_2072_);
if (v___x_2074_ == 0)
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_unbox(v_defValue_2073_);
if (v___x_2088_ == 0)
{
v___y_2076_ = v___x_2070_;
goto v___jp_2075_;
}
else
{
v___y_2076_ = v___x_2074_;
goto v___jp_2075_;
}
}
else
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_unbox(v_defValue_2073_);
v___y_2076_ = v___x_2089_;
goto v___jp_2075_;
}
v___jp_2075_:
{
if (v___y_2076_ == 0)
{
lean_object* v_name_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2086_; 
v_name_2077_ = lean_ctor_get(v_a_2072_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2072_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v_a_2072_, 1);
lean_dec(v_unused_2087_);
v___x_2079_ = v_a_2072_;
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_name_2077_);
lean_dec(v_a_2072_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2081_, 0, v___x_2074_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2081_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_name_2077_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_array_push(v_b_2063_, v___x_2083_);
v_a_2066_ = v___x_2084_;
goto v___jp_2065_;
}
}
}
else
{
lean_dec(v_a_2072_);
v_a_2066_ = v_b_2063_;
goto v___jp_2065_;
}
}
}
v___jp_2065_:
{
size_t v___x_2067_; size_t v___x_2068_; 
v___x_2067_ = ((size_t)1ULL);
v___x_2068_ = lean_usize_add(v_i_2062_, v___x_2067_);
v_i_2062_ = v___x_2068_;
v_b_2063_ = v_a_2066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2090_, lean_object* v_as_2091_, lean_object* v_sz_2092_, lean_object* v_i_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_){
_start:
{
size_t v_sz_boxed_2096_; size_t v_i_boxed_2097_; lean_object* v_res_2098_; 
v_sz_boxed_2096_ = lean_unbox_usize(v_sz_2092_);
lean_dec(v_sz_2092_);
v_i_boxed_2097_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2090_, v_as_2091_, v_sz_boxed_2096_, v_i_boxed_2097_, v_b_2094_);
lean_dec_ref(v_as_2091_);
lean_dec_ref(v___x_2090_);
return v_res_2098_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2101_; size_t v_sz_2102_; 
v___x_2101_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2102_ = lean_array_size(v___x_2101_);
return v_sz_2102_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2104_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
lean_ctor_set(v___x_2104_, 2, v___x_2103_);
lean_ctor_set(v___x_2104_, 3, v___x_2103_);
lean_ctor_set(v___x_2104_, 4, v___x_2103_);
lean_ctor_set(v___x_2104_, 5, v___x_2103_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2113_ = l_Lean_Name_append(v___x_2112_, v___x_2111_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_options_2123_; lean_object* v_inheritedTraceOptions_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; size_t v_sz_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
v_options_2123_ = lean_ctor_get(v_a_2120_, 2);
v_inheritedTraceOptions_2124_ = lean_ctor_get(v_a_2120_, 13);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2127_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2128_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2129_ = ((size_t)0ULL);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2123_, v___x_2127_, v_sz_2128_, v___x_2129_, v___x_2126_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2191_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2191_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2191_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_array_get_size(v_a_2131_);
v___x_2180_ = lean_nat_dec_eq(v___x_2179_, v___x_2125_);
if (v___x_2180_ == 0)
{
uint8_t v_hasTrace_2181_; 
v_hasTrace_2181_ = lean_ctor_get_uint8(v_options_2123_, sizeof(void*)*1);
if (v_hasTrace_2181_ == 0)
{
v___y_2136_ = v_a_2119_;
v___y_2137_ = v_a_2121_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2182_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2183_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2124_, v_options_2123_, v___x_2183_);
if (v___x_2184_ == 0)
{
v___y_2136_ = v_a_2119_;
v___y_2137_ = v_a_2121_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2185_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2117_);
v___x_2186_ = l_Lean_MessageData_ofName(v_declName_2117_);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2182_, v___x_2187_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_dec_ref(v___x_2188_);
v___y_2136_ = v_a_2119_;
v___y_2137_ = v_a_2121_;
goto v___jp_2135_;
}
else
{
lean_del_object(v___x_2133_);
lean_dec(v_a_2131_);
lean_dec(v_declName_2117_);
return v___x_2188_;
}
}
}
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_del_object(v___x_2133_);
lean_dec(v_a_2131_);
lean_dec(v_declName_2117_);
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
v___jp_2135_:
{
lean_object* v___x_2138_; lean_object* v_env_2139_; lean_object* v_nextMacroScope_2140_; lean_object* v_ngen_2141_; lean_object* v_auxDeclNGen_2142_; lean_object* v_traceState_2143_; lean_object* v_messages_2144_; lean_object* v_infoState_2145_; lean_object* v_snapshotTasks_2146_; lean_object* v_newDecls_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2177_; 
v___x_2138_ = lean_st_ref_take(v___y_2137_);
v_env_2139_ = lean_ctor_get(v___x_2138_, 0);
v_nextMacroScope_2140_ = lean_ctor_get(v___x_2138_, 1);
v_ngen_2141_ = lean_ctor_get(v___x_2138_, 2);
v_auxDeclNGen_2142_ = lean_ctor_get(v___x_2138_, 3);
v_traceState_2143_ = lean_ctor_get(v___x_2138_, 4);
v_messages_2144_ = lean_ctor_get(v___x_2138_, 6);
v_infoState_2145_ = lean_ctor_get(v___x_2138_, 7);
v_snapshotTasks_2146_ = lean_ctor_get(v___x_2138_, 8);
v_newDecls_2147_ = lean_ctor_get(v___x_2138_, 9);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v___x_2138_, 5);
lean_dec(v_unused_2178_);
v___x_2149_ = v___x_2138_;
v_isShared_2150_ = v_isSharedCheck_2177_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_newDecls_2147_);
lean_inc(v_snapshotTasks_2146_);
lean_inc(v_infoState_2145_);
lean_inc(v_messages_2144_);
lean_inc(v_traceState_2143_);
lean_inc(v_auxDeclNGen_2142_);
lean_inc(v_ngen_2141_);
lean_inc(v_nextMacroScope_2140_);
lean_inc(v_env_2139_);
lean_dec(v___x_2138_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2177_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2151_ = l_Lean_Meta_eqnOptionsExt;
v___x_2152_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2151_, v_env_2139_, v_declName_2117_, v_a_2131_);
v___x_2153_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 5, v___x_2153_);
lean_ctor_set(v___x_2149_, 0, v___x_2152_);
v___x_2155_ = v___x_2149_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_nextMacroScope_2140_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_ngen_2141_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_auxDeclNGen_2142_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_traceState_2143_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_messages_2144_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_infoState_2145_);
lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_snapshotTasks_2146_);
lean_ctor_set(v_reuseFailAlloc_2176_, 9, v_newDecls_2147_);
v___x_2155_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_mctx_2158_; lean_object* v_zetaDeltaFVarIds_2159_; lean_object* v_postponed_2160_; lean_object* v_diag_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2174_; 
v___x_2156_ = lean_st_ref_set(v___y_2137_, v___x_2155_);
v___x_2157_ = lean_st_ref_take(v___y_2136_);
v_mctx_2158_ = lean_ctor_get(v___x_2157_, 0);
v_zetaDeltaFVarIds_2159_ = lean_ctor_get(v___x_2157_, 2);
v_postponed_2160_ = lean_ctor_get(v___x_2157_, 3);
v_diag_2161_ = lean_ctor_get(v___x_2157_, 4);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v___x_2157_, 1);
lean_dec(v_unused_2175_);
v___x_2163_ = v___x_2157_;
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_diag_2161_);
lean_inc(v_postponed_2160_);
lean_inc(v_zetaDeltaFVarIds_2159_);
lean_inc(v_mctx_2158_);
lean_dec(v___x_2157_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_mctx_2158_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_zetaDeltaFVarIds_2159_);
lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_postponed_2160_);
lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_diag_2161_);
v___x_2167_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2168_ = lean_st_ref_set(v___y_2136_, v___x_2167_);
v___x_2169_ = lean_box(0);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2169_);
v___x_2171_ = v___x_2133_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
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
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_declName_2117_);
v_a_2192_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2130_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2130_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2207_, lean_object* v_as_2208_, size_t v_sz_2209_, size_t v_i_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2207_, v_as_2208_, v_sz_2209_, v_i_2210_, v_b_2211_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2218_, lean_object* v_as_2219_, lean_object* v_sz_2220_, lean_object* v_i_2221_, lean_object* v_b_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
size_t v_sz_boxed_2228_; size_t v_i_boxed_2229_; lean_object* v_res_2230_; 
v_sz_boxed_2228_ = lean_unbox_usize(v_sz_2220_);
lean_dec(v_sz_2220_);
v_i_boxed_2229_ = lean_unbox_usize(v_i_2221_);
lean_dec(v_i_2221_);
v_res_2230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2218_, v_as_2219_, v_sz_boxed_2228_, v_i_boxed_2229_, v_b_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec_ref(v_as_2219_);
lean_dec_ref(v___x_2218_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_st_mk_ref(v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2256_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2256_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2256_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_unbox(v_a_2240_);
lean_dec(v_a_2240_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
lean_dec_ref(v_f_2237_);
v___x_2245_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 1);
lean_ctor_set(v___x_2242_, 0, v___x_2245_);
v___x_2247_ = v___x_2242_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2249_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2250_ = lean_st_ref_take(v___x_2249_);
v___x_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2251_, 0, v_f_2237_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_st_ref_set(v___x_2249_, v___x_2251_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2252_);
v___x_2254_ = v___x_2242_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_f_2237_);
v_a_2257_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2239_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2239_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2271_, lean_object* v_as_x27_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
if (lean_obj_tag(v_as_x27_2272_) == 0)
{
lean_object* v___x_2279_; 
lean_dec(v_declName_2271_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_b_2273_);
return v___x_2279_;
}
else
{
lean_object* v_head_2280_; lean_object* v_tail_2281_; lean_object* v___x_2282_; 
lean_dec_ref(v_b_2273_);
v_head_2280_ = lean_ctor_get(v_as_x27_2272_, 0);
v_tail_2281_ = lean_ctor_get(v_as_x27_2272_, 1);
lean_inc(v_head_2280_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v_declName_2271_);
v___x_2282_ = lean_apply_6(v_head_2280_, v_declName_2271_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, lean_box(0));
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2295_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_box(0);
if (lean_obj_tag(v_a_2283_) == 1)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
lean_dec(v_declName_2271_);
v___x_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_a_2283_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v___x_2287_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2289_);
v___x_2291_ = v___x_2285_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
else
{
lean_object* v___x_2293_; 
lean_del_object(v___x_2285_);
lean_dec(v_a_2283_);
v___x_2293_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2272_ = v_tail_2281_;
v_b_2273_ = v___x_2293_;
goto _start;
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_declName_2271_);
v_a_2296_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2282_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2282_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2304_, lean_object* v_as_x27_2305_, lean_object* v_b_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2304_, v_as_x27_2305_, v_b_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_as_x27_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2313_, lean_object* v_declName_2314_, uint8_t v_nonRec_2315_, lean_object* v___x_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2325_; lean_object* v_env_2326_; uint8_t v___x_2327_; uint8_t v___x_2328_; 
v___x_2325_ = lean_st_ref_get(v___y_2320_);
v_env_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_ref(v_env_2326_);
lean_dec(v___x_2325_);
v___x_2327_ = 1;
lean_inc(v___x_2313_);
v___x_2328_ = l_Lean_Environment_contains(v_env_2326_, v___x_2313_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; 
lean_dec(v___x_2313_);
lean_inc(v_declName_2314_);
v___x_2329_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2314_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = lean_unbox(v_a_2330_);
lean_dec(v_a_2330_);
if (v___x_2331_ == 0)
{
lean_dec_ref(v___x_2316_);
lean_dec(v_declName_2314_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2332_; 
lean_inc(v_declName_2314_);
v___x_2332_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2314_, v___y_2320_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
if (v___x_2334_ == 0)
{
if (v_nonRec_2315_ == 0)
{
lean_dec_ref(v___x_2316_);
lean_dec(v_declName_2314_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2335_; lean_object* v_env_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2335_ = lean_st_ref_get(v___y_2320_);
v_env_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc_ref(v_env_2336_);
lean_dec(v___x_2335_);
lean_inc(v_declName_2314_);
v___x_2337_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2336_, v_declName_2314_, v___x_2316_);
v___x_2338_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2314_, v___x_2337_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
return v___x_2338_;
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec_ref(v___x_2316_);
v___x_2339_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2340_ = lean_st_ref_get(v___x_2339_);
v___x_2341_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2342_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2314_, v___x_2340_, v___x_2341_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___x_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2352_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2352_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2352_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v_fst_2347_; 
v_fst_2347_ = lean_ctor_get(v_a_2343_, 0);
lean_inc(v_fst_2347_);
lean_dec(v_a_2343_);
if (lean_obj_tag(v_fst_2347_) == 0)
{
lean_del_object(v___x_2345_);
goto v___jp_2322_;
}
else
{
lean_object* v_val_2348_; lean_object* v___x_2350_; 
v_val_2348_ = lean_ctor_get(v_fst_2347_, 0);
lean_inc(v_val_2348_);
lean_dec_ref(v_fst_2347_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v_val_2348_);
v___x_2350_ = v___x_2345_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_val_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2342_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2342_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v___x_2316_);
lean_dec(v_declName_2314_);
v_a_2361_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2332_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2332_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v___x_2316_);
lean_dec(v_declName_2314_);
v_a_2369_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2329_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2329_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v___x_2316_);
lean_dec(v_declName_2314_);
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2313_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
v___jp_2322_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2379_, lean_object* v_declName_2380_, lean_object* v_nonRec_2381_, lean_object* v___x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v_nonRec_boxed_2388_; lean_object* v_res_2389_; 
v_nonRec_boxed_2388_ = lean_unbox(v_nonRec_2381_);
v_res_2389_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2379_, v_declName_2380_, v_nonRec_boxed_2388_, v___x_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_ref_2396_; lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
v_ref_2396_ = lean_ctor_get(v___y_2393_, 5);
v___x_2397_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_inc(v_ref_2396_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_ref_2396_);
lean_ctor_set(v___x_2402_, 1, v_a_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 1);
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2414_, uint8_t v_isExporting_2415_, lean_object* v___x_2416_, lean_object* v___y_2417_, lean_object* v___x_2418_, lean_object* v_a_x3f_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v_env_2422_; lean_object* v_nextMacroScope_2423_; lean_object* v_ngen_2424_; lean_object* v_auxDeclNGen_2425_; lean_object* v_traceState_2426_; lean_object* v_messages_2427_; lean_object* v_infoState_2428_; lean_object* v_snapshotTasks_2429_; lean_object* v_newDecls_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2455_; 
v___x_2421_ = lean_st_ref_take(v___y_2414_);
v_env_2422_ = lean_ctor_get(v___x_2421_, 0);
v_nextMacroScope_2423_ = lean_ctor_get(v___x_2421_, 1);
v_ngen_2424_ = lean_ctor_get(v___x_2421_, 2);
v_auxDeclNGen_2425_ = lean_ctor_get(v___x_2421_, 3);
v_traceState_2426_ = lean_ctor_get(v___x_2421_, 4);
v_messages_2427_ = lean_ctor_get(v___x_2421_, 6);
v_infoState_2428_ = lean_ctor_get(v___x_2421_, 7);
v_snapshotTasks_2429_ = lean_ctor_get(v___x_2421_, 8);
v_newDecls_2430_ = lean_ctor_get(v___x_2421_, 9);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v___x_2421_, 5);
lean_dec(v_unused_2456_);
v___x_2432_ = v___x_2421_;
v_isShared_2433_ = v_isSharedCheck_2455_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_newDecls_2430_);
lean_inc(v_snapshotTasks_2429_);
lean_inc(v_infoState_2428_);
lean_inc(v_messages_2427_);
lean_inc(v_traceState_2426_);
lean_inc(v_auxDeclNGen_2425_);
lean_inc(v_ngen_2424_);
lean_inc(v_nextMacroScope_2423_);
lean_inc(v_env_2422_);
lean_dec(v___x_2421_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2455_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = l_Lean_Environment_setExporting(v_env_2422_, v_isExporting_2415_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 5, v___x_2416_);
lean_ctor_set(v___x_2432_, 0, v___x_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_nextMacroScope_2423_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v_ngen_2424_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v_auxDeclNGen_2425_);
lean_ctor_set(v_reuseFailAlloc_2454_, 4, v_traceState_2426_);
lean_ctor_set(v_reuseFailAlloc_2454_, 5, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2454_, 6, v_messages_2427_);
lean_ctor_set(v_reuseFailAlloc_2454_, 7, v_infoState_2428_);
lean_ctor_set(v_reuseFailAlloc_2454_, 8, v_snapshotTasks_2429_);
lean_ctor_set(v_reuseFailAlloc_2454_, 9, v_newDecls_2430_);
v___x_2436_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_mctx_2439_; lean_object* v_zetaDeltaFVarIds_2440_; lean_object* v_postponed_2441_; lean_object* v_diag_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2452_; 
v___x_2437_ = lean_st_ref_set(v___y_2414_, v___x_2436_);
v___x_2438_ = lean_st_ref_take(v___y_2417_);
v_mctx_2439_ = lean_ctor_get(v___x_2438_, 0);
v_zetaDeltaFVarIds_2440_ = lean_ctor_get(v___x_2438_, 2);
v_postponed_2441_ = lean_ctor_get(v___x_2438_, 3);
v_diag_2442_ = lean_ctor_get(v___x_2438_, 4);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; 
v_unused_2453_ = lean_ctor_get(v___x_2438_, 1);
lean_dec(v_unused_2453_);
v___x_2444_ = v___x_2438_;
v_isShared_2445_ = v_isSharedCheck_2452_;
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
v_isShared_2445_ = v_isSharedCheck_2452_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2418_);
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_mctx_2439_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_zetaDeltaFVarIds_2440_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_postponed_2441_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_diag_2442_);
v___x_2447_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_st_ref_set(v___y_2417_, v___x_2447_);
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2457_, lean_object* v_isExporting_2458_, lean_object* v___x_2459_, lean_object* v___y_2460_, lean_object* v___x_2461_, lean_object* v_a_x3f_2462_, lean_object* v___y_2463_){
_start:
{
uint8_t v_isExporting_boxed_2464_; lean_object* v_res_2465_; 
v_isExporting_boxed_2464_ = lean_unbox(v_isExporting_2458_);
v_res_2465_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2457_, v_isExporting_boxed_2464_, v___x_2459_, v___y_2460_, v___x_2461_, v_a_x3f_2462_);
lean_dec(v_a_x3f_2462_);
lean_dec(v___y_2460_);
lean_dec(v___y_2457_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2466_, uint8_t v_isExporting_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; lean_object* v_env_2474_; uint8_t v_isExporting_2475_; lean_object* v___x_2476_; lean_object* v_env_2477_; lean_object* v_nextMacroScope_2478_; lean_object* v_ngen_2479_; lean_object* v_auxDeclNGen_2480_; lean_object* v_traceState_2481_; lean_object* v_messages_2482_; lean_object* v_infoState_2483_; lean_object* v_snapshotTasks_2484_; lean_object* v_newDecls_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2539_; 
v___x_2473_ = lean_st_ref_get(v___y_2471_);
v_env_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_ref(v_env_2474_);
lean_dec(v___x_2473_);
v_isExporting_2475_ = lean_ctor_get_uint8(v_env_2474_, sizeof(void*)*8);
lean_dec_ref(v_env_2474_);
v___x_2476_ = lean_st_ref_take(v___y_2471_);
v_env_2477_ = lean_ctor_get(v___x_2476_, 0);
v_nextMacroScope_2478_ = lean_ctor_get(v___x_2476_, 1);
v_ngen_2479_ = lean_ctor_get(v___x_2476_, 2);
v_auxDeclNGen_2480_ = lean_ctor_get(v___x_2476_, 3);
v_traceState_2481_ = lean_ctor_get(v___x_2476_, 4);
v_messages_2482_ = lean_ctor_get(v___x_2476_, 6);
v_infoState_2483_ = lean_ctor_get(v___x_2476_, 7);
v_snapshotTasks_2484_ = lean_ctor_get(v___x_2476_, 8);
v_newDecls_2485_ = lean_ctor_get(v___x_2476_, 9);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v___x_2476_, 5);
lean_dec(v_unused_2540_);
v___x_2487_ = v___x_2476_;
v_isShared_2488_ = v_isSharedCheck_2539_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_newDecls_2485_);
lean_inc(v_snapshotTasks_2484_);
lean_inc(v_infoState_2483_);
lean_inc(v_messages_2482_);
lean_inc(v_traceState_2481_);
lean_inc(v_auxDeclNGen_2480_);
lean_inc(v_ngen_2479_);
lean_inc(v_nextMacroScope_2478_);
lean_inc(v_env_2477_);
lean_dec(v___x_2476_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2539_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = l_Lean_Environment_setExporting(v_env_2477_, v_isExporting_2467_);
v___x_2490_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 5, v___x_2490_);
lean_ctor_set(v___x_2487_, 0, v___x_2489_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_nextMacroScope_2478_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_ngen_2479_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v_auxDeclNGen_2480_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v_traceState_2481_);
lean_ctor_set(v_reuseFailAlloc_2538_, 5, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2538_, 6, v_messages_2482_);
lean_ctor_set(v_reuseFailAlloc_2538_, 7, v_infoState_2483_);
lean_ctor_set(v_reuseFailAlloc_2538_, 8, v_snapshotTasks_2484_);
lean_ctor_set(v_reuseFailAlloc_2538_, 9, v_newDecls_2485_);
v___x_2492_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_mctx_2495_; lean_object* v_zetaDeltaFVarIds_2496_; lean_object* v_postponed_2497_; lean_object* v_diag_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2536_; 
v___x_2493_ = lean_st_ref_set(v___y_2471_, v___x_2492_);
v___x_2494_ = lean_st_ref_take(v___y_2469_);
v_mctx_2495_ = lean_ctor_get(v___x_2494_, 0);
v_zetaDeltaFVarIds_2496_ = lean_ctor_get(v___x_2494_, 2);
v_postponed_2497_ = lean_ctor_get(v___x_2494_, 3);
v_diag_2498_ = lean_ctor_get(v___x_2494_, 4);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; 
v_unused_2537_ = lean_ctor_get(v___x_2494_, 1);
lean_dec(v_unused_2537_);
v___x_2500_ = v___x_2494_;
v_isShared_2501_ = v_isSharedCheck_2536_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_diag_2498_);
lean_inc(v_postponed_2497_);
lean_inc(v_zetaDeltaFVarIds_2496_);
lean_inc(v_mctx_2495_);
lean_dec(v___x_2494_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2536_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_mctx_2495_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_zetaDeltaFVarIds_2496_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_postponed_2497_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_diag_2498_);
v___x_2504_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v_r_2506_; 
v___x_2505_ = lean_st_ref_set(v___y_2469_, v___x_2504_);
lean_inc(v___y_2471_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc_ref(v___y_2468_);
v_r_2506_ = lean_apply_5(v_x_2466_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, lean_box(0));
if (lean_obj_tag(v_r_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2523_; 
v_a_2507_ = lean_ctor_get(v_r_2506_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_r_2506_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2509_ = v_r_2506_;
v_isShared_2510_ = v_isSharedCheck_2523_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v_r_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2523_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
lean_inc(v_a_2507_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set_tag(v___x_2509_, 1);
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v___x_2513_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2471_, v_isExporting_2475_, v___x_2490_, v___y_2469_, v___x_2502_, v___x_2512_);
lean_dec_ref(v___x_2512_);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v___x_2513_, 0);
lean_dec(v_unused_2521_);
v___x_2515_ = v___x_2513_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_dec(v___x_2513_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v_a_2507_);
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2507_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2524_ = lean_ctor_get(v_r_2506_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v_r_2506_);
v___x_2525_ = lean_box(0);
v___x_2526_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2471_, v_isExporting_2475_, v___x_2490_, v___y_2469_, v___x_2502_, v___x_2525_);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2526_, 0);
lean_dec(v_unused_2534_);
v___x_2528_ = v___x_2526_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_dec(v___x_2526_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 1);
lean_ctor_set(v___x_2528_, 0, v_a_2524_);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2524_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2541_, lean_object* v_isExporting_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
uint8_t v_isExporting_boxed_2548_; lean_object* v_res_2549_; 
v_isExporting_boxed_2548_ = lean_unbox(v_isExporting_2542_);
v_res_2549_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2541_, v_isExporting_boxed_2548_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2550_, uint8_t v_when_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
if (v_when_2551_ == 0)
{
lean_object* v___x_2557_; 
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
v___x_2557_ = lean_apply_5(v_x_2550_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, lean_box(0));
return v___x_2557_;
}
else
{
uint8_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = 0;
v___x_2559_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2550_, v___x_2558_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2560_, lean_object* v_when_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v_when_boxed_2567_; lean_object* v_res_2568_; 
v_when_boxed_2567_ = lean_unbox(v_when_2561_);
v_res_2568_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2560_, v_when_boxed_2567_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2568_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2571_ = l_Lean_stringToMessageData(v___x_2570_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2578_, uint8_t v_nonRec_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; lean_object* v_env_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___f_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; 
v___x_2585_ = lean_st_ref_get(v___y_2583_);
v_env_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc_ref(v_env_2586_);
lean_dec(v___x_2585_);
v___x_2587_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2578_);
v___x_2588_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2586_, v_declName_2578_, v___x_2587_);
v___x_2589_ = lean_box(v_nonRec_2579_);
lean_inc(v___x_2588_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2590_, 0, v___x_2588_);
lean_closure_set(v___f_2590_, 1, v_declName_2578_);
lean_closure_set(v___f_2590_, 2, v___x_2589_);
lean_closure_set(v___f_2590_, 3, v___x_2587_);
v___x_2591_ = 1;
v___x_2592_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2590_, v___x_2591_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
if (lean_obj_tag(v_a_2593_) == 1)
{
lean_object* v_val_2594_; uint8_t v___x_2595_; 
v_val_2594_ = lean_ctor_get(v_a_2593_, 0);
lean_inc(v_val_2594_);
lean_dec_ref(v_a_2593_);
v___x_2595_ = lean_name_eq(v_val_2594_, v___x_2588_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v___x_2592_);
v___x_2596_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2597_ = l_Lean_MessageData_ofName(v_val_2594_);
v___x_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2598_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = l_Lean_MessageData_ofName(v___x_2588_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2604_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
else
{
lean_dec(v_val_2594_);
lean_dec(v___x_2588_);
return v___x_2592_;
}
}
else
{
lean_dec(v_a_2593_);
lean_dec(v___x_2588_);
return v___x_2592_;
}
}
else
{
lean_dec(v___x_2588_);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2614_, lean_object* v_nonRec_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
uint8_t v_nonRec_boxed_2621_; lean_object* v_res_2622_; 
v_nonRec_boxed_2621_ = lean_unbox(v_nonRec_2615_);
v_res_2622_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2614_, v_nonRec_boxed_2621_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2623_, uint8_t v_nonRec_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2630_ = lean_box(v_nonRec_2624_);
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2631_, 0, v_declName_2623_);
lean_closure_set(v___f_2631_, 1, v___x_2630_);
v___x_2632_ = lean_unsigned_to_nat(32u);
v___x_2633_ = lean_mk_empty_array_with_capacity(v___x_2632_);
lean_dec_ref(v___x_2633_);
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2635_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2636_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2634_, v___x_2635_, v___f_2631_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2637_, lean_object* v_nonRec_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
uint8_t v_nonRec_boxed_2644_; lean_object* v_res_2645_; 
v_nonRec_boxed_2644_ = lean_unbox(v_nonRec_2638_);
v_res_2645_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2637_, v_nonRec_boxed_2644_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2646_, lean_object* v_as_2647_, lean_object* v_as_x27_2648_, lean_object* v_b_2649_, lean_object* v_a_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2646_, v_as_x27_2648_, v_b_2649_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2657_, lean_object* v_as_2658_, lean_object* v_as_x27_2659_, lean_object* v_b_2660_, lean_object* v_a_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2657_, v_as_2658_, v_as_x27_2659_, v_b_2660_, v_a_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v_as_x27_2659_);
lean_dec(v_as_2658_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2668_, lean_object* v_x_2669_, uint8_t v_isExporting_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2669_, v_isExporting_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2677_, lean_object* v_x_2678_, lean_object* v_isExporting_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v_isExporting_boxed_2685_; lean_object* v_res_2686_; 
v_isExporting_boxed_2685_ = lean_unbox(v_isExporting_2679_);
v_res_2686_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2677_, v_x_2678_, v_isExporting_boxed_2685_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2687_, lean_object* v_x_2688_, uint8_t v_when_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2688_, v_when_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2696_, lean_object* v_x_2697_, lean_object* v_when_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
uint8_t v_when_boxed_2704_; lean_object* v_res_2705_; 
v_when_boxed_2704_ = lean_unbox(v_when_2698_);
v_res_2705_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2696_, v_x_2697_, v_when_boxed_2704_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_msg_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2714_, v_msg_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2721_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_unsigned_to_nat(32u);
v___x_2723_ = lean_mk_empty_array_with_capacity(v___x_2722_);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2725_ = ((size_t)5ULL);
v___x_2726_ = lean_unsigned_to_nat(0u);
v___x_2727_ = lean_unsigned_to_nat(32u);
v___x_2728_ = lean_mk_empty_array_with_capacity(v___x_2727_);
v___x_2729_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2730_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v___x_2728_);
lean_ctor_set(v___x_2730_, 2, v___x_2726_);
lean_ctor_set(v___x_2730_, 3, v___x_2726_);
lean_ctor_set_usize(v___x_2730_, 4, v___x_2725_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; lean_object* v_traceState_2734_; lean_object* v_traces_2735_; lean_object* v___x_2736_; lean_object* v_traceState_2737_; lean_object* v_env_2738_; lean_object* v_nextMacroScope_2739_; lean_object* v_ngen_2740_; lean_object* v_auxDeclNGen_2741_; lean_object* v_cache_2742_; lean_object* v_messages_2743_; lean_object* v_infoState_2744_; lean_object* v_snapshotTasks_2745_; lean_object* v_newDecls_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2765_; 
v___x_2733_ = lean_st_ref_get(v___y_2731_);
v_traceState_2734_ = lean_ctor_get(v___x_2733_, 4);
lean_inc_ref(v_traceState_2734_);
lean_dec(v___x_2733_);
v_traces_2735_ = lean_ctor_get(v_traceState_2734_, 0);
lean_inc_ref(v_traces_2735_);
lean_dec_ref(v_traceState_2734_);
v___x_2736_ = lean_st_ref_take(v___y_2731_);
v_traceState_2737_ = lean_ctor_get(v___x_2736_, 4);
v_env_2738_ = lean_ctor_get(v___x_2736_, 0);
v_nextMacroScope_2739_ = lean_ctor_get(v___x_2736_, 1);
v_ngen_2740_ = lean_ctor_get(v___x_2736_, 2);
v_auxDeclNGen_2741_ = lean_ctor_get(v___x_2736_, 3);
v_cache_2742_ = lean_ctor_get(v___x_2736_, 5);
v_messages_2743_ = lean_ctor_get(v___x_2736_, 6);
v_infoState_2744_ = lean_ctor_get(v___x_2736_, 7);
v_snapshotTasks_2745_ = lean_ctor_get(v___x_2736_, 8);
v_newDecls_2746_ = lean_ctor_get(v___x_2736_, 9);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2748_ = v___x_2736_;
v_isShared_2749_ = v_isSharedCheck_2765_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_newDecls_2746_);
lean_inc(v_snapshotTasks_2745_);
lean_inc(v_infoState_2744_);
lean_inc(v_messages_2743_);
lean_inc(v_cache_2742_);
lean_inc(v_traceState_2737_);
lean_inc(v_auxDeclNGen_2741_);
lean_inc(v_ngen_2740_);
lean_inc(v_nextMacroScope_2739_);
lean_inc(v_env_2738_);
lean_dec(v___x_2736_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2765_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint64_t v_tid_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2763_; 
v_tid_2750_ = lean_ctor_get_uint64(v_traceState_2737_, sizeof(void*)*1);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_traceState_2737_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v_traceState_2737_, 0);
lean_dec(v_unused_2764_);
v___x_2752_ = v_traceState_2737_;
v_isShared_2753_ = v_isSharedCheck_2763_;
goto v_resetjp_2751_;
}
else
{
lean_dec(v_traceState_2737_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2763_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2754_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2754_);
v___x_2756_ = v___x_2752_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2754_);
lean_ctor_set_uint64(v_reuseFailAlloc_2762_, sizeof(void*)*1, v_tid_2750_);
v___x_2756_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2758_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 4, v___x_2756_);
v___x_2758_ = v___x_2748_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_env_2738_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_nextMacroScope_2739_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_ngen_2740_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v_auxDeclNGen_2741_);
lean_ctor_set(v_reuseFailAlloc_2761_, 4, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2761_, 5, v_cache_2742_);
lean_ctor_set(v_reuseFailAlloc_2761_, 6, v_messages_2743_);
lean_ctor_set(v_reuseFailAlloc_2761_, 7, v_infoState_2744_);
lean_ctor_set(v_reuseFailAlloc_2761_, 8, v_snapshotTasks_2745_);
lean_ctor_set(v_reuseFailAlloc_2761_, 9, v_newDecls_2746_);
v___x_2758_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_st_ref_set(v___y_2731_, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_traces_2735_);
return v___x_2760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2766_);
lean_dec(v___y_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
uint8_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = 0;
v___x_2782_ = lean_box(v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
return v_res_2788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2791_ = l_Lean_stringToMessageData(v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2797_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2798_ = l_Lean_MessageData_ofName(v_name_2792_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2801_, lean_object* v_x_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2801_, v_x_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec_ref(v_x_2802_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_x_2807_){
_start:
{
if (lean_obj_tag(v_x_2807_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v_x_2807_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_x_2807_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v_x_2807_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v_x_2807_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 1);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_a_2817_ = lean_ctor_get(v_x_2807_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_x_2807_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v_x_2807_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v_x_2807_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 0);
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_x_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_2825_);
return v_res_2827_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_e_2828_){
_start:
{
if (lean_obj_tag(v_e_2828_) == 0)
{
uint8_t v___x_2829_; 
v___x_2829_ = 2;
return v___x_2829_;
}
else
{
lean_object* v_a_2830_; uint8_t v___x_2831_; 
v_a_2830_ = lean_ctor_get(v_e_2828_, 0);
v___x_2831_ = lean_unbox(v_a_2830_);
if (v___x_2831_ == 0)
{
uint8_t v___x_2832_; 
v___x_2832_ = 1;
return v___x_2832_;
}
else
{
uint8_t v___x_2833_; 
v___x_2833_ = 0;
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_e_2834_){
_start:
{
uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_res_2835_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_e_2834_);
lean_dec_ref(v_e_2834_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(size_t v_sz_2837_, size_t v_i_2838_, lean_object* v_bs_2839_){
_start:
{
uint8_t v___x_2840_; 
v___x_2840_ = lean_usize_dec_lt(v_i_2838_, v_sz_2837_);
if (v___x_2840_ == 0)
{
return v_bs_2839_;
}
else
{
lean_object* v_v_2841_; lean_object* v_msg_2842_; lean_object* v___x_2843_; lean_object* v_bs_x27_2844_; size_t v___x_2845_; size_t v___x_2846_; lean_object* v___x_2847_; 
v_v_2841_ = lean_array_uget_borrowed(v_bs_2839_, v_i_2838_);
v_msg_2842_ = lean_ctor_get(v_v_2841_, 1);
lean_inc_ref(v_msg_2842_);
v___x_2843_ = lean_unsigned_to_nat(0u);
v_bs_x27_2844_ = lean_array_uset(v_bs_2839_, v_i_2838_, v___x_2843_);
v___x_2845_ = ((size_t)1ULL);
v___x_2846_ = lean_usize_add(v_i_2838_, v___x_2845_);
v___x_2847_ = lean_array_uset(v_bs_x27_2844_, v_i_2838_, v_msg_2842_);
v_i_2838_ = v___x_2846_;
v_bs_2839_ = v___x_2847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_sz_2849_, lean_object* v_i_2850_, lean_object* v_bs_2851_){
_start:
{
size_t v_sz_boxed_2852_; size_t v_i_boxed_2853_; lean_object* v_res_2854_; 
v_sz_boxed_2852_ = lean_unbox_usize(v_sz_2849_);
lean_dec(v_sz_2849_);
v_i_boxed_2853_ = lean_unbox_usize(v_i_2850_);
lean_dec(v_i_2850_);
v_res_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_boxed_2852_, v_i_boxed_2853_, v_bs_2851_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_oldTraces_2855_, lean_object* v_data_2856_, lean_object* v_ref_2857_, lean_object* v_msg_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_fileName_2862_; lean_object* v_fileMap_2863_; lean_object* v_options_2864_; lean_object* v_currRecDepth_2865_; lean_object* v_maxRecDepth_2866_; lean_object* v_ref_2867_; lean_object* v_currNamespace_2868_; lean_object* v_openDecls_2869_; lean_object* v_initHeartbeats_2870_; lean_object* v_maxHeartbeats_2871_; lean_object* v_quotContext_2872_; lean_object* v_currMacroScope_2873_; uint8_t v_diag_2874_; lean_object* v_cancelTk_x3f_2875_; uint8_t v_suppressElabErrors_2876_; lean_object* v_inheritedTraceOptions_2877_; lean_object* v___x_2878_; lean_object* v_traceState_2879_; lean_object* v_traces_2880_; lean_object* v_ref_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; size_t v_sz_2884_; size_t v___x_2885_; lean_object* v___x_2886_; lean_object* v_msg_2887_; lean_object* v___x_2888_; lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2927_; 
v_fileName_2862_ = lean_ctor_get(v___y_2859_, 0);
v_fileMap_2863_ = lean_ctor_get(v___y_2859_, 1);
v_options_2864_ = lean_ctor_get(v___y_2859_, 2);
v_currRecDepth_2865_ = lean_ctor_get(v___y_2859_, 3);
v_maxRecDepth_2866_ = lean_ctor_get(v___y_2859_, 4);
v_ref_2867_ = lean_ctor_get(v___y_2859_, 5);
v_currNamespace_2868_ = lean_ctor_get(v___y_2859_, 6);
v_openDecls_2869_ = lean_ctor_get(v___y_2859_, 7);
v_initHeartbeats_2870_ = lean_ctor_get(v___y_2859_, 8);
v_maxHeartbeats_2871_ = lean_ctor_get(v___y_2859_, 9);
v_quotContext_2872_ = lean_ctor_get(v___y_2859_, 10);
v_currMacroScope_2873_ = lean_ctor_get(v___y_2859_, 11);
v_diag_2874_ = lean_ctor_get_uint8(v___y_2859_, sizeof(void*)*14);
v_cancelTk_x3f_2875_ = lean_ctor_get(v___y_2859_, 12);
v_suppressElabErrors_2876_ = lean_ctor_get_uint8(v___y_2859_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2877_ = lean_ctor_get(v___y_2859_, 13);
v___x_2878_ = lean_st_ref_get(v___y_2860_);
v_traceState_2879_ = lean_ctor_get(v___x_2878_, 4);
lean_inc_ref(v_traceState_2879_);
lean_dec(v___x_2878_);
v_traces_2880_ = lean_ctor_get(v_traceState_2879_, 0);
lean_inc_ref(v_traces_2880_);
lean_dec_ref(v_traceState_2879_);
v_ref_2881_ = l_Lean_replaceRef(v_ref_2857_, v_ref_2867_);
lean_inc_ref(v_inheritedTraceOptions_2877_);
lean_inc(v_cancelTk_x3f_2875_);
lean_inc(v_currMacroScope_2873_);
lean_inc(v_quotContext_2872_);
lean_inc(v_maxHeartbeats_2871_);
lean_inc(v_initHeartbeats_2870_);
lean_inc(v_openDecls_2869_);
lean_inc(v_currNamespace_2868_);
lean_inc(v_maxRecDepth_2866_);
lean_inc(v_currRecDepth_2865_);
lean_inc_ref(v_options_2864_);
lean_inc_ref(v_fileMap_2863_);
lean_inc_ref(v_fileName_2862_);
v___x_2882_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2882_, 0, v_fileName_2862_);
lean_ctor_set(v___x_2882_, 1, v_fileMap_2863_);
lean_ctor_set(v___x_2882_, 2, v_options_2864_);
lean_ctor_set(v___x_2882_, 3, v_currRecDepth_2865_);
lean_ctor_set(v___x_2882_, 4, v_maxRecDepth_2866_);
lean_ctor_set(v___x_2882_, 5, v_ref_2881_);
lean_ctor_set(v___x_2882_, 6, v_currNamespace_2868_);
lean_ctor_set(v___x_2882_, 7, v_openDecls_2869_);
lean_ctor_set(v___x_2882_, 8, v_initHeartbeats_2870_);
lean_ctor_set(v___x_2882_, 9, v_maxHeartbeats_2871_);
lean_ctor_set(v___x_2882_, 10, v_quotContext_2872_);
lean_ctor_set(v___x_2882_, 11, v_currMacroScope_2873_);
lean_ctor_set(v___x_2882_, 12, v_cancelTk_x3f_2875_);
lean_ctor_set(v___x_2882_, 13, v_inheritedTraceOptions_2877_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*14, v_diag_2874_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*14 + 1, v_suppressElabErrors_2876_);
v___x_2883_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2880_);
lean_dec_ref(v_traces_2880_);
v_sz_2884_ = lean_array_size(v___x_2883_);
v___x_2885_ = ((size_t)0ULL);
v___x_2886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_2884_, v___x_2885_, v___x_2883_);
v_msg_2887_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2887_, 0, v_data_2856_);
lean_ctor_set(v_msg_2887_, 1, v_msg_2858_);
lean_ctor_set(v_msg_2887_, 2, v___x_2886_);
v___x_2888_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2887_, v___x_2882_, v___y_2860_);
lean_dec_ref(v___x_2882_);
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2927_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2927_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v_traceState_2894_; lean_object* v_env_2895_; lean_object* v_nextMacroScope_2896_; lean_object* v_ngen_2897_; lean_object* v_auxDeclNGen_2898_; lean_object* v_cache_2899_; lean_object* v_messages_2900_; lean_object* v_infoState_2901_; lean_object* v_snapshotTasks_2902_; lean_object* v_newDecls_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2926_; 
v___x_2893_ = lean_st_ref_take(v___y_2860_);
v_traceState_2894_ = lean_ctor_get(v___x_2893_, 4);
v_env_2895_ = lean_ctor_get(v___x_2893_, 0);
v_nextMacroScope_2896_ = lean_ctor_get(v___x_2893_, 1);
v_ngen_2897_ = lean_ctor_get(v___x_2893_, 2);
v_auxDeclNGen_2898_ = lean_ctor_get(v___x_2893_, 3);
v_cache_2899_ = lean_ctor_get(v___x_2893_, 5);
v_messages_2900_ = lean_ctor_get(v___x_2893_, 6);
v_infoState_2901_ = lean_ctor_get(v___x_2893_, 7);
v_snapshotTasks_2902_ = lean_ctor_get(v___x_2893_, 8);
v_newDecls_2903_ = lean_ctor_get(v___x_2893_, 9);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2905_ = v___x_2893_;
v_isShared_2906_ = v_isSharedCheck_2926_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_newDecls_2903_);
lean_inc(v_snapshotTasks_2902_);
lean_inc(v_infoState_2901_);
lean_inc(v_messages_2900_);
lean_inc(v_cache_2899_);
lean_inc(v_traceState_2894_);
lean_inc(v_auxDeclNGen_2898_);
lean_inc(v_ngen_2897_);
lean_inc(v_nextMacroScope_2896_);
lean_inc(v_env_2895_);
lean_dec(v___x_2893_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2926_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
uint64_t v_tid_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2924_; 
v_tid_2907_ = lean_ctor_get_uint64(v_traceState_2894_, sizeof(void*)*1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_traceState_2894_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; 
v_unused_2925_ = lean_ctor_get(v_traceState_2894_, 0);
lean_dec(v_unused_2925_);
v___x_2909_ = v_traceState_2894_;
v_isShared_2910_ = v_isSharedCheck_2924_;
goto v_resetjp_2908_;
}
else
{
lean_dec(v_traceState_2894_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2924_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_ref_2857_);
lean_ctor_set(v___x_2911_, 1, v_a_2889_);
v___x_2912_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2855_, v___x_2911_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v___x_2912_);
v___x_2914_ = v___x_2909_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2912_);
lean_ctor_set_uint64(v_reuseFailAlloc_2923_, sizeof(void*)*1, v_tid_2907_);
v___x_2914_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 4, v___x_2914_);
v___x_2916_ = v___x_2905_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_env_2895_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_nextMacroScope_2896_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v_ngen_2897_);
lean_ctor_set(v_reuseFailAlloc_2922_, 3, v_auxDeclNGen_2898_);
lean_ctor_set(v_reuseFailAlloc_2922_, 4, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2922_, 5, v_cache_2899_);
lean_ctor_set(v_reuseFailAlloc_2922_, 6, v_messages_2900_);
lean_ctor_set(v_reuseFailAlloc_2922_, 7, v_infoState_2901_);
lean_ctor_set(v_reuseFailAlloc_2922_, 8, v_snapshotTasks_2902_);
lean_ctor_set(v_reuseFailAlloc_2922_, 9, v_newDecls_2903_);
v___x_2916_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2917_ = lean_st_ref_set(v___y_2860_, v___x_2916_);
v___x_2918_ = lean_box(0);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2918_);
v___x_2920_ = v___x_2891_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_oldTraces_2928_, lean_object* v_data_2929_, lean_object* v_ref_2930_, lean_object* v_msg_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2928_, v_data_2929_, v_ref_2930_, v_msg_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2935_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2938_ = l_Lean_stringToMessageData(v___x_2937_);
return v___x_2938_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2));
v___x_2941_ = l_Lean_stringToMessageData(v___x_2940_);
return v___x_2941_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4(void){
_start:
{
lean_object* v___x_2942_; double v___x_2943_; 
v___x_2942_ = lean_unsigned_to_nat(1000u);
v___x_2943_ = lean_float_of_nat(v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2944_, uint8_t v_collapsed_2945_, lean_object* v_tag_2946_, lean_object* v_opts_2947_, uint8_t v_clsEnabled_2948_, lean_object* v_oldTraces_2949_, lean_object* v_msg_2950_, lean_object* v_resStartStop_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3055_; 
v_fst_2955_ = lean_ctor_get(v_resStartStop_2951_, 0);
v_snd_2956_ = lean_ctor_get(v_resStartStop_2951_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_resStartStop_2951_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_2958_ = v_resStartStop_2951_;
v_isShared_2959_ = v_isSharedCheck_3055_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_snd_2956_);
lean_inc(v_fst_2955_);
lean_dec(v_resStartStop_2951_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3055_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v_data_2963_; lean_object* v_fst_2974_; lean_object* v_snd_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3054_; 
v_fst_2974_ = lean_ctor_get(v_snd_2956_, 0);
v_snd_2975_ = lean_ctor_get(v_snd_2956_, 1);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_snd_2956_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_2977_ = v_snd_2956_;
v_isShared_2978_ = v_isSharedCheck_3054_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_snd_2975_);
lean_inc(v_fst_2974_);
lean_dec(v_snd_2956_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3054_;
goto v_resetjp_2976_;
}
v___jp_2960_:
{
lean_object* v___x_2964_; 
lean_inc(v___y_2962_);
v___x_2964_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2949_, v_data_2963_, v___y_2962_, v___y_2961_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref(v___x_2964_);
v___x_2965_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2955_);
return v___x_2965_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_fst_2955_);
v_a_2966_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2964_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v___y_2982_; lean_object* v_a_2983_; uint8_t v___y_3007_; double v___y_3039_; 
v___x_2979_ = l_Lean_trace_profiler;
v___x_2980_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2947_, v___x_2979_);
if (v___x_2980_ == 0)
{
v___y_3007_ = v___x_2980_;
goto v___jp_3006_;
}
else
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3045_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2947_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; double v___x_3048_; double v___x_3049_; double v___x_3050_; 
v___x_3046_ = l_Lean_trace_profiler_threshold;
v___x_3047_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2947_, v___x_3046_);
v___x_3048_ = lean_float_of_nat(v___x_3047_);
v___x_3049_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4);
v___x_3050_ = lean_float_div(v___x_3048_, v___x_3049_);
v___y_3039_ = v___x_3050_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; double v___x_3053_; 
v___x_3051_ = l_Lean_trace_profiler_threshold;
v___x_3052_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2947_, v___x_3051_);
v___x_3053_ = lean_float_of_nat(v___x_3052_);
v___y_3039_ = v___x_3053_;
goto v___jp_3038_;
}
}
v___jp_2981_:
{
uint8_t v_result_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v_result_2984_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_fst_2955_);
v___x_2985_ = l_Lean_TraceResult_toEmoji(v_result_2984_);
v___x_2986_ = l_Lean_stringToMessageData(v___x_2985_);
v___x_2987_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 7);
lean_ctor_set(v___x_2977_, 1, v___x_2987_);
lean_ctor_set(v___x_2977_, 0, v___x_2986_);
v___x_2989_ = v___x_2977_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v_m_2991_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 7);
lean_ctor_set(v___x_2958_, 1, v_a_2983_);
lean_ctor_set(v___x_2958_, 0, v___x_2989_);
v_m_2991_ = v___x_2958_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_a_2983_);
v_m_2991_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; double v___x_2994_; lean_object* v_data_2995_; 
v___x_2992_ = lean_box(v_result_2984_);
v___x_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
v___x_2994_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2946_);
lean_inc_ref(v___x_2993_);
lean_inc(v_cls_2944_);
v_data_2995_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2995_, 0, v_cls_2944_);
lean_ctor_set(v_data_2995_, 1, v___x_2993_);
lean_ctor_set(v_data_2995_, 2, v_tag_2946_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3, v___x_2994_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3 + 8, v___x_2994_);
lean_ctor_set_uint8(v_data_2995_, sizeof(void*)*3 + 16, v_collapsed_2945_);
if (v___x_2980_ == 0)
{
lean_dec_ref(v___x_2993_);
lean_dec(v_snd_2975_);
lean_dec(v_fst_2974_);
lean_dec_ref(v_tag_2946_);
lean_dec(v_cls_2944_);
v___y_2961_ = v_m_2991_;
v___y_2962_ = v___y_2982_;
v_data_2963_ = v_data_2995_;
goto v___jp_2960_;
}
else
{
lean_object* v_data_2996_; double v___x_2997_; double v___x_2998_; 
lean_dec_ref(v_data_2995_);
v_data_2996_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2996_, 0, v_cls_2944_);
lean_ctor_set(v_data_2996_, 1, v___x_2993_);
lean_ctor_set(v_data_2996_, 2, v_tag_2946_);
v___x_2997_ = lean_unbox_float(v_fst_2974_);
lean_dec(v_fst_2974_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3, v___x_2997_);
v___x_2998_ = lean_unbox_float(v_snd_2975_);
lean_dec(v_snd_2975_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3 + 8, v___x_2998_);
lean_ctor_set_uint8(v_data_2996_, sizeof(void*)*3 + 16, v_collapsed_2945_);
v___y_2961_ = v_m_2991_;
v___y_2962_ = v___y_2982_;
v_data_2963_ = v_data_2996_;
goto v___jp_2960_;
}
}
}
}
v___jp_3001_:
{
lean_object* v_ref_3002_; lean_object* v___x_3003_; 
v_ref_3002_ = lean_ctor_get(v___y_2952_, 5);
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc(v_fst_2955_);
v___x_3003_ = lean_apply_4(v_msg_2950_, v_fst_2955_, v___y_2952_, v___y_2953_, lean_box(0));
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___y_2982_ = v_ref_3002_;
v_a_2983_ = v_a_3004_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3005_; 
lean_dec_ref(v___x_3003_);
v___x_3005_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3);
v___y_2982_ = v_ref_3002_;
v_a_2983_ = v___x_3005_;
goto v___jp_2981_;
}
}
v___jp_3006_:
{
if (v_clsEnabled_2948_ == 0)
{
if (v___y_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v_traceState_3009_; lean_object* v_env_3010_; lean_object* v_nextMacroScope_3011_; lean_object* v_ngen_3012_; lean_object* v_auxDeclNGen_3013_; lean_object* v_cache_3014_; lean_object* v_messages_3015_; lean_object* v_infoState_3016_; lean_object* v_snapshotTasks_3017_; lean_object* v_newDecls_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_2977_);
lean_dec(v_snd_2975_);
lean_dec(v_fst_2974_);
lean_del_object(v___x_2958_);
lean_dec_ref(v_msg_2950_);
lean_dec_ref(v_tag_2946_);
lean_dec(v_cls_2944_);
v___x_3008_ = lean_st_ref_take(v___y_2953_);
v_traceState_3009_ = lean_ctor_get(v___x_3008_, 4);
v_env_3010_ = lean_ctor_get(v___x_3008_, 0);
v_nextMacroScope_3011_ = lean_ctor_get(v___x_3008_, 1);
v_ngen_3012_ = lean_ctor_get(v___x_3008_, 2);
v_auxDeclNGen_3013_ = lean_ctor_get(v___x_3008_, 3);
v_cache_3014_ = lean_ctor_get(v___x_3008_, 5);
v_messages_3015_ = lean_ctor_get(v___x_3008_, 6);
v_infoState_3016_ = lean_ctor_get(v___x_3008_, 7);
v_snapshotTasks_3017_ = lean_ctor_get(v___x_3008_, 8);
v_newDecls_3018_ = lean_ctor_get(v___x_3008_, 9);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3020_ = v___x_3008_;
v_isShared_3021_ = v_isSharedCheck_3037_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_newDecls_3018_);
lean_inc(v_snapshotTasks_3017_);
lean_inc(v_infoState_3016_);
lean_inc(v_messages_3015_);
lean_inc(v_cache_3014_);
lean_inc(v_traceState_3009_);
lean_inc(v_auxDeclNGen_3013_);
lean_inc(v_ngen_3012_);
lean_inc(v_nextMacroScope_3011_);
lean_inc(v_env_3010_);
lean_dec(v___x_3008_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3037_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
uint64_t v_tid_3022_; lean_object* v_traces_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3036_; 
v_tid_3022_ = lean_ctor_get_uint64(v_traceState_3009_, sizeof(void*)*1);
v_traces_3023_ = lean_ctor_get(v_traceState_3009_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_traceState_3009_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3025_ = v_traceState_3009_;
v_isShared_3026_ = v_isSharedCheck_3036_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_traces_3023_);
lean_dec(v_traceState_3009_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3036_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3027_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2949_, v_traces_3023_);
lean_dec_ref(v_traces_3023_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3027_);
v___x_3029_ = v___x_3025_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3027_);
lean_ctor_set_uint64(v_reuseFailAlloc_3035_, sizeof(void*)*1, v_tid_3022_);
v___x_3029_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3031_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 4, v___x_3029_);
v___x_3031_ = v___x_3020_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_env_3010_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_nextMacroScope_3011_);
lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_ngen_3012_);
lean_ctor_set(v_reuseFailAlloc_3034_, 3, v_auxDeclNGen_3013_);
lean_ctor_set(v_reuseFailAlloc_3034_, 4, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3034_, 5, v_cache_3014_);
lean_ctor_set(v_reuseFailAlloc_3034_, 6, v_messages_3015_);
lean_ctor_set(v_reuseFailAlloc_3034_, 7, v_infoState_3016_);
lean_ctor_set(v_reuseFailAlloc_3034_, 8, v_snapshotTasks_3017_);
lean_ctor_set(v_reuseFailAlloc_3034_, 9, v_newDecls_3018_);
v___x_3031_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_st_ref_set(v___y_2953_, v___x_3031_);
v___x_3033_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2955_);
return v___x_3033_;
}
}
}
}
}
else
{
goto v___jp_3001_;
}
}
else
{
goto v___jp_3001_;
}
}
v___jp_3038_:
{
double v___x_3040_; double v___x_3041_; double v___x_3042_; uint8_t v___x_3043_; 
v___x_3040_ = lean_unbox_float(v_snd_2975_);
v___x_3041_ = lean_unbox_float(v_fst_2974_);
v___x_3042_ = lean_float_sub(v___x_3040_, v___x_3041_);
v___x_3043_ = lean_float_decLt(v___y_3039_, v___x_3042_);
v___y_3007_ = v___x_3043_;
goto v___jp_3006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3056_, lean_object* v_collapsed_3057_, lean_object* v_tag_3058_, lean_object* v_opts_3059_, lean_object* v_clsEnabled_3060_, lean_object* v_oldTraces_3061_, lean_object* v_msg_3062_, lean_object* v_resStartStop_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
uint8_t v_collapsed_boxed_3067_; uint8_t v_clsEnabled_boxed_3068_; lean_object* v_res_3069_; 
v_collapsed_boxed_3067_ = lean_unbox(v_collapsed_3057_);
v_clsEnabled_boxed_3068_ = lean_unbox(v_clsEnabled_3060_);
v_res_3069_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3056_, v_collapsed_boxed_3067_, v_tag_3058_, v_opts_3059_, v_clsEnabled_boxed_3068_, v_oldTraces_3061_, v_msg_3062_, v_resStartStop_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec_ref(v_opts_3059_);
return v_res_3069_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
lean_ctor_set(v___x_3074_, 2, v___x_3073_);
lean_ctor_set(v___x_3074_, 3, v___x_3073_);
lean_ctor_set(v___x_3074_, 4, v___x_3072_);
lean_ctor_set(v___x_3074_, 5, v___x_3072_);
lean_ctor_set(v___x_3074_, 6, v___x_3072_);
lean_ctor_set(v___x_3074_, 7, v___x_3072_);
lean_ctor_set(v___x_3074_, 8, v___x_3072_);
lean_ctor_set(v___x_3074_, 9, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3076_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
lean_ctor_set(v___x_3076_, 2, v___x_3075_);
lean_ctor_set(v___x_3076_, 3, v___x_3075_);
lean_ctor_set(v___x_3076_, 4, v___x_3075_);
lean_ctor_set(v___x_3076_, 5, v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
lean_ctor_set(v___x_3078_, 2, v___x_3077_);
lean_ctor_set(v___x_3078_, 3, v___x_3077_);
lean_ctor_set(v___x_3078_, 4, v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3079_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3080_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3081_ = lean_box(1);
v___x_3082_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3083_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v___x_3082_);
lean_ctor_set(v___x_3084_, 2, v___x_3081_);
lean_ctor_set(v___x_3084_, 3, v___x_3080_);
lean_ctor_set(v___x_3084_, 4, v___x_3079_);
return v___x_3084_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3090_ = l_Lean_Name_append(v___x_3089_, v___x_3088_);
return v___x_3090_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3091_; double v___x_3092_; 
v___x_3091_ = lean_unsigned_to_nat(1000000000u);
v___x_3092_ = lean_float_of_nat(v___x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3093_, lean_object* v_name_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_options_3098_; uint8_t v_hasTrace_3099_; 
v_options_3098_ = lean_ctor_get(v___y_3095_, 2);
v_hasTrace_3099_ = lean_ctor_get_uint8(v_options_3098_, sizeof(void*)*1);
if (v_hasTrace_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v_env_3101_; lean_object* v___x_3102_; 
lean_dec_ref(v___f_3093_);
v___x_3100_ = lean_st_ref_get(v___y_3096_);
v_env_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_ref(v_env_3101_);
lean_dec(v___x_3100_);
lean_inc(v_name_3094_);
v___x_3102_ = l_Lean_Meta_declFromEqLikeName(v_env_3101_, v_name_3094_);
if (lean_obj_tag(v___x_3102_) == 1)
{
lean_object* v_val_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3202_; 
v_val_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3202_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_val_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3202_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_fst_3107_; lean_object* v_snd_3108_; lean_object* v___x_3109_; lean_object* v_env_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v_fst_3107_ = lean_ctor_get(v_val_3103_, 0);
lean_inc_n(v_fst_3107_, 2);
v_snd_3108_ = lean_ctor_get(v_val_3103_, 1);
lean_inc_n(v_snd_3108_, 2);
lean_dec(v_val_3103_);
v___x_3109_ = lean_st_ref_get(v___y_3096_);
v_env_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc_ref(v_env_3110_);
lean_dec(v___x_3109_);
v___x_3111_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3110_, v_fst_3107_, v_snd_3108_);
v___x_3112_ = lean_name_eq(v_name_3094_, v___x_3111_);
lean_dec(v___x_3111_);
lean_dec(v_name_3094_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_dec(v_snd_3108_);
lean_dec(v_fst_3107_);
v___x_3113_ = lean_box(v_hasTrace_3099_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3113_);
v___x_3115_ = v___x_3105_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
else
{
uint8_t v___x_3117_; lean_object* v_a_3119_; 
lean_inc(v_snd_3108_);
v___x_3117_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3108_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3133_; uint8_t v___x_3134_; lean_object* v_a_3136_; 
lean_del_object(v___x_3105_);
v___x_3133_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3134_ = lean_string_dec_eq(v_snd_3108_, v___x_3133_);
lean_dec(v_snd_3108_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec(v_fst_3107_);
v___x_3148_ = lean_box(v_hasTrace_3099_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
else
{
uint8_t v___x_3150_; uint8_t v___x_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; uint64_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3150_ = 1;
v___x_3151_ = 0;
v___x_3152_ = 2;
v___x_3153_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3153_, 0, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3153_, 1, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3153_, 2, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3153_, 3, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3153_, 4, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3153_, 5, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 6, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 7, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3153_, 8, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 9, v___x_3150_);
lean_ctor_set_uint8(v___x_3153_, 10, v___x_3151_);
lean_ctor_set_uint8(v___x_3153_, 11, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 12, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 13, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 14, v___x_3152_);
lean_ctor_set_uint8(v___x_3153_, 15, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 16, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 17, v___x_3134_);
lean_ctor_set_uint8(v___x_3153_, 18, v___x_3134_);
v___x_3154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3155_, 0, v___x_3153_);
lean_ctor_set_uint64(v___x_3155_, sizeof(void*)*1, v___x_3154_);
v___x_3156_ = lean_box(1);
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3160_ = lean_box(0);
v___x_3161_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3161_, 0, v___x_3155_);
lean_ctor_set(v___x_3161_, 1, v___x_3156_);
lean_ctor_set(v___x_3161_, 2, v___x_3158_);
lean_ctor_set(v___x_3161_, 3, v___x_3159_);
lean_ctor_set(v___x_3161_, 4, v___x_3160_);
lean_ctor_set(v___x_3161_, 5, v___x_3157_);
lean_ctor_set(v___x_3161_, 6, v___x_3160_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7 + 1, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7 + 2, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7 + 3, v___x_3112_);
v___x_3162_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3163_ = lean_st_mk_ref(v___x_3162_);
v___x_3164_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3107_, v___x_3112_, v___x_3161_, v___x_3163_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3161_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = lean_st_ref_get(v___x_3163_);
lean_dec(v___x_3163_);
lean_dec(v___x_3166_);
v_a_3136_ = v_a_3165_;
goto v___jp_3135_;
}
else
{
lean_dec(v___x_3163_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3167_; 
v_a_3167_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3167_);
lean_dec_ref(v___x_3164_);
v_a_3136_ = v_a_3167_;
goto v___jp_3135_;
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
v_a_3168_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3164_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3164_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
v___jp_3135_:
{
if (lean_obj_tag(v_a_3136_) == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_box(v_hasTrace_3099_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
else
{
lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3146_; 
v_isSharedCheck_3146_ = !lean_is_exclusive(v_a_3136_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v_a_3136_, 0);
lean_dec(v_unused_3147_);
v___x_3140_ = v_a_3136_;
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
else
{
lean_dec(v_a_3136_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_box(v___x_3134_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set_tag(v___x_3140_, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
else
{
uint8_t v___x_3176_; uint8_t v___x_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; uint64_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_dec(v_snd_3108_);
v___x_3176_ = 1;
v___x_3177_ = 0;
v___x_3178_ = 2;
v___x_3179_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3179_, 0, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3179_, 1, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3179_, 2, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3179_, 3, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3179_, 4, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3179_, 5, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 6, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 7, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3179_, 8, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 9, v___x_3176_);
lean_ctor_set_uint8(v___x_3179_, 10, v___x_3177_);
lean_ctor_set_uint8(v___x_3179_, 11, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 12, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 13, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 14, v___x_3178_);
lean_ctor_set_uint8(v___x_3179_, 15, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 16, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 17, v___x_3117_);
lean_ctor_set_uint8(v___x_3179_, 18, v___x_3117_);
v___x_3180_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set_uint64(v___x_3181_, sizeof(void*)*1, v___x_3180_);
v___x_3182_ = lean_box(1);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3185_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3187_, 0, v___x_3181_);
lean_ctor_set(v___x_3187_, 1, v___x_3182_);
lean_ctor_set(v___x_3187_, 2, v___x_3184_);
lean_ctor_set(v___x_3187_, 3, v___x_3185_);
lean_ctor_set(v___x_3187_, 4, v___x_3186_);
lean_ctor_set(v___x_3187_, 5, v___x_3183_);
lean_ctor_set(v___x_3187_, 6, v___x_3186_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7 + 1, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7 + 2, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7 + 3, v___x_3112_);
v___x_3188_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3189_ = lean_st_mk_ref(v___x_3188_);
v___x_3190_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3107_, v___x_3187_, v___x_3189_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3187_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___x_3190_);
v___x_3192_ = lean_st_ref_get(v___x_3189_);
lean_dec(v___x_3189_);
lean_dec(v___x_3192_);
v_a_3119_ = v_a_3191_;
goto v___jp_3118_;
}
else
{
lean_dec(v___x_3189_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3193_; 
v_a_3193_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___x_3190_);
v_a_3119_ = v_a_3193_;
goto v___jp_3118_;
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_del_object(v___x_3105_);
v_a_3194_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3190_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3190_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
v___jp_3118_:
{
if (lean_obj_tag(v_a_3119_) == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = lean_box(v_hasTrace_3099_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3120_);
v___x_3122_ = v___x_3105_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
else
{
lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3131_; 
lean_del_object(v___x_3105_);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3119_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v_a_3119_, 0);
lean_dec(v_unused_3132_);
v___x_3125_ = v_a_3119_;
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
else
{
lean_dec(v_a_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = lean_box(v___x_3117_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3127_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
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
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec(v___x_3102_);
lean_dec(v_name_3094_);
v___x_3203_ = lean_box(v_hasTrace_3099_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v_a_3214_; lean_object* v___y_3227_; lean_object* v___y_3228_; uint8_t v_a_3229_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; uint8_t v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_a_3241_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v_a_3245_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v_a_3250_; lean_object* v___y_3260_; lean_object* v___y_3261_; uint8_t v_a_3262_; uint8_t v___y_3266_; uint8_t v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v_a_3270_; uint8_t v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v_a_3275_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v_a_3280_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; 
v_inheritedTraceOptions_3205_ = lean_ctor_get(v___y_3095_, 13);
lean_inc(v_name_3094_);
v___f_3206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3206_, 0, v_name_3094_);
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3208_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3205_, v_options_3098_, v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3405_; uint8_t v___x_3406_; lean_object* v_a_3408_; lean_object* v_a_3421_; 
v___x_3405_ = l_Lean_trace_profiler;
v___x_3406_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3098_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3433_; lean_object* v_env_3434_; lean_object* v___x_3435_; 
lean_dec_ref(v___f_3206_);
lean_dec_ref(v___f_3093_);
v___x_3433_ = lean_st_ref_get(v___y_3096_);
v_env_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc_ref(v_env_3434_);
lean_dec(v___x_3433_);
lean_inc(v_name_3094_);
v___x_3435_ = l_Lean_Meta_declFromEqLikeName(v_env_3434_, v_name_3094_);
if (lean_obj_tag(v___x_3435_) == 1)
{
lean_object* v_val_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3509_; 
v_val_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3509_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_val_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3509_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v___x_3442_; lean_object* v_env_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v_fst_3440_ = lean_ctor_get(v_val_3436_, 0);
lean_inc_n(v_fst_3440_, 2);
v_snd_3441_ = lean_ctor_get(v_val_3436_, 1);
lean_inc_n(v_snd_3441_, 2);
lean_dec(v_val_3436_);
v___x_3442_ = lean_st_ref_get(v___y_3096_);
v_env_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc_ref(v_env_3443_);
lean_dec(v___x_3442_);
v___x_3444_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3443_, v_fst_3440_, v_snd_3441_);
v___x_3445_ = lean_name_eq(v_name_3094_, v___x_3444_);
lean_dec(v___x_3444_);
lean_dec(v_name_3094_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
lean_dec(v_snd_3441_);
lean_dec(v_fst_3440_);
v___x_3446_ = lean_box(v___x_3406_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3446_);
v___x_3448_ = v___x_3438_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
else
{
uint8_t v___x_3450_; 
lean_inc(v_snd_3441_);
v___x_3450_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3441_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3451_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3452_ = lean_string_dec_eq(v_snd_3441_, v___x_3451_);
lean_dec(v_snd_3441_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_dec(v_fst_3440_);
v___x_3453_ = lean_box(v___x_3406_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3453_);
v___x_3455_ = v___x_3438_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
else
{
uint8_t v___x_3457_; uint8_t v___x_3458_; uint8_t v___x_3459_; lean_object* v___x_3460_; uint64_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_del_object(v___x_3438_);
v___x_3457_ = 1;
v___x_3458_ = 0;
v___x_3459_ = 2;
v___x_3460_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3460_, 0, v___x_3406_);
lean_ctor_set_uint8(v___x_3460_, 1, v___x_3406_);
lean_ctor_set_uint8(v___x_3460_, 2, v___x_3406_);
lean_ctor_set_uint8(v___x_3460_, 3, v___x_3406_);
lean_ctor_set_uint8(v___x_3460_, 4, v___x_3406_);
lean_ctor_set_uint8(v___x_3460_, 5, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 6, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 7, v___x_3406_);
lean_ctor_set_uint8(v___x_3460_, 8, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 9, v___x_3457_);
lean_ctor_set_uint8(v___x_3460_, 10, v___x_3458_);
lean_ctor_set_uint8(v___x_3460_, 11, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 12, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 13, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 14, v___x_3459_);
lean_ctor_set_uint8(v___x_3460_, 15, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 16, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 17, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3460_, 18, v_hasTrace_3099_);
v___x_3461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set_uint64(v___x_3462_, sizeof(void*)*1, v___x_3461_);
v___x_3463_ = lean_box(1);
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3466_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3467_ = lean_box(0);
v___x_3468_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3468_, 0, v___x_3462_);
lean_ctor_set(v___x_3468_, 1, v___x_3463_);
lean_ctor_set(v___x_3468_, 2, v___x_3465_);
lean_ctor_set(v___x_3468_, 3, v___x_3466_);
lean_ctor_set(v___x_3468_, 4, v___x_3467_);
lean_ctor_set(v___x_3468_, 5, v___x_3464_);
lean_ctor_set(v___x_3468_, 6, v___x_3467_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7, v___x_3406_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7 + 1, v___x_3406_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7 + 2, v___x_3406_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7 + 3, v_hasTrace_3099_);
v___x_3469_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3470_ = lean_st_mk_ref(v___x_3469_);
v___x_3471_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3440_, v_hasTrace_3099_, v___x_3468_, v___x_3470_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3468_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref(v___x_3471_);
v___x_3473_ = lean_st_ref_get(v___x_3470_);
lean_dec(v___x_3470_);
lean_dec(v___x_3473_);
v_a_3421_ = v_a_3472_;
goto v___jp_3420_;
}
else
{
lean_dec(v___x_3470_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3474_; 
v_a_3474_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3474_);
lean_dec_ref(v___x_3471_);
v_a_3421_ = v_a_3474_;
goto v___jp_3420_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3475_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3471_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3471_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
}
else
{
uint8_t v___x_3483_; uint8_t v___x_3484_; uint8_t v___x_3485_; lean_object* v___x_3486_; uint64_t v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec(v_snd_3441_);
lean_del_object(v___x_3438_);
v___x_3483_ = 1;
v___x_3484_ = 0;
v___x_3485_ = 2;
v___x_3486_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3486_, 0, v___x_3406_);
lean_ctor_set_uint8(v___x_3486_, 1, v___x_3406_);
lean_ctor_set_uint8(v___x_3486_, 2, v___x_3406_);
lean_ctor_set_uint8(v___x_3486_, 3, v___x_3406_);
lean_ctor_set_uint8(v___x_3486_, 4, v___x_3406_);
lean_ctor_set_uint8(v___x_3486_, 5, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 6, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 7, v___x_3406_);
lean_ctor_set_uint8(v___x_3486_, 8, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 9, v___x_3483_);
lean_ctor_set_uint8(v___x_3486_, 10, v___x_3484_);
lean_ctor_set_uint8(v___x_3486_, 11, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 12, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 13, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 14, v___x_3485_);
lean_ctor_set_uint8(v___x_3486_, 15, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 16, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 17, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3486_, 18, v_hasTrace_3099_);
v___x_3487_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3486_);
v___x_3488_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3488_, 0, v___x_3486_);
lean_ctor_set_uint64(v___x_3488_, sizeof(void*)*1, v___x_3487_);
v___x_3489_ = lean_box(1);
v___x_3490_ = lean_unsigned_to_nat(0u);
v___x_3491_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3492_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3493_ = lean_box(0);
v___x_3494_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3494_, 0, v___x_3488_);
lean_ctor_set(v___x_3494_, 1, v___x_3489_);
lean_ctor_set(v___x_3494_, 2, v___x_3491_);
lean_ctor_set(v___x_3494_, 3, v___x_3492_);
lean_ctor_set(v___x_3494_, 4, v___x_3493_);
lean_ctor_set(v___x_3494_, 5, v___x_3490_);
lean_ctor_set(v___x_3494_, 6, v___x_3493_);
lean_ctor_set_uint8(v___x_3494_, sizeof(void*)*7, v___x_3406_);
lean_ctor_set_uint8(v___x_3494_, sizeof(void*)*7 + 1, v___x_3406_);
lean_ctor_set_uint8(v___x_3494_, sizeof(void*)*7 + 2, v___x_3406_);
lean_ctor_set_uint8(v___x_3494_, sizeof(void*)*7 + 3, v_hasTrace_3099_);
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3496_ = lean_st_mk_ref(v___x_3495_);
v___x_3497_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3440_, v___x_3494_, v___x_3496_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3494_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref(v___x_3497_);
v___x_3499_ = lean_st_ref_get(v___x_3496_);
lean_dec(v___x_3496_);
lean_dec(v___x_3499_);
v_a_3408_ = v_a_3498_;
goto v___jp_3407_;
}
else
{
lean_dec(v___x_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3500_; 
v_a_3500_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3500_);
lean_dec_ref(v___x_3497_);
v_a_3408_ = v_a_3500_;
goto v___jp_3407_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
v_a_3501_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3497_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3497_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
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
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec(v___x_3435_);
lean_dec(v_name_3094_);
v___x_3510_ = lean_box(v___x_3406_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
return v___x_3511_;
}
}
else
{
goto v___jp_3289_;
}
v___jp_3407_:
{
if (lean_obj_tag(v_a_3408_) == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_box(v___x_3406_);
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
else
{
lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3418_; 
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3408_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v_a_3408_, 0);
lean_dec(v_unused_3419_);
v___x_3412_ = v_a_3408_;
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
else
{
lean_dec(v_a_3408_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3414_ = lean_box(v_hasTrace_3099_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3414_);
v___x_3416_ = v___x_3412_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
v___jp_3420_:
{
if (lean_obj_tag(v_a_3421_) == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_box(v___x_3406_);
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
else
{
lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
v_isSharedCheck_3431_ = !lean_is_exclusive(v_a_3421_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v_a_3421_, 0);
lean_dec(v_unused_3432_);
v___x_3425_ = v_a_3421_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_dec(v_a_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_box(v_hasTrace_3099_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3427_);
v___x_3429_ = v___x_3425_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
goto v___jp_3289_;
}
v___jp_3211_:
{
lean_object* v___x_3215_; double v___x_3216_; double v___x_3217_; double v___x_3218_; double v___x_3219_; double v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3215_ = lean_io_mono_nanos_now();
v___x_3216_ = lean_float_of_nat(v___y_3213_);
v___x_3217_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3218_ = lean_float_div(v___x_3216_, v___x_3217_);
v___x_3219_ = lean_float_of_nat(v___x_3215_);
v___x_3220_ = lean_float_div(v___x_3219_, v___x_3217_);
v___x_3221_ = lean_box_float(v___x_3218_);
v___x_3222_ = lean_box_float(v___x_3220_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v_a_3214_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3207_, v_hasTrace_3099_, v___x_3208_, v_options_3098_, v___x_3210_, v___y_3212_, v___f_3206_, v___x_3224_, v___y_3095_, v___y_3096_);
return v___x_3225_;
}
v___jp_3226_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_box(v_a_3229_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
v___y_3212_ = v___y_3227_;
v___y_3213_ = v___y_3228_;
v_a_3214_ = v___x_3231_;
goto v___jp_3211_;
}
v___jp_3232_:
{
if (lean_obj_tag(v_a_3236_) == 0)
{
v___y_3227_ = v___y_3234_;
v___y_3228_ = v___y_3235_;
v_a_3229_ = v___y_3233_;
goto v___jp_3226_;
}
else
{
lean_dec_ref(v_a_3236_);
v___y_3227_ = v___y_3234_;
v___y_3228_ = v___y_3235_;
v_a_3229_ = v_hasTrace_3099_;
goto v___jp_3226_;
}
}
v___jp_3237_:
{
if (lean_obj_tag(v_a_3241_) == 0)
{
v___y_3227_ = v___y_3239_;
v___y_3228_ = v___y_3240_;
v_a_3229_ = v___y_3238_;
goto v___jp_3226_;
}
else
{
lean_dec_ref(v_a_3241_);
v___y_3227_ = v___y_3239_;
v___y_3228_ = v___y_3240_;
v_a_3229_ = v_hasTrace_3099_;
goto v___jp_3226_;
}
}
v___jp_3242_:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_a_3245_);
v___y_3212_ = v___y_3243_;
v___y_3213_ = v___y_3244_;
v_a_3214_ = v___x_3246_;
goto v___jp_3211_;
}
v___jp_3247_:
{
lean_object* v___x_3251_; double v___x_3252_; double v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3251_ = lean_io_get_num_heartbeats();
v___x_3252_ = lean_float_of_nat(v___y_3249_);
v___x_3253_ = lean_float_of_nat(v___x_3251_);
v___x_3254_ = lean_box_float(v___x_3252_);
v___x_3255_ = lean_box_float(v___x_3253_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v_a_3250_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3207_, v_hasTrace_3099_, v___x_3208_, v_options_3098_, v___x_3210_, v___y_3248_, v___f_3206_, v___x_3257_, v___y_3095_, v___y_3096_);
return v___x_3258_;
}
v___jp_3259_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_box(v_a_3262_);
v___x_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
v___y_3248_ = v___y_3261_;
v___y_3249_ = v___y_3260_;
v_a_3250_ = v___x_3264_;
goto v___jp_3247_;
}
v___jp_3265_:
{
if (lean_obj_tag(v_a_3270_) == 0)
{
v___y_3260_ = v___y_3269_;
v___y_3261_ = v___y_3268_;
v_a_3262_ = v___y_3266_;
goto v___jp_3259_;
}
else
{
lean_dec_ref(v_a_3270_);
v___y_3260_ = v___y_3269_;
v___y_3261_ = v___y_3268_;
v_a_3262_ = v___y_3267_;
goto v___jp_3259_;
}
}
v___jp_3271_:
{
if (lean_obj_tag(v_a_3275_) == 0)
{
uint8_t v___x_3276_; 
v___x_3276_ = 0;
v___y_3260_ = v___y_3274_;
v___y_3261_ = v___y_3273_;
v_a_3262_ = v___x_3276_;
goto v___jp_3259_;
}
else
{
lean_dec_ref(v_a_3275_);
v___y_3260_ = v___y_3274_;
v___y_3261_ = v___y_3273_;
v_a_3262_ = v___y_3272_;
goto v___jp_3259_;
}
}
v___jp_3277_:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_a_3280_);
v___y_3248_ = v___y_3279_;
v___y_3249_ = v___y_3278_;
v_a_3250_ = v___x_3281_;
goto v___jp_3247_;
}
v___jp_3282_:
{
if (lean_obj_tag(v___y_3285_) == 0)
{
lean_object* v_a_3286_; uint8_t v___x_3287_; 
v_a_3286_ = lean_ctor_get(v___y_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___y_3285_);
v___x_3287_ = lean_unbox(v_a_3286_);
lean_dec(v_a_3286_);
v___y_3260_ = v___y_3284_;
v___y_3261_ = v___y_3283_;
v_a_3262_ = v___x_3287_;
goto v___jp_3259_;
}
else
{
lean_object* v_a_3288_; 
v_a_3288_ = lean_ctor_get(v___y_3285_, 0);
lean_inc(v_a_3288_);
lean_dec_ref(v___y_3285_);
v___y_3278_ = v___y_3284_;
v___y_3279_ = v___y_3283_;
v_a_3280_ = v_a_3288_;
goto v___jp_3277_;
}
}
v___jp_3289_:
{
lean_object* v___x_3290_; lean_object* v_a_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3290_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3096_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref(v___x_3290_);
v___x_3292_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3293_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3098_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v_env_3296_; lean_object* v___x_3297_; 
lean_dec_ref(v___f_3093_);
v___x_3294_ = lean_io_mono_nanos_now();
v___x_3295_ = lean_st_ref_get(v___y_3096_);
v_env_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_ref(v_env_3296_);
lean_dec(v___x_3295_);
lean_inc(v_name_3094_);
v___x_3297_ = l_Lean_Meta_declFromEqLikeName(v_env_3296_, v_name_3094_);
if (lean_obj_tag(v___x_3297_) == 1)
{
lean_object* v_val_3298_; lean_object* v_fst_3299_; lean_object* v_snd_3300_; lean_object* v___x_3301_; lean_object* v_env_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v_val_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_val_3298_);
lean_dec_ref(v___x_3297_);
v_fst_3299_ = lean_ctor_get(v_val_3298_, 0);
lean_inc_n(v_fst_3299_, 2);
v_snd_3300_ = lean_ctor_get(v_val_3298_, 1);
lean_inc_n(v_snd_3300_, 2);
lean_dec(v_val_3298_);
v___x_3301_ = lean_st_ref_get(v___y_3096_);
v_env_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc_ref(v_env_3302_);
lean_dec(v___x_3301_);
v___x_3303_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3302_, v_fst_3299_, v_snd_3300_);
v___x_3304_ = lean_name_eq(v_name_3094_, v___x_3303_);
lean_dec(v___x_3303_);
lean_dec(v_name_3094_);
if (v___x_3304_ == 0)
{
lean_dec(v_snd_3300_);
lean_dec(v_fst_3299_);
v___y_3227_ = v_a_3291_;
v___y_3228_ = v___x_3294_;
v_a_3229_ = v___x_3293_;
goto v___jp_3226_;
}
else
{
uint8_t v___x_3305_; 
lean_inc(v_snd_3300_);
v___x_3305_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3300_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3307_ = lean_string_dec_eq(v_snd_3300_, v___x_3306_);
lean_dec(v_snd_3300_);
if (v___x_3307_ == 0)
{
lean_dec(v_fst_3299_);
v___y_3227_ = v_a_3291_;
v___y_3228_ = v___x_3294_;
v_a_3229_ = v___x_3293_;
goto v___jp_3226_;
}
else
{
uint8_t v___x_3308_; uint8_t v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; uint64_t v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3308_ = 1;
v___x_3309_ = 0;
v___x_3310_ = 2;
v___x_3311_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3311_, 0, v___x_3293_);
lean_ctor_set_uint8(v___x_3311_, 1, v___x_3293_);
lean_ctor_set_uint8(v___x_3311_, 2, v___x_3293_);
lean_ctor_set_uint8(v___x_3311_, 3, v___x_3293_);
lean_ctor_set_uint8(v___x_3311_, 4, v___x_3293_);
lean_ctor_set_uint8(v___x_3311_, 5, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 6, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 7, v___x_3293_);
lean_ctor_set_uint8(v___x_3311_, 8, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 9, v___x_3308_);
lean_ctor_set_uint8(v___x_3311_, 10, v___x_3309_);
lean_ctor_set_uint8(v___x_3311_, 11, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 12, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 13, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 14, v___x_3310_);
lean_ctor_set_uint8(v___x_3311_, 15, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 16, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 17, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3311_, 18, v_hasTrace_3099_);
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
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7, v___x_3293_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7 + 1, v___x_3293_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7 + 2, v___x_3293_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7 + 3, v_hasTrace_3099_);
v___x_3320_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3321_ = lean_st_mk_ref(v___x_3320_);
v___x_3322_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3299_, v_hasTrace_3099_, v___x_3319_, v___x_3321_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3319_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref(v___x_3322_);
v___x_3324_ = lean_st_ref_get(v___x_3321_);
lean_dec(v___x_3321_);
lean_dec(v___x_3324_);
v___y_3238_ = v___x_3293_;
v___y_3239_ = v_a_3291_;
v___y_3240_ = v___x_3294_;
v_a_3241_ = v_a_3323_;
goto v___jp_3237_;
}
else
{
lean_dec(v___x_3321_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3325_; 
v_a_3325_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3322_);
v___y_3238_ = v___x_3293_;
v___y_3239_ = v_a_3291_;
v___y_3240_ = v___x_3294_;
v_a_3241_ = v_a_3325_;
goto v___jp_3237_;
}
else
{
lean_object* v_a_3326_; 
v_a_3326_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3326_);
lean_dec_ref(v___x_3322_);
v___y_3243_ = v_a_3291_;
v___y_3244_ = v___x_3294_;
v_a_3245_ = v_a_3326_;
goto v___jp_3242_;
}
}
}
}
else
{
uint8_t v___x_3327_; uint8_t v___x_3328_; uint8_t v___x_3329_; lean_object* v___x_3330_; uint64_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec(v_snd_3300_);
v___x_3327_ = 1;
v___x_3328_ = 0;
v___x_3329_ = 2;
v___x_3330_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3330_, 0, v___x_3293_);
lean_ctor_set_uint8(v___x_3330_, 1, v___x_3293_);
lean_ctor_set_uint8(v___x_3330_, 2, v___x_3293_);
lean_ctor_set_uint8(v___x_3330_, 3, v___x_3293_);
lean_ctor_set_uint8(v___x_3330_, 4, v___x_3293_);
lean_ctor_set_uint8(v___x_3330_, 5, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 6, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 7, v___x_3293_);
lean_ctor_set_uint8(v___x_3330_, 8, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 9, v___x_3327_);
lean_ctor_set_uint8(v___x_3330_, 10, v___x_3328_);
lean_ctor_set_uint8(v___x_3330_, 11, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 12, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 13, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 14, v___x_3329_);
lean_ctor_set_uint8(v___x_3330_, 15, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 16, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 17, v_hasTrace_3099_);
lean_ctor_set_uint8(v___x_3330_, 18, v_hasTrace_3099_);
v___x_3331_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3330_);
v___x_3332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3332_, 0, v___x_3330_);
lean_ctor_set_uint64(v___x_3332_, sizeof(void*)*1, v___x_3331_);
v___x_3333_ = lean_box(1);
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3338_, 0, v___x_3332_);
lean_ctor_set(v___x_3338_, 1, v___x_3333_);
lean_ctor_set(v___x_3338_, 2, v___x_3335_);
lean_ctor_set(v___x_3338_, 3, v___x_3336_);
lean_ctor_set(v___x_3338_, 4, v___x_3337_);
lean_ctor_set(v___x_3338_, 5, v___x_3334_);
lean_ctor_set(v___x_3338_, 6, v___x_3337_);
lean_ctor_set_uint8(v___x_3338_, sizeof(void*)*7, v___x_3293_);
lean_ctor_set_uint8(v___x_3338_, sizeof(void*)*7 + 1, v___x_3293_);
lean_ctor_set_uint8(v___x_3338_, sizeof(void*)*7 + 2, v___x_3293_);
lean_ctor_set_uint8(v___x_3338_, sizeof(void*)*7 + 3, v_hasTrace_3099_);
v___x_3339_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3340_ = lean_st_mk_ref(v___x_3339_);
v___x_3341_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3299_, v___x_3338_, v___x_3340_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3338_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref(v___x_3341_);
v___x_3343_ = lean_st_ref_get(v___x_3340_);
lean_dec(v___x_3340_);
lean_dec(v___x_3343_);
v___y_3233_ = v___x_3293_;
v___y_3234_ = v_a_3291_;
v___y_3235_ = v___x_3294_;
v_a_3236_ = v_a_3342_;
goto v___jp_3232_;
}
else
{
lean_dec(v___x_3340_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3344_; 
v_a_3344_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3344_);
lean_dec_ref(v___x_3341_);
v___y_3233_ = v___x_3293_;
v___y_3234_ = v_a_3291_;
v___y_3235_ = v___x_3294_;
v_a_3236_ = v_a_3344_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3345_; 
v_a_3345_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3345_);
lean_dec_ref(v___x_3341_);
v___y_3243_ = v_a_3291_;
v___y_3244_ = v___x_3294_;
v_a_3245_ = v_a_3345_;
goto v___jp_3242_;
}
}
}
}
}
else
{
lean_dec(v___x_3297_);
lean_dec(v_name_3094_);
v___y_3227_ = v_a_3291_;
v___y_3228_ = v___x_3294_;
v_a_3229_ = v___x_3293_;
goto v___jp_3226_;
}
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v_env_3348_; lean_object* v___x_3349_; 
v___x_3346_ = lean_io_get_num_heartbeats();
v___x_3347_ = lean_st_ref_get(v___y_3096_);
v_env_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc_ref(v_env_3348_);
lean_dec(v___x_3347_);
lean_inc(v_name_3094_);
v___x_3349_ = l_Lean_Meta_declFromEqLikeName(v_env_3348_, v_name_3094_);
if (lean_obj_tag(v___x_3349_) == 1)
{
lean_object* v_val_3350_; lean_object* v_fst_3351_; lean_object* v_snd_3352_; lean_object* v___x_3353_; lean_object* v_env_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_val_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_val_3350_);
lean_dec_ref(v___x_3349_);
v_fst_3351_ = lean_ctor_get(v_val_3350_, 0);
lean_inc_n(v_fst_3351_, 2);
v_snd_3352_ = lean_ctor_get(v_val_3350_, 1);
lean_inc_n(v_snd_3352_, 2);
lean_dec(v_val_3350_);
v___x_3353_ = lean_st_ref_get(v___y_3096_);
v_env_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_ref(v_env_3354_);
lean_dec(v___x_3353_);
v___x_3355_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3354_, v_fst_3351_, v_snd_3352_);
v___x_3356_ = lean_name_eq(v_name_3094_, v___x_3355_);
lean_dec(v___x_3355_);
lean_dec(v_name_3094_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec(v_snd_3352_);
lean_dec(v_fst_3351_);
v___x_3357_ = lean_box(0);
lean_inc(v___y_3096_);
lean_inc_ref(v___y_3095_);
v___x_3358_ = lean_apply_4(v___f_3093_, v___x_3357_, v___y_3095_, v___y_3096_, lean_box(0));
v___y_3283_ = v_a_3291_;
v___y_3284_ = v___x_3346_;
v___y_3285_ = v___x_3358_;
goto v___jp_3282_;
}
else
{
uint8_t v___x_3359_; 
lean_inc(v_snd_3352_);
v___x_3359_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3352_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3361_ = lean_string_dec_eq(v_snd_3352_, v___x_3360_);
lean_dec(v_snd_3352_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec(v_fst_3351_);
v___x_3362_ = lean_box(0);
lean_inc(v___y_3096_);
lean_inc_ref(v___y_3095_);
v___x_3363_ = lean_apply_4(v___f_3093_, v___x_3362_, v___y_3095_, v___y_3096_, lean_box(0));
v___y_3283_ = v_a_3291_;
v___y_3284_ = v___x_3346_;
v___y_3285_ = v___x_3363_;
goto v___jp_3282_;
}
else
{
uint8_t v___x_3364_; uint8_t v___x_3365_; uint8_t v___x_3366_; lean_object* v___x_3367_; uint64_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec_ref(v___f_3093_);
v___x_3364_ = 1;
v___x_3365_ = 0;
v___x_3366_ = 2;
v___x_3367_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3367_, 0, v___x_3359_);
lean_ctor_set_uint8(v___x_3367_, 1, v___x_3359_);
lean_ctor_set_uint8(v___x_3367_, 2, v___x_3359_);
lean_ctor_set_uint8(v___x_3367_, 3, v___x_3359_);
lean_ctor_set_uint8(v___x_3367_, 4, v___x_3359_);
lean_ctor_set_uint8(v___x_3367_, 5, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 6, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 7, v___x_3359_);
lean_ctor_set_uint8(v___x_3367_, 8, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 9, v___x_3364_);
lean_ctor_set_uint8(v___x_3367_, 10, v___x_3365_);
lean_ctor_set_uint8(v___x_3367_, 11, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 12, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 13, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 14, v___x_3366_);
lean_ctor_set_uint8(v___x_3367_, 15, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 16, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 17, v___x_3293_);
lean_ctor_set_uint8(v___x_3367_, 18, v___x_3293_);
v___x_3368_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3367_);
v___x_3369_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set_uint64(v___x_3369_, sizeof(void*)*1, v___x_3368_);
v___x_3370_ = lean_box(1);
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3375_, 0, v___x_3369_);
lean_ctor_set(v___x_3375_, 1, v___x_3370_);
lean_ctor_set(v___x_3375_, 2, v___x_3372_);
lean_ctor_set(v___x_3375_, 3, v___x_3373_);
lean_ctor_set(v___x_3375_, 4, v___x_3374_);
lean_ctor_set(v___x_3375_, 5, v___x_3371_);
lean_ctor_set(v___x_3375_, 6, v___x_3374_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7, v___x_3359_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7 + 1, v___x_3359_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7 + 2, v___x_3359_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7 + 3, v___x_3293_);
v___x_3376_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3377_ = lean_st_mk_ref(v___x_3376_);
v___x_3378_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3351_, v___x_3293_, v___x_3375_, v___x_3377_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = lean_st_ref_get(v___x_3377_);
lean_dec(v___x_3377_);
lean_dec(v___x_3380_);
v___y_3266_ = v___x_3359_;
v___y_3267_ = v___x_3293_;
v___y_3268_ = v_a_3291_;
v___y_3269_ = v___x_3346_;
v_a_3270_ = v_a_3379_;
goto v___jp_3265_;
}
else
{
lean_dec(v___x_3377_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3381_; 
v_a_3381_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3378_);
v___y_3266_ = v___x_3359_;
v___y_3267_ = v___x_3293_;
v___y_3268_ = v_a_3291_;
v___y_3269_ = v___x_3346_;
v_a_3270_ = v_a_3381_;
goto v___jp_3265_;
}
else
{
lean_object* v_a_3382_; 
v_a_3382_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3378_);
v___y_3278_ = v___x_3346_;
v___y_3279_ = v_a_3291_;
v_a_3280_ = v_a_3382_;
goto v___jp_3277_;
}
}
}
}
else
{
uint8_t v___x_3383_; uint8_t v___x_3384_; uint8_t v___x_3385_; uint8_t v___x_3386_; lean_object* v___x_3387_; uint64_t v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec(v_snd_3352_);
lean_dec_ref(v___f_3093_);
v___x_3383_ = 0;
v___x_3384_ = 1;
v___x_3385_ = 0;
v___x_3386_ = 2;
v___x_3387_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3387_, 0, v___x_3383_);
lean_ctor_set_uint8(v___x_3387_, 1, v___x_3383_);
lean_ctor_set_uint8(v___x_3387_, 2, v___x_3383_);
lean_ctor_set_uint8(v___x_3387_, 3, v___x_3383_);
lean_ctor_set_uint8(v___x_3387_, 4, v___x_3383_);
lean_ctor_set_uint8(v___x_3387_, 5, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 6, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 7, v___x_3383_);
lean_ctor_set_uint8(v___x_3387_, 8, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 9, v___x_3384_);
lean_ctor_set_uint8(v___x_3387_, 10, v___x_3385_);
lean_ctor_set_uint8(v___x_3387_, 11, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 12, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 13, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 14, v___x_3386_);
lean_ctor_set_uint8(v___x_3387_, 15, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 16, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 17, v___x_3293_);
lean_ctor_set_uint8(v___x_3387_, 18, v___x_3293_);
v___x_3388_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3387_);
v___x_3389_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set_uint64(v___x_3389_, sizeof(void*)*1, v___x_3388_);
v___x_3390_ = lean_box(1);
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3394_ = lean_box(0);
v___x_3395_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3395_, 0, v___x_3389_);
lean_ctor_set(v___x_3395_, 1, v___x_3390_);
lean_ctor_set(v___x_3395_, 2, v___x_3392_);
lean_ctor_set(v___x_3395_, 3, v___x_3393_);
lean_ctor_set(v___x_3395_, 4, v___x_3394_);
lean_ctor_set(v___x_3395_, 5, v___x_3391_);
lean_ctor_set(v___x_3395_, 6, v___x_3394_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7, v___x_3383_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7 + 1, v___x_3383_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7 + 2, v___x_3383_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7 + 3, v___x_3293_);
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3397_ = lean_st_mk_ref(v___x_3396_);
v___x_3398_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3351_, v___x_3395_, v___x_3397_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3395_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = lean_st_ref_get(v___x_3397_);
lean_dec(v___x_3397_);
lean_dec(v___x_3400_);
v___y_3272_ = v___x_3293_;
v___y_3273_ = v_a_3291_;
v___y_3274_ = v___x_3346_;
v_a_3275_ = v_a_3399_;
goto v___jp_3271_;
}
else
{
lean_dec(v___x_3397_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3401_; 
v_a_3401_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3401_);
lean_dec_ref(v___x_3398_);
v___y_3272_ = v___x_3293_;
v___y_3273_ = v_a_3291_;
v___y_3274_ = v___x_3346_;
v_a_3275_ = v_a_3401_;
goto v___jp_3271_;
}
else
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v___x_3398_);
v___y_3278_ = v___x_3346_;
v___y_3279_ = v_a_3291_;
v_a_3280_ = v_a_3402_;
goto v___jp_3277_;
}
}
}
}
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec(v___x_3349_);
lean_dec(v_name_3094_);
v___x_3403_ = lean_box(0);
lean_inc(v___y_3096_);
lean_inc_ref(v___y_3095_);
v___x_3404_ = lean_apply_4(v___f_3093_, v___x_3403_, v___y_3095_, v___y_3096_, lean_box(0));
v___y_3283_ = v_a_3291_;
v___y_3284_ = v___x_3346_;
v___y_3285_ = v___x_3404_;
goto v___jp_3282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3512_, lean_object* v_name_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3512_, v_name_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = lean_unsigned_to_nat(3137104340u);
v___x_3562_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3563_ = l_Lean_Name_num___override(v___x_3562_, v___x_3561_);
return v___x_3563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3566_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3567_ = l_Lean_Name_str___override(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3570_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3571_ = l_Lean_Name_str___override(v___x_3570_, v___x_3569_);
return v___x_3571_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3572_ = lean_unsigned_to_nat(2u);
v___x_3573_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3574_ = l_Lean_Name_num___override(v___x_3573_, v___x_3572_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3576_; lean_object* v___x_3577_; 
v___f_3576_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3577_ = l_Lean_registerReservedNameAction(v___f_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec_ref(v___x_3577_);
v___x_3578_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3579_ = 0;
v___x_3580_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3581_ = l_Lean_registerTraceClass(v___x_3578_, v___x_3579_, v___x_3580_);
return v___x_3581_;
}
else
{
return v___x_3577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b1_3584_, lean_object* v_x_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_3585_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b1_3590_, lean_object* v_x_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b1_3590_, v_x_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
return v_res_3595_;
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
