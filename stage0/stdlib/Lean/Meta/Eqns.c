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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Array_instInhabited___redArg();
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_backward_defeqAttrib_useBackward;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedEqnsExtState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedEqnsExtState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eqnsExt"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 82, 168, 170, 186, 217, 249, 198)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqnsExt;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_withEqnOptions___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_withEqnOptions___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_withEqnOptions___redArg___closed__6;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Meta.Eqns"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "_private.Lean.Meta.Eqns.0.Lean.Meta.registerEqnThms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "equation theorem `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is already registered for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4;
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
lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; 
v___f_172_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_174_ = lean_box(1);
v___x_175_ = 0;
v___x_176_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_173_, v___x_174_, v___x_175_, v___f_172_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object* v_init_179_, lean_object* v_t_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_179_, v_t_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_182_, lean_object* v_t_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_182_, v_t_183_);
lean_dec(v_t_183_);
return v_res_184_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = lean_string_utf8_byte_size(v_s_191_);
v___x_193_ = lean_unsigned_to_nat(3u);
v___x_194_ = lean_nat_dec_le(v___x_193_, v___x_192_);
if (v___x_194_ == 0)
{
lean_dec_ref(v_s_191_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_string_memcmp(v_s_191_, v___x_195_, v___x_196_, v___x_196_, v___x_193_);
if (v___x_197_ == 0)
{
lean_dec_ref(v_s_191_);
return v___x_197_;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
lean_inc_ref(v_s_191_);
v___x_198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_198_, 0, v_s_191_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_192_);
v___x_199_ = l_String_Slice_Pos_nextn(v___x_198_, v___x_196_, v___x_193_);
lean_dec_ref_known(v___x_198_, 3);
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v_s_191_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
lean_ctor_set(v___x_200_, 2, v___x_192_);
v___x_201_ = l_String_Slice_isNat(v___x_200_);
lean_dec_ref_known(v___x_200_, 3);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_209_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_211_ = lean_string_dec_eq(v_s_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_213_ = lean_string_dec_eq(v_s_209_, v___x_212_);
if (v___x_213_ == 0)
{
uint8_t v___x_214_; 
v___x_214_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_209_);
return v___x_214_;
}
else
{
lean_dec_ref(v_s_209_);
return v___x_213_;
}
}
else
{
lean_dec_ref(v_s_209_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Lean_Meta_isEqnLikeSuffix(v_s_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_221_, lean_object* v_env_222_, uint8_t v___x_223_, lean_object* v_as_x27_224_, lean_object* v_b_225_){
_start:
{
if (lean_obj_tag(v_as_x27_224_) == 0)
{
lean_dec_ref(v_env_222_);
lean_dec_ref(v_str_221_);
lean_inc_ref(v_b_225_);
return v_b_225_;
}
else
{
lean_object* v_head_226_; lean_object* v_tail_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___y_231_; uint8_t v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_head_226_ = lean_ctor_get(v_as_x27_224_, 0);
v_tail_227_ = lean_ctor_get(v_as_x27_224_, 1);
v___x_228_ = lean_box(0);
v___x_229_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_237_ = 0;
lean_inc_ref(v_env_222_);
v___x_238_ = l_Lean_Environment_setExporting(v_env_222_, v___x_237_);
lean_inc(v_head_226_);
v___x_239_ = l_Lean_Environment_isSafeDefinition(v___x_238_, v_head_226_);
if (v___x_239_ == 0)
{
v___y_231_ = v___x_239_;
goto v___jp_230_;
}
else
{
uint8_t v___x_240_; 
lean_inc(v_head_226_);
lean_inc_ref(v_env_222_);
v___x_240_ = l_Lean_Meta_isMatcherCore(v_env_222_, v_head_226_);
if (v___x_240_ == 0)
{
v___y_231_ = v___x_223_;
goto v___jp_230_;
}
else
{
v_as_x27_224_ = v_tail_227_;
v_b_225_ = v___x_229_;
goto _start;
}
}
v___jp_230_:
{
if (v___y_231_ == 0)
{
v_as_x27_224_ = v_tail_227_;
v_b_225_ = v___x_229_;
goto _start;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref(v_env_222_);
lean_inc(v_head_226_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_head_226_);
lean_ctor_set(v___x_233_, 1, v_str_221_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_228_);
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_242_, lean_object* v_env_243_, lean_object* v___x_244_, lean_object* v_as_x27_245_, lean_object* v_b_246_){
_start:
{
uint8_t v___x_616__boxed_247_; lean_object* v_res_248_; 
v___x_616__boxed_247_ = lean_unbox(v___x_244_);
v_res_248_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_242_, v_env_243_, v___x_616__boxed_247_, v_as_x27_245_, v_b_246_);
lean_dec_ref(v_b_246_);
lean_dec(v_as_x27_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_249_, lean_object* v_name_250_){
_start:
{
if (lean_obj_tag(v_name_250_) == 1)
{
lean_object* v_pre_251_; lean_object* v_str_252_; uint8_t v___x_253_; 
v_pre_251_ = lean_ctor_get(v_name_250_, 0);
lean_inc(v_pre_251_);
v_str_252_ = lean_ctor_get(v_name_250_, 1);
lean_inc_ref_n(v_str_252_, 2);
lean_dec_ref_known(v_name_250_, 2);
v___x_253_ = l_Lean_Meta_isEqnLikeSuffix(v_str_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec_ref(v_str_252_);
lean_dec(v_pre_251_);
lean_dec_ref(v_env_249_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_fst_262_; 
lean_inc(v_pre_251_);
v___x_255_ = l_Lean_privateToUserName(v_pre_251_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v_pre_251_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_261_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_252_, v_env_249_, v___x_253_, v___x_258_, v___x_260_);
lean_dec_ref_known(v___x_258_, 2);
v_fst_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_fst_262_);
lean_dec_ref(v___x_261_);
if (lean_obj_tag(v_fst_262_) == 0)
{
return v___x_259_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v_fst_262_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v_fst_262_, 1);
return v_val_263_;
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_name_250_);
lean_dec_ref(v_env_249_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_265_, lean_object* v_env_266_, uint8_t v___x_267_, lean_object* v_as_268_, lean_object* v_as_x27_269_, lean_object* v_b_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_265_, v_env_266_, v___x_267_, v_as_x27_269_, v_b_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_273_, lean_object* v_env_274_, lean_object* v___x_275_, lean_object* v_as_276_, lean_object* v_as_x27_277_, lean_object* v_b_278_, lean_object* v_a_279_){
_start:
{
uint8_t v___x_687__boxed_280_; lean_object* v_res_281_; 
v___x_687__boxed_280_ = lean_unbox(v___x_275_);
v_res_281_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_273_, v_env_274_, v___x_687__boxed_280_, v_as_276_, v_as_x27_277_, v_b_278_, v_a_279_);
lean_dec_ref(v_b_278_);
lean_dec(v_as_x27_277_);
lean_dec(v_as_276_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_282_, lean_object* v_declName_283_, lean_object* v_suffix_284_){
_start:
{
uint8_t v_isExposed_285_; lean_object* v_name_286_; 
lean_inc(v_declName_283_);
lean_inc_ref(v_env_282_);
v_isExposed_285_ = l_Lean_Environment_hasExposedBody(v_env_282_, v_declName_283_);
v_name_286_ = l_Lean_Name_str___override(v_declName_283_, v_suffix_284_);
if (v_isExposed_285_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_mkPrivateName(v_env_282_, v_name_286_);
lean_dec_ref(v_env_282_);
return v___x_287_;
}
else
{
lean_dec_ref(v_env_282_);
return v_name_286_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_288_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
lean_ctor_set(v___x_293_, 3, v___x_292_);
lean_ctor_set(v___x_293_, 4, v___x_291_);
lean_ctor_set(v___x_293_, 5, v___x_291_);
lean_ctor_set(v___x_293_, 6, v___x_291_);
lean_ctor_set(v___x_293_, 7, v___x_291_);
lean_ctor_set(v___x_293_, 8, v___x_291_);
lean_ctor_set(v___x_293_, 9, v___x_291_);
lean_ctor_set(v___x_293_, 10, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(32u);
v___x_295_ = lean_mk_empty_array_with_capacity(v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_297_ = ((size_t)5ULL);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_unsigned_to_nat(32u);
v___x_300_ = lean_mk_empty_array_with_capacity(v___x_299_);
v___x_301_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_302_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_298_);
lean_ctor_set(v___x_302_, 3, v___x_298_);
lean_ctor_set_usize(v___x_302_, 4, v___x_297_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_box(1);
v___x_304_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_305_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_toCold_312_; lean_object* v_env_313_; lean_object* v_options_314_; uint8_t v___x_315_; lean_object* v_env_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_toCold_312_ = lean_ctor_get(v___y_308_, 0);
v_env_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_313_);
lean_dec(v___x_311_);
v_options_314_ = lean_ctor_get(v_toCold_312_, 2);
v___x_315_ = 0;
v_env_316_ = l_Lean_Environment_setRecordingDeps(v_env_313_, v___x_315_);
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_314_);
v___x_319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_319_, 0, v_env_316_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v_options_314_);
v___x_320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_msgData_307_);
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
lean_object* v_reservedName_384_; lean_object* v___x_385_; lean_object* v_env_386_; uint8_t v___x_387_; uint8_t v___x_388_; 
lean_inc(v_declName_379_);
v_reservedName_384_ = l_Lean_Name_str___override(v_declName_379_, v_suffix_380_);
v___x_385_ = lean_st_ref_get(v___y_382_);
v_env_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_env_386_);
lean_dec(v___x_385_);
v___x_387_ = 1;
lean_inc(v_reservedName_384_);
v___x_388_ = l_Lean_Environment_contains(v_env_386_, v_reservedName_384_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_reservedName_384_);
lean_dec(v_declName_379_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_379_, v_reservedName_384_, v___y_381_, v___y_382_);
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
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object* v___x_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v___x_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_526_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_529_; lean_object* v___f_530_; 
v___x_529_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_530_, 0, v___x_529_);
return v___f_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; 
v___f_537_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_);
v___x_538_ = lean_box(0);
v___x_539_ = lean_box(1);
v___x_540_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_));
v___x_541_ = 0;
v___x_542_ = 1;
v___x_543_ = l_Lean_registerEnvExtension___redArg(v___f_537_, v___x_538_, v___x_539_, v___x_540_, v___x_541_, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_546_, lean_object* v_opt_547_){
_start:
{
lean_object* v_name_548_; lean_object* v_defValue_549_; lean_object* v_map_550_; lean_object* v___x_551_; 
v_name_548_ = lean_ctor_get(v_opt_547_, 0);
v_defValue_549_ = lean_ctor_get(v_opt_547_, 1);
v_map_550_ = lean_ctor_get(v_opts_546_, 0);
v___x_551_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_550_, v_name_548_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_inc(v_defValue_549_);
return v_defValue_549_;
}
else
{
lean_object* v_val_552_; 
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_551_, 1);
if (lean_obj_tag(v_val_552_) == 3)
{
lean_object* v_v_553_; 
v_v_553_ = lean_ctor_get(v_val_552_, 0);
lean_inc(v_v_553_);
lean_dec_ref_known(v_val_552_, 1);
return v_v_553_;
}
else
{
lean_dec(v_val_552_);
lean_inc(v_defValue_549_);
return v_defValue_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_554_, lean_object* v_opt_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_554_, v_opt_555_);
lean_dec_ref(v_opt_555_);
lean_dec_ref(v_opts_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_){
_start:
{
lean_object* v_a_565_; uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_lt(v_i_562_, v_sz_561_);
if (v___x_569_ == 0)
{
return v_b_563_;
}
else
{
lean_object* v_a_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v_map_573_; uint8_t v_hasTrace_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_587_; 
v_a_570_ = lean_array_uget_borrowed(v_as_560_, v_i_562_);
v_fst_571_ = lean_ctor_get(v_a_570_, 0);
v_snd_572_ = lean_ctor_get(v_a_570_, 1);
v_map_573_ = lean_ctor_get(v_b_563_, 0);
v_hasTrace_574_ = lean_ctor_get_uint8(v_b_563_, sizeof(void*)*1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_b_563_);
if (v_isSharedCheck_587_ == 0)
{
v___x_576_ = v_b_563_;
v_isShared_577_ = v_isSharedCheck_587_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_map_573_);
lean_dec(v_b_563_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_587_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; 
lean_inc(v_snd_572_);
lean_inc(v_fst_571_);
v___x_578_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_571_, v_snd_572_, v_map_573_);
if (v_hasTrace_574_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_582_; 
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_580_ = l_Lean_Name_isPrefixOf(v___x_579_, v_fst_571_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_578_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*1, v___x_580_);
v_a_565_ = v___x_582_;
goto v___jp_564_;
}
}
else
{
lean_object* v___x_585_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_585_ = v___x_576_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_586_, sizeof(void*)*1, v_hasTrace_574_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
v_a_565_ = v___x_585_;
goto v___jp_564_;
}
}
}
}
v___jp_564_:
{
size_t v___x_566_; size_t v___x_567_; 
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_i_562_, v___x_566_);
v_i_562_ = v___x_567_;
v_b_563_ = v_a_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_588_, lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_b_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_593_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_588_, v_sz_boxed_592_, v_i_boxed_593_, v_b_591_);
lean_dec_ref(v_as_588_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_595_, lean_object* v_k_596_, uint8_t v_v_597_){
_start:
{
lean_object* v_map_598_; uint8_t v_hasTrace_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_613_; 
v_map_598_ = lean_ctor_get(v_o_595_, 0);
v_hasTrace_599_ = lean_ctor_get_uint8(v_o_595_, sizeof(void*)*1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_o_595_);
if (v_isSharedCheck_613_ == 0)
{
v___x_601_ = v_o_595_;
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_map_598_);
lean_dec(v_o_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_603_, 0, v_v_597_);
lean_inc(v_k_596_);
v___x_604_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_596_, v___x_603_, v_map_598_);
if (v_hasTrace_599_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_608_; 
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_606_ = l_Lean_Name_isPrefixOf(v___x_605_, v_k_596_);
lean_dec(v_k_596_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_604_);
v___x_608_ = v___x_601_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_604_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*1, v___x_606_);
return v___x_608_;
}
}
else
{
lean_object* v___x_611_; 
lean_dec(v_k_596_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_604_);
v___x_611_ = v___x_601_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_604_);
lean_ctor_set_uint8(v_reuseFailAlloc_612_, sizeof(void*)*1, v_hasTrace_599_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_614_, lean_object* v_k_615_, lean_object* v_v_616_){
_start:
{
uint8_t v_v_boxed_617_; lean_object* v_res_618_; 
v_v_boxed_617_ = lean_unbox(v_v_616_);
v_res_618_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_614_, v_k_615_, v_v_boxed_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_619_, lean_object* v_opt_620_, uint8_t v_val_621_){
_start:
{
lean_object* v_name_622_; lean_object* v___x_623_; 
v_name_622_ = lean_ctor_get(v_opt_620_, 0);
lean_inc(v_name_622_);
lean_dec_ref(v_opt_620_);
v___x_623_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_619_, v_name_622_, v_val_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_624_, lean_object* v_opt_625_, lean_object* v_val_626_){
_start:
{
uint8_t v_val_boxed_627_; lean_object* v_res_628_; 
v_val_boxed_627_ = lean_unbox(v_val_626_);
v_res_628_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_624_, v_opt_625_, v_val_boxed_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_629_, size_t v_i_630_, size_t v_stop_631_, lean_object* v_b_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_eq(v_i_630_, v_stop_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v_defValue_635_; uint8_t v___x_636_; lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; 
v___x_634_ = lean_array_uget_borrowed(v_as_629_, v_i_630_);
v_defValue_635_ = lean_ctor_get(v___x_634_, 1);
v___x_636_ = lean_unbox(v_defValue_635_);
lean_inc(v___x_634_);
v___x_637_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_632_, v___x_634_, v___x_636_);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_630_, v___x_638_);
v_i_630_ = v___x_639_;
v_b_632_ = v___x_637_;
goto _start;
}
else
{
return v_b_632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_641_, lean_object* v_i_642_, lean_object* v_stop_643_, lean_object* v_b_644_){
_start:
{
size_t v_i_boxed_645_; size_t v_stop_boxed_646_; lean_object* v_res_647_; 
v_i_boxed_645_ = lean_unbox_usize(v_i_642_);
lean_dec(v_i_642_);
v_stop_boxed_646_ = lean_unbox_usize(v_stop_643_);
lean_dec(v_stop_643_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_641_, v_i_boxed_645_, v_stop_boxed_646_, v_b_644_);
lean_dec_ref(v_as_641_);
return v_res_647_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Array_instInhabited___redArg();
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = l_Lean_Meta_eqnAffectingOptions;
v___x_654_ = lean_array_get_size(v___x_653_);
return v___x_654_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_nat_dec_lt(v___x_656_, v___x_655_);
return v___x_657_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_659_ = lean_nat_dec_le(v___x_658_, v___x_658_);
return v___x_659_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_660_; size_t v___x_661_; 
v___x_660_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_661_ = lean_usize_of_nat(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_662_, lean_object* v_act_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
uint16_t v___y_670_; lean_object* v___y_671_; lean_object* v_fileName_672_; lean_object* v_fileMap_673_; lean_object* v_currNamespace_674_; lean_object* v_openDecls_675_; lean_object* v_initHeartbeats_676_; lean_object* v_maxHeartbeats_677_; lean_object* v_quotContext_678_; lean_object* v_currMacroScope_679_; lean_object* v_cancelTk_x3f_680_; lean_object* v_inheritedTraceOptions_681_; lean_object* v_currRecDepth_682_; lean_object* v_ref_683_; uint8_t v_suppressElabErrors_684_; uint8_t v_isRecordingDeps_685_; lean_object* v___y_686_; uint16_t v___y_693_; uint8_t v___y_694_; lean_object* v___y_695_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_toCold_734_; lean_object* v_currRecDepth_735_; lean_object* v_ref_736_; uint8_t v_suppressElabErrors_737_; uint8_t v_isRecordingDeps_738_; lean_object* v_fileName_739_; lean_object* v_fileMap_740_; lean_object* v_options_741_; lean_object* v_currNamespace_742_; lean_object* v_openDecls_743_; lean_object* v_initHeartbeats_744_; lean_object* v_maxHeartbeats_745_; lean_object* v_quotContext_746_; lean_object* v_currMacroScope_747_; lean_object* v_cancelTk_x3f_748_; lean_object* v_inheritedTraceOptions_749_; lean_object* v___y_751_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_733_ = lean_st_ref_get(v_a_667_);
v_toCold_734_ = lean_ctor_get(v_a_666_, 0);
v_currRecDepth_735_ = lean_ctor_get(v_a_666_, 1);
v_ref_736_ = lean_ctor_get(v_a_666_, 2);
v_suppressElabErrors_737_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*3 + 2);
v_isRecordingDeps_738_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*3 + 3);
v_fileName_739_ = lean_ctor_get(v_toCold_734_, 0);
v_fileMap_740_ = lean_ctor_get(v_toCold_734_, 1);
v_options_741_ = lean_ctor_get(v_toCold_734_, 2);
v_currNamespace_742_ = lean_ctor_get(v_toCold_734_, 4);
v_openDecls_743_ = lean_ctor_get(v_toCold_734_, 5);
v_initHeartbeats_744_ = lean_ctor_get(v_toCold_734_, 6);
v_maxHeartbeats_745_ = lean_ctor_get(v_toCold_734_, 7);
v_quotContext_746_ = lean_ctor_get(v_toCold_734_, 8);
v_currMacroScope_747_ = lean_ctor_get(v_toCold_734_, 9);
v_cancelTk_x3f_748_ = lean_ctor_get(v_toCold_734_, 10);
v_inheritedTraceOptions_749_ = lean_ctor_get(v_toCold_734_, 11);
if (v_isRecordingDeps_738_ == 0)
{
lean_object* v_env_762_; lean_object* v___x_763_; lean_object* v_toEnvExtension_764_; lean_object* v_asyncMode_765_; uint8_t v___x_766_; lean_object* v___x_767_; 
v_env_762_ = lean_ctor_get(v___x_733_, 0);
lean_inc_ref(v_env_762_);
lean_dec(v___x_733_);
v___x_763_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_764_ = lean_ctor_get(v___x_763_, 0);
v_asyncMode_765_ = lean_ctor_get(v_toEnvExtension_764_, 2);
v___x_766_ = 0;
v___x_767_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_732_, v___x_763_, v_env_762_, v_declName_662_, v_asyncMode_765_, v___x_766_);
if (lean_obj_tag(v___x_767_) == 1)
{
lean_object* v_val_768_; lean_object* v___y_770_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_val_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_val_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_774_ = l_Lean_Meta_eqnAffectingOptions;
v___x_775_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_775_ == 0)
{
lean_inc_ref(v_options_741_);
v___y_770_ = v_options_741_;
goto v___jp_769_;
}
else
{
uint8_t v___x_776_; 
v___x_776_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_776_ == 0)
{
if (v___x_775_ == 0)
{
lean_inc_ref(v_options_741_);
v___y_770_ = v_options_741_;
goto v___jp_769_;
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_741_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_774_, v___x_777_, v___x_778_, v_options_741_);
v___y_770_ = v___x_779_;
goto v___jp_769_;
}
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_741_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_774_, v___x_780_, v___x_781_, v_options_741_);
v___y_770_ = v___x_782_;
goto v___jp_769_;
}
}
v___jp_769_:
{
size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; 
v_sz_771_ = lean_array_size(v_val_768_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_768_, v_sz_771_, v___x_772_, v___y_770_);
lean_dec(v_val_768_);
v___y_751_ = v___x_773_;
goto v___jp_750_;
}
}
else
{
lean_object* v___x_783_; uint8_t v___x_784_; 
lean_dec(v___x_767_);
v___x_783_ = l_Lean_Meta_eqnAffectingOptions;
v___x_784_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_784_ == 0)
{
lean_inc_ref(v_options_741_);
v___y_751_ = v_options_741_;
goto v___jp_750_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_785_ == 0)
{
if (v___x_784_ == 0)
{
lean_inc_ref(v_options_741_);
v___y_751_ = v_options_741_;
goto v___jp_750_;
}
else
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_741_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_783_, v___x_786_, v___x_787_, v_options_741_);
v___y_751_ = v___x_788_;
goto v___jp_750_;
}
}
else
{
size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((size_t)0ULL);
v___x_790_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_741_);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_783_, v___x_789_, v___x_790_, v_options_741_);
v___y_751_ = v___x_791_;
goto v___jp_750_;
}
}
}
}
else
{
lean_object* v___x_792_; 
lean_dec(v___x_733_);
lean_dec(v_declName_662_);
lean_inc_ref(v_options_741_);
v___x_792_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_741_);
v___y_751_ = v___x_792_;
goto v___jp_750_;
}
v___jp_669_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_687_ = l_Lean_maxRecDepth;
v___x_688_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_671_, v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_689_, 0, v_fileName_672_);
lean_ctor_set(v___x_689_, 1, v_fileMap_673_);
lean_ctor_set(v___x_689_, 2, v___y_671_);
lean_ctor_set(v___x_689_, 3, v___x_688_);
lean_ctor_set(v___x_689_, 4, v_currNamespace_674_);
lean_ctor_set(v___x_689_, 5, v_openDecls_675_);
lean_ctor_set(v___x_689_, 6, v_initHeartbeats_676_);
lean_ctor_set(v___x_689_, 7, v_maxHeartbeats_677_);
lean_ctor_set(v___x_689_, 8, v_quotContext_678_);
lean_ctor_set(v___x_689_, 9, v_currMacroScope_679_);
lean_ctor_set(v___x_689_, 10, v_cancelTk_x3f_680_);
lean_ctor_set(v___x_689_, 11, v_inheritedTraceOptions_681_);
lean_inc(v_ref_683_);
lean_inc(v_currRecDepth_682_);
v___x_690_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_currRecDepth_682_);
lean_ctor_set(v___x_690_, 2, v_ref_683_);
lean_ctor_set_uint16(v___x_690_, sizeof(void*)*3, v___y_670_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*3 + 2, v_suppressElabErrors_684_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*3 + 3, v_isRecordingDeps_685_);
lean_inc(v___y_686_);
lean_inc(v_a_665_);
lean_inc_ref(v_a_664_);
v___x_691_ = lean_apply_5(v_act_663_, v_a_664_, v_a_665_, v___x_690_, v___y_686_, lean_box(0));
return v___x_691_;
}
v___jp_692_:
{
lean_object* v___x_696_; lean_object* v_env_697_; lean_object* v_nextMacroScope_698_; lean_object* v_ngen_699_; lean_object* v_auxDeclNGen_700_; lean_object* v_traceState_701_; lean_object* v_recordedDeps_702_; lean_object* v_messages_703_; lean_object* v_infoState_704_; lean_object* v_snapshotTasks_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_730_; 
v___x_696_ = lean_st_ref_take(v_a_667_);
v_env_697_ = lean_ctor_get(v___x_696_, 0);
v_nextMacroScope_698_ = lean_ctor_get(v___x_696_, 1);
v_ngen_699_ = lean_ctor_get(v___x_696_, 2);
v_auxDeclNGen_700_ = lean_ctor_get(v___x_696_, 3);
v_traceState_701_ = lean_ctor_get(v___x_696_, 4);
v_recordedDeps_702_ = lean_ctor_get(v___x_696_, 6);
v_messages_703_ = lean_ctor_get(v___x_696_, 7);
v_infoState_704_ = lean_ctor_get(v___x_696_, 8);
v_snapshotTasks_705_ = lean_ctor_get(v___x_696_, 9);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v___x_696_, 5);
lean_dec(v_unused_731_);
v___x_707_ = v___x_696_;
v_isShared_708_ = v_isSharedCheck_730_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snapshotTasks_705_);
lean_inc(v_infoState_704_);
lean_inc(v_messages_703_);
lean_inc(v_recordedDeps_702_);
lean_inc(v_traceState_701_);
lean_inc(v_auxDeclNGen_700_);
lean_inc(v_ngen_699_);
lean_inc(v_nextMacroScope_698_);
lean_inc(v_env_697_);
lean_dec(v___x_696_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_730_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_709_ = l_Lean_Kernel_enableDiag(v_env_697_, v___y_694_);
v___x_710_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 5, v___x_710_);
lean_ctor_set(v___x_707_, 0, v___x_709_);
v___x_712_ = v___x_707_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_nextMacroScope_698_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_ngen_699_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_auxDeclNGen_700_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_traceState_701_);
lean_ctor_set(v_reuseFailAlloc_729_, 5, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_729_, 6, v_recordedDeps_702_);
lean_ctor_set(v_reuseFailAlloc_729_, 7, v_messages_703_);
lean_ctor_set(v_reuseFailAlloc_729_, 8, v_infoState_704_);
lean_ctor_set(v_reuseFailAlloc_729_, 9, v_snapshotTasks_705_);
v___x_712_ = v_reuseFailAlloc_729_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v_toCold_714_; lean_object* v_currRecDepth_715_; lean_object* v_ref_716_; uint8_t v_suppressElabErrors_717_; uint8_t v_isRecordingDeps_718_; lean_object* v_fileName_719_; lean_object* v_fileMap_720_; lean_object* v_currNamespace_721_; lean_object* v_openDecls_722_; lean_object* v_initHeartbeats_723_; lean_object* v_maxHeartbeats_724_; lean_object* v_quotContext_725_; lean_object* v_currMacroScope_726_; lean_object* v_cancelTk_x3f_727_; lean_object* v_inheritedTraceOptions_728_; 
v___x_713_ = lean_st_ref_put(v_a_667_, v___x_712_);
v_toCold_714_ = lean_ctor_get(v_a_666_, 0);
v_currRecDepth_715_ = lean_ctor_get(v_a_666_, 1);
v_ref_716_ = lean_ctor_get(v_a_666_, 2);
v_suppressElabErrors_717_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*3 + 2);
v_isRecordingDeps_718_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*3 + 3);
v_fileName_719_ = lean_ctor_get(v_toCold_714_, 0);
v_fileMap_720_ = lean_ctor_get(v_toCold_714_, 1);
v_currNamespace_721_ = lean_ctor_get(v_toCold_714_, 4);
v_openDecls_722_ = lean_ctor_get(v_toCold_714_, 5);
v_initHeartbeats_723_ = lean_ctor_get(v_toCold_714_, 6);
v_maxHeartbeats_724_ = lean_ctor_get(v_toCold_714_, 7);
v_quotContext_725_ = lean_ctor_get(v_toCold_714_, 8);
v_currMacroScope_726_ = lean_ctor_get(v_toCold_714_, 9);
v_cancelTk_x3f_727_ = lean_ctor_get(v_toCold_714_, 10);
v_inheritedTraceOptions_728_ = lean_ctor_get(v_toCold_714_, 11);
lean_inc_ref(v_inheritedTraceOptions_728_);
lean_inc(v_cancelTk_x3f_727_);
lean_inc(v_currMacroScope_726_);
lean_inc(v_quotContext_725_);
lean_inc(v_maxHeartbeats_724_);
lean_inc(v_initHeartbeats_723_);
lean_inc(v_openDecls_722_);
lean_inc(v_currNamespace_721_);
lean_inc_ref(v_fileMap_720_);
lean_inc_ref(v_fileName_719_);
v___y_670_ = v___y_693_;
v___y_671_ = v___y_695_;
v_fileName_672_ = v_fileName_719_;
v_fileMap_673_ = v_fileMap_720_;
v_currNamespace_674_ = v_currNamespace_721_;
v_openDecls_675_ = v_openDecls_722_;
v_initHeartbeats_676_ = v_initHeartbeats_723_;
v_maxHeartbeats_677_ = v_maxHeartbeats_724_;
v_quotContext_678_ = v_quotContext_725_;
v_currMacroScope_679_ = v_currMacroScope_726_;
v_cancelTk_x3f_680_ = v_cancelTk_x3f_727_;
v_inheritedTraceOptions_681_ = v_inheritedTraceOptions_728_;
v_currRecDepth_682_ = v_currRecDepth_715_;
v_ref_683_ = v_ref_716_;
v_suppressElabErrors_684_ = v_suppressElabErrors_717_;
v_isRecordingDeps_685_ = v_isRecordingDeps_718_;
v___y_686_ = v_a_667_;
goto v___jp_669_;
}
}
}
v___jp_750_:
{
uint16_t v___x_752_; lean_object* v___x_753_; lean_object* v_env_754_; uint8_t v___x_755_; uint16_t v___x_756_; uint16_t v___x_757_; uint16_t v___x_758_; uint8_t v___x_759_; 
v___x_752_ = l_Lean_OptionFlags_ofOptions(v___y_751_);
v___x_753_ = lean_st_ref_get(v_a_667_);
v_env_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc_ref(v_env_754_);
lean_dec(v___x_753_);
v___x_755_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_754_);
lean_dec_ref(v_env_754_);
v___x_756_ = 512;
v___x_757_ = lean_uint16_land(v___x_752_, v___x_756_);
v___x_758_ = 0;
v___x_759_ = lean_uint16_dec_eq(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
if (v___x_755_ == 0)
{
uint8_t v___x_760_; 
v___x_760_ = 1;
v___y_693_ = v___x_752_;
v___y_694_ = v___x_760_;
v___y_695_ = v___y_751_;
goto v___jp_692_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_749_);
lean_inc(v_cancelTk_x3f_748_);
lean_inc(v_currMacroScope_747_);
lean_inc(v_quotContext_746_);
lean_inc(v_maxHeartbeats_745_);
lean_inc(v_initHeartbeats_744_);
lean_inc(v_openDecls_743_);
lean_inc(v_currNamespace_742_);
lean_inc_ref(v_fileMap_740_);
lean_inc_ref(v_fileName_739_);
v___y_670_ = v___x_752_;
v___y_671_ = v___y_751_;
v_fileName_672_ = v_fileName_739_;
v_fileMap_673_ = v_fileMap_740_;
v_currNamespace_674_ = v_currNamespace_742_;
v_openDecls_675_ = v_openDecls_743_;
v_initHeartbeats_676_ = v_initHeartbeats_744_;
v_maxHeartbeats_677_ = v_maxHeartbeats_745_;
v_quotContext_678_ = v_quotContext_746_;
v_currMacroScope_679_ = v_currMacroScope_747_;
v_cancelTk_x3f_680_ = v_cancelTk_x3f_748_;
v_inheritedTraceOptions_681_ = v_inheritedTraceOptions_749_;
v_currRecDepth_682_ = v_currRecDepth_735_;
v_ref_683_ = v_ref_736_;
v_suppressElabErrors_684_ = v_suppressElabErrors_737_;
v_isRecordingDeps_685_ = v_isRecordingDeps_738_;
v___y_686_ = v_a_667_;
goto v___jp_669_;
}
}
else
{
if (v___x_755_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_749_);
lean_inc(v_cancelTk_x3f_748_);
lean_inc(v_currMacroScope_747_);
lean_inc(v_quotContext_746_);
lean_inc(v_maxHeartbeats_745_);
lean_inc(v_initHeartbeats_744_);
lean_inc(v_openDecls_743_);
lean_inc(v_currNamespace_742_);
lean_inc_ref(v_fileMap_740_);
lean_inc_ref(v_fileName_739_);
v___y_670_ = v___x_752_;
v___y_671_ = v___y_751_;
v_fileName_672_ = v_fileName_739_;
v_fileMap_673_ = v_fileMap_740_;
v_currNamespace_674_ = v_currNamespace_742_;
v_openDecls_675_ = v_openDecls_743_;
v_initHeartbeats_676_ = v_initHeartbeats_744_;
v_maxHeartbeats_677_ = v_maxHeartbeats_745_;
v_quotContext_678_ = v_quotContext_746_;
v_currMacroScope_679_ = v_currMacroScope_747_;
v_cancelTk_x3f_680_ = v_cancelTk_x3f_748_;
v_inheritedTraceOptions_681_ = v_inheritedTraceOptions_749_;
v_currRecDepth_682_ = v_currRecDepth_735_;
v_ref_683_ = v_ref_736_;
v_suppressElabErrors_684_ = v_suppressElabErrors_737_;
v_isRecordingDeps_685_ = v_isRecordingDeps_738_;
v___y_686_ = v_a_667_;
goto v___jp_669_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
v___y_693_ = v___x_752_;
v___y_694_ = v___x_761_;
v___y_695_ = v___y_751_;
goto v___jp_692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_793_, lean_object* v_act_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_793_, v_act_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_801_, lean_object* v_declName_802_, lean_object* v_act_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_802_, v_act_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_810_, lean_object* v_declName_811_, lean_object* v_act_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_810_, v_declName_811_, v_act_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_env_823_; lean_object* v_toConstantVal_824_; lean_object* v_value_825_; lean_object* v_all_826_; uint8_t v___y_828_; lean_object* v_type_836_; uint8_t v___x_837_; 
v___x_822_ = lean_st_ref_get(v___y_820_);
v_env_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc_ref_n(v_env_823_, 2);
lean_dec(v___x_822_);
v_toConstantVal_824_ = lean_ctor_get(v_thm_819_, 0);
v_value_825_ = lean_ctor_get(v_thm_819_, 1);
v_all_826_ = lean_ctor_get(v_thm_819_, 2);
v_type_836_ = lean_ctor_get(v_toConstantVal_824_, 2);
v___x_837_ = l_Lean_Environment_hasUnsafe(v_env_823_, v_type_836_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; 
v___x_838_ = l_Lean_Environment_hasUnsafe(v_env_823_, v_value_825_);
v___y_828_ = v___x_838_;
goto v___jp_827_;
}
else
{
lean_dec_ref(v_env_823_);
v___y_828_ = v___x_837_;
goto v___jp_827_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_829_, 0, v_thm_819_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc(v_all_826_);
lean_inc_ref(v_value_825_);
lean_inc_ref(v_toConstantVal_824_);
lean_dec_ref(v_thm_819_);
v___x_831_ = lean_box(0);
v___x_832_ = 0;
v___x_833_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_833_, 0, v_toConstantVal_824_);
lean_ctor_set(v___x_833_, 1, v_value_825_);
lean_ctor_set(v___x_833_, 2, v___x_831_);
lean_ctor_set(v___x_833_, 3, v_all_826_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*4, v___x_832_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_839_, v___y_840_);
lean_dec(v___y_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_843_, v___y_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_857_, lean_object* v_b_858_, lean_object* v_c_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; 
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
v___x_865_ = lean_apply_7(v_k_857_, v_b_858_, v_c_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, lean_box(0));
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_866_, lean_object* v_b_867_, lean_object* v_c_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_866_, v_b_867_, v_c_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_875_, lean_object* v_k_876_, uint8_t v_cleanupAnnotations_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___f_883_; uint8_t v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___f_883_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_883_, 0, v_k_876_);
v___x_884_ = 1;
v___x_885_ = 0;
v___x_886_ = lean_box(0);
v___x_887_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_875_, v___x_884_, v___x_885_, v___x_884_, v___x_885_, v___x_886_, v___f_883_, v_cleanupAnnotations_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
v_a_896_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_887_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_887_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_904_, lean_object* v_k_905_, lean_object* v_cleanupAnnotations_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_912_; lean_object* v_res_913_; 
v_cleanupAnnotations_boxed_912_ = lean_unbox(v_cleanupAnnotations_906_);
v_res_913_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_904_, v_k_905_, v_cleanupAnnotations_boxed_912_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_914_, lean_object* v_e_915_, lean_object* v_k_916_, uint8_t v_cleanupAnnotations_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_915_, v_k_916_, v_cleanupAnnotations_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_924_, lean_object* v_e_925_, lean_object* v_k_926_, lean_object* v_cleanupAnnotations_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_933_; lean_object* v_res_934_; 
v_cleanupAnnotations_boxed_933_ = lean_unbox(v_cleanupAnnotations_927_);
v_res_934_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_924_, v_e_925_, v_k_926_, v_cleanupAnnotations_boxed_933_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = l_List_reverse___redArg(v_a_936_);
return v___x_937_;
}
else
{
lean_object* v_head_938_; lean_object* v_tail_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
v_head_938_ = lean_ctor_get(v_a_935_, 0);
v_tail_939_ = lean_ctor_get(v_a_935_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v_a_935_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_tail_939_);
lean_inc(v_head_938_);
lean_dec(v_a_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = l_Lean_mkLevelParam(v_head_938_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_a_936_);
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_a_936_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v_a_935_ = v_tail_939_;
v_a_936_ = v___x_945_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_949_, lean_object* v_name_950_, lean_object* v_xs_951_, lean_object* v_body_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_name_958_; lean_object* v_levelParams_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1029_; 
v_name_958_ = lean_ctor_get(v_toConstantVal_949_, 0);
v_levelParams_959_ = lean_ctor_get(v_toConstantVal_949_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_toConstantVal_949_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_toConstantVal_949_, 2);
lean_dec(v_unused_1030_);
v___x_961_ = v_toConstantVal_949_;
v_isShared_962_ = v_isSharedCheck_1029_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_levelParams_959_);
lean_inc(v_name_958_);
lean_dec(v_toConstantVal_949_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1029_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_lhs_966_; lean_object* v___x_967_; 
v___x_963_ = lean_box(0);
lean_inc(v_levelParams_959_);
v___x_964_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_959_, v___x_963_);
v___x_965_ = l_Lean_mkConst(v_name_958_, v___x_964_);
v_lhs_966_ = l_Lean_mkAppN(v___x_965_, v_xs_951_);
lean_inc_ref(v_lhs_966_);
v___x_967_ = l_Lean_Meta_mkEq(v_lhs_966_, v_body_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; uint8_t v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = 0;
v___x_970_ = 1;
v___x_971_ = 1;
v___x_972_ = l_Lean_Meta_mkForallFVars(v_xs_951_, v_a_968_, v___x_969_, v___x_970_, v___x_970_, v___x_971_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v___x_974_ = l_Lean_Meta_letToHave(v_a_973_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = l_Lean_Meta_mkEqRefl(v_lhs_966_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = l_Lean_Meta_mkLambdaFVars(v_xs_951_, v_a_977_, v___x_969_, v___x_970_, v___x_969_, v___x_970_, v___x_971_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
lean_inc(v_name_950_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 2, v_a_975_);
lean_ctor_set(v___x_961_, 0, v_name_950_);
v___x_981_ = v___x_961_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_name_950_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_levelParams_959_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_a_975_);
v___x_981_ = v_reuseFailAlloc_988_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___x_986_; 
lean_inc(v_name_950_);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v_name_950_);
lean_ctor_set(v___x_982_, 1, v___x_963_);
v___x_983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v_a_979_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
v___x_984_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_983_, v___y_956_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = l_Lean_addDecl(v_a_985_, v___x_969_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v___x_987_; 
lean_dec_ref_known(v___x_986_, 1);
v___x_987_ = l_Lean_inferDefEqAttr(v_name_950_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
return v___x_987_;
}
else
{
lean_dec(v_name_950_);
return v___x_986_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_a_975_);
lean_del_object(v___x_961_);
lean_dec(v_levelParams_959_);
lean_dec(v_name_950_);
v_a_989_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_978_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_978_);
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
lean_dec(v_a_975_);
lean_del_object(v___x_961_);
lean_dec(v_levelParams_959_);
lean_dec(v_name_950_);
v_a_997_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_976_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_976_);
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
lean_dec_ref(v_lhs_966_);
lean_del_object(v___x_961_);
lean_dec(v_levelParams_959_);
lean_dec(v_name_950_);
v_a_1005_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_974_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_974_);
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
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_lhs_966_);
lean_del_object(v___x_961_);
lean_dec(v_levelParams_959_);
lean_dec(v_name_950_);
v_a_1013_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_972_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_972_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v_lhs_966_);
lean_del_object(v___x_961_);
lean_dec(v_levelParams_959_);
lean_dec(v_name_950_);
v_a_1021_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_967_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_967_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1031_, lean_object* v_name_1032_, lean_object* v_xs_1033_, lean_object* v_body_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1031_, v_name_1032_, v_xs_1033_, v_body_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v_xs_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1041_, lean_object* v_info_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_toConstantVal_1048_; lean_object* v_value_1049_; lean_object* v___f_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
v_toConstantVal_1048_ = lean_ctor_get(v_info_1042_, 0);
lean_inc_ref(v_toConstantVal_1048_);
v_value_1049_ = lean_ctor_get(v_info_1042_, 1);
lean_inc_ref(v_value_1049_);
lean_dec_ref(v_info_1042_);
v___f_1050_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1050_, 0, v_toConstantVal_1048_);
lean_closure_set(v___f_1050_, 1, v_name_1041_);
v___x_1051_ = 1;
v___x_1052_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1049_, v___f_1050_, v___x_1051_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1053_, lean_object* v_info_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1053_, v_info_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1061_, lean_object* v_name_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1071_; lean_object* v_env_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = lean_st_ref_get(v_a_1066_);
v_env_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc_ref(v_env_1072_);
lean_dec(v___x_1071_);
v___x_1073_ = 0;
lean_inc(v_declName_1061_);
v___x_1074_ = l_Lean_Environment_find_x3f(v_env_1072_, v_declName_1061_, v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1102_; 
v_val_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1102_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_val_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1102_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
if (lean_obj_tag(v_val_1075_) == 1)
{
lean_object* v_val_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_val_1079_ = lean_ctor_get(v_val_1075_, 0);
lean_inc_ref(v_val_1079_);
lean_dec_ref_known(v_val_1075_, 1);
lean_inc_n(v_name_1062_, 2);
v___x_1080_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1080_, 0, v_name_1062_);
lean_closure_set(v___x_1080_, 1, v_val_1079_);
lean_inc(v_declName_1061_);
v___x_1081_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1081_, 0, lean_box(0));
lean_closure_set(v___x_1081_, 1, v_declName_1061_);
lean_closure_set(v___x_1081_, 2, v___x_1080_);
v___x_1082_ = l_Lean_Meta_realizeConst(v_declName_1061_, v_name_1062_, v___x_1081_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1092_; 
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___x_1082_, 0);
lean_dec(v_unused_1093_);
v___x_1084_ = v___x_1082_;
v_isShared_1085_ = v_isSharedCheck_1092_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v___x_1082_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1092_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v_name_1062_);
v___x_1087_ = v___x_1077_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_name_1062_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1087_);
v___x_1089_ = v___x_1084_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_del_object(v___x_1077_);
lean_dec(v_name_1062_);
v_a_1094_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1082_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1082_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_del_object(v___x_1077_);
lean_dec(v_val_1075_);
lean_dec(v_name_1062_);
lean_dec(v_declName_1061_);
goto v___jp_1068_;
}
}
}
else
{
lean_dec(v___x_1074_);
lean_dec(v_name_1062_);
lean_dec(v_declName_1061_);
goto v___jp_1068_;
}
v___jp_1068_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1103_, lean_object* v_name_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1103_, v_name_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1111_, lean_object* v_vals_1112_, lean_object* v_i_1113_, lean_object* v_k_1114_){
_start:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_array_get_size(v_keys_1111_);
v___x_1116_ = lean_nat_dec_lt(v_i_1113_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec(v_i_1113_);
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
else
{
lean_object* v_k_x27_1118_; uint8_t v___x_1119_; 
v_k_x27_1118_ = lean_array_fget_borrowed(v_keys_1111_, v_i_1113_);
v___x_1119_ = lean_name_eq(v_k_1114_, v_k_x27_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_add(v_i_1113_, v___x_1120_);
lean_dec(v_i_1113_);
v_i_1113_ = v___x_1121_;
goto _start;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_array_fget_borrowed(v_vals_1112_, v_i_1113_);
lean_dec(v_i_1113_);
lean_inc(v___x_1123_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1125_, lean_object* v_vals_1126_, lean_object* v_i_1127_, lean_object* v_k_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1125_, v_vals_1126_, v_i_1127_, v_k_1128_);
lean_dec(v_k_1128_);
lean_dec_ref(v_vals_1126_);
lean_dec_ref(v_keys_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1130_, size_t v_x_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1130_) == 0)
{
lean_object* v_es_1133_; lean_object* v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; lean_object* v_j_1137_; lean_object* v___x_1138_; 
v_es_1133_ = lean_ctor_get(v_x_1130_, 0);
v___x_1134_ = lean_box(2);
v___x_1135_ = ((size_t)31ULL);
v___x_1136_ = lean_usize_land(v_x_1131_, v___x_1135_);
v_j_1137_ = lean_usize_to_nat(v___x_1136_);
v___x_1138_ = lean_array_get_borrowed(v___x_1134_, v_es_1133_, v_j_1137_);
lean_dec(v_j_1137_);
switch(lean_obj_tag(v___x_1138_))
{
case 0:
{
lean_object* v_key_1139_; lean_object* v_val_1140_; uint8_t v___x_1141_; 
v_key_1139_ = lean_ctor_get(v___x_1138_, 0);
v_val_1140_ = lean_ctor_get(v___x_1138_, 1);
v___x_1141_ = lean_name_eq(v_x_1132_, v_key_1139_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_box(0);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; 
lean_inc(v_val_1140_);
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_val_1140_);
return v___x_1143_;
}
}
case 1:
{
lean_object* v_node_1144_; size_t v___x_1145_; size_t v___x_1146_; 
v_node_1144_ = lean_ctor_get(v___x_1138_, 0);
v___x_1145_ = ((size_t)5ULL);
v___x_1146_ = lean_usize_shift_right(v_x_1131_, v___x_1145_);
v_x_1130_ = v_node_1144_;
v_x_1131_ = v___x_1146_;
goto _start;
}
default: 
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_box(0);
return v___x_1148_;
}
}
}
else
{
lean_object* v_ks_1149_; lean_object* v_vs_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_ks_1149_ = lean_ctor_get(v_x_1130_, 0);
v_vs_1150_ = lean_ctor_get(v_x_1130_, 1);
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1149_, v_vs_1150_, v___x_1151_, v_x_1132_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
size_t v_x_344__boxed_1156_; lean_object* v_res_1157_; 
v_x_344__boxed_1156_ = lean_unbox_usize(v_x_1154_);
lean_dec(v_x_1154_);
v_res_1157_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1153_, v_x_344__boxed_1156_, v_x_1155_);
lean_dec(v_x_1155_);
lean_dec_ref(v_x_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
uint64_t v___y_1161_; 
if (lean_obj_tag(v_x_1159_) == 0)
{
uint64_t v___x_1164_; 
v___x_1164_ = 1723ULL;
v___y_1161_ = v___x_1164_;
goto v___jp_1160_;
}
else
{
uint64_t v_hash_1165_; 
v_hash_1165_ = lean_ctor_get_uint64(v_x_1159_, sizeof(void*)*2);
v___y_1161_ = v_hash_1165_;
goto v___jp_1160_;
}
v___jp_1160_:
{
size_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_uint64_to_usize(v___y_1161_);
v___x_1163_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1158_, v___x_1162_, v_x_1159_);
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1166_, v_x_1167_);
lean_dec(v_x_1167_);
lean_dec_ref(v_x_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_env_1174_; lean_object* v___x_1175_; lean_object* v_asyncMode_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1172_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1173_ = lean_st_ref_get(v_a_1170_);
v_env_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc_ref(v_env_1174_);
lean_dec(v___x_1173_);
v___x_1175_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1176_ = lean_ctor_get(v___x_1175_, 2);
v___x_1177_ = lean_box(0);
v___x_1178_ = 0;
v___x_1179_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1172_, v___x_1175_, v_env_1174_, v_asyncMode_1176_, v___x_1177_, v___x_1178_);
v___x_1180_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1179_, v_thmName_1169_);
lean_dec(v___x_1179_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec(v_thmName_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1186_, v_a_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_thmName_1191_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1197_, v_x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1200_, v_x_1201_, v_x_1202_);
lean_dec(v_x_1202_);
lean_dec_ref(v_x_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1204_, lean_object* v_x_1205_, size_t v_x_1206_, lean_object* v_x_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1205_, v_x_1206_, v_x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
size_t v_x_439__boxed_1213_; lean_object* v_res_1214_; 
v_x_439__boxed_1213_ = lean_unbox_usize(v_x_1211_);
lean_dec(v_x_1211_);
v_res_1214_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1209_, v_x_1210_, v_x_439__boxed_1213_, v_x_1212_);
lean_dec(v_x_1212_);
lean_dec_ref(v_x_1210_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1215_, lean_object* v_keys_1216_, lean_object* v_vals_1217_, lean_object* v_heq_1218_, lean_object* v_i_1219_, lean_object* v_k_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1216_, v_vals_1217_, v_i_1219_, v_k_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1222_, lean_object* v_keys_1223_, lean_object* v_vals_1224_, lean_object* v_heq_1225_, lean_object* v_i_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1222_, v_keys_1223_, v_vals_1224_, v_heq_1225_, v_i_1226_, v_k_1227_);
lean_dec(v_k_1227_);
lean_dec_ref(v_vals_1224_);
lean_dec_ref(v_keys_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1229_, lean_object* v_i_1230_, lean_object* v_k_1231_){
_start:
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_array_get_size(v_keys_1229_);
v___x_1233_ = lean_nat_dec_lt(v_i_1230_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v_i_1230_);
return v___x_1233_;
}
else
{
lean_object* v_k_x27_1234_; uint8_t v___x_1235_; 
v_k_x27_1234_ = lean_array_fget_borrowed(v_keys_1229_, v_i_1230_);
v___x_1235_ = lean_name_eq(v_k_1231_, v_k_x27_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_add(v_i_1230_, v___x_1236_);
lean_dec(v_i_1230_);
v_i_1230_ = v___x_1237_;
goto _start;
}
else
{
lean_dec(v_i_1230_);
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1239_, lean_object* v_i_1240_, lean_object* v_k_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1239_, v_i_1240_, v_k_1241_);
lean_dec(v_k_1241_);
lean_dec_ref(v_keys_1239_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1244_, size_t v_x_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
lean_object* v_es_1247_; lean_object* v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; lean_object* v_j_1251_; lean_object* v___x_1252_; 
v_es_1247_ = lean_ctor_get(v_x_1244_, 0);
v___x_1248_ = lean_box(2);
v___x_1249_ = ((size_t)31ULL);
v___x_1250_ = lean_usize_land(v_x_1245_, v___x_1249_);
v_j_1251_ = lean_usize_to_nat(v___x_1250_);
v___x_1252_ = lean_array_get_borrowed(v___x_1248_, v_es_1247_, v_j_1251_);
lean_dec(v_j_1251_);
switch(lean_obj_tag(v___x_1252_))
{
case 0:
{
lean_object* v_key_1253_; uint8_t v___x_1254_; 
v_key_1253_ = lean_ctor_get(v___x_1252_, 0);
v___x_1254_ = lean_name_eq(v_x_1246_, v_key_1253_);
return v___x_1254_;
}
case 1:
{
lean_object* v_node_1255_; size_t v___x_1256_; size_t v___x_1257_; 
v_node_1255_ = lean_ctor_get(v___x_1252_, 0);
v___x_1256_ = ((size_t)5ULL);
v___x_1257_ = lean_usize_shift_right(v_x_1245_, v___x_1256_);
v_x_1244_ = v_node_1255_;
v_x_1245_ = v___x_1257_;
goto _start;
}
default: 
{
uint8_t v___x_1259_; 
v___x_1259_ = 0;
return v___x_1259_;
}
}
}
else
{
lean_object* v_ks_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_ks_1260_ = lean_ctor_get(v_x_1244_, 0);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1260_, v___x_1261_, v_x_1246_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
size_t v_x_328__boxed_1266_; uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_x_328__boxed_1266_ = lean_unbox_usize(v_x_1264_);
lean_dec(v_x_1264_);
v_res_1267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1263_, v_x_328__boxed_1266_, v_x_1265_);
lean_dec(v_x_1265_);
lean_dec_ref(v_x_1263_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
uint64_t v___y_1272_; 
if (lean_obj_tag(v_x_1270_) == 0)
{
uint64_t v___x_1275_; 
v___x_1275_ = 1723ULL;
v___y_1272_ = v___x_1275_;
goto v___jp_1271_;
}
else
{
uint64_t v_hash_1276_; 
v_hash_1276_ = lean_ctor_get_uint64(v_x_1270_, sizeof(void*)*2);
v___y_1272_ = v_hash_1276_;
goto v___jp_1271_;
}
v___jp_1271_:
{
size_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_uint64_to_usize(v___y_1272_);
v___x_1274_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1269_, v___x_1273_, v_x_1270_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1277_, v_x_1278_);
lean_dec(v_x_1278_);
lean_dec_ref(v_x_1277_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_env_1286_; lean_object* v___x_1287_; lean_object* v_asyncMode_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1284_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1285_ = lean_st_ref_get(v_a_1282_);
v_env_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc_ref(v_env_1286_);
lean_dec(v___x_1285_);
v___x_1287_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1288_ = lean_ctor_get(v___x_1287_, 2);
v___x_1289_ = lean_box(0);
v___x_1290_ = 0;
v___x_1291_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1284_, v___x_1287_, v_env_1286_, v_asyncMode_1288_, v___x_1289_, v___x_1290_);
v___x_1292_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1291_, v_thmName_1281_);
lean_dec(v___x_1291_);
v___x_1293_ = lean_box(v___x_1292_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec(v_thmName_1295_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1299_, v_a_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Meta_isEqnThm(v_thmName_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_thmName_1304_);
return v_res_1308_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
uint8_t v___x_1312_; 
v___x_1312_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1310_, v_x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
uint8_t v_res_1316_; lean_object* v_r_1317_; 
v_res_1316_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1313_, v_x_1314_, v_x_1315_);
lean_dec(v_x_1315_);
lean_dec_ref(v_x_1314_);
v_r_1317_ = lean_box(v_res_1316_);
return v_r_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1318_, lean_object* v_x_1319_, size_t v_x_1320_, lean_object* v_x_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1319_, v_x_1320_, v_x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
size_t v_x_419__boxed_1327_; uint8_t v_res_1328_; lean_object* v_r_1329_; 
v_x_419__boxed_1327_ = lean_unbox_usize(v_x_1325_);
lean_dec(v_x_1325_);
v_res_1328_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1323_, v_x_1324_, v_x_419__boxed_1327_, v_x_1326_);
lean_dec(v_x_1326_);
lean_dec_ref(v_x_1324_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1330_, lean_object* v_keys_1331_, lean_object* v_vals_1332_, lean_object* v_heq_1333_, lean_object* v_i_1334_, lean_object* v_k_1335_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1331_, v_i_1334_, v_k_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1337_, lean_object* v_keys_1338_, lean_object* v_vals_1339_, lean_object* v_heq_1340_, lean_object* v_i_1341_, lean_object* v_k_1342_){
_start:
{
uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_res_1343_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1337_, v_keys_1338_, v_vals_1339_, v_heq_1340_, v_i_1341_, v_k_1342_);
lean_dec(v_k_1342_);
lean_dec_ref(v_vals_1339_);
lean_dec_ref(v_keys_1338_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1345_, lean_object* v_msg_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_panic_fn_borrowed(v_x1_1345_, v_msg_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1348_, lean_object* v_msg_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1348_, v_msg_1349_);
lean_dec_ref(v_x1_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v_ks_1355_; lean_object* v_vs_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1380_; 
v_ks_1355_ = lean_ctor_get(v_x_1351_, 0);
v_vs_1356_ = lean_ctor_get(v_x_1351_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1358_ = v_x_1351_;
v_isShared_1359_ = v_isSharedCheck_1380_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_vs_1356_);
lean_inc(v_ks_1355_);
lean_dec(v_x_1351_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1380_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = lean_array_get_size(v_ks_1355_);
v___x_1361_ = lean_nat_dec_lt(v_x_1352_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_dec(v_x_1352_);
v___x_1362_ = lean_array_push(v_ks_1355_, v_x_1353_);
v___x_1363_ = lean_array_push(v_vs_1356_, v_x_1354_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1363_);
lean_ctor_set(v___x_1358_, 0, v___x_1362_);
v___x_1365_ = v___x_1358_;
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
else
{
lean_object* v_k_x27_1367_; uint8_t v___x_1368_; 
v_k_x27_1367_ = lean_array_fget_borrowed(v_ks_1355_, v_x_1352_);
v___x_1368_ = lean_name_eq(v_x_1353_, v_k_x27_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1370_; 
if (v_isShared_1359_ == 0)
{
v___x_1370_ = v___x_1358_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_ks_1355_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_vs_1356_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_x_1352_, v___x_1371_);
lean_dec(v_x_1352_);
v_x_1351_ = v___x_1370_;
v_x_1352_ = v___x_1372_;
goto _start;
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = lean_array_fset(v_ks_1355_, v_x_1352_, v_x_1353_);
v___x_1376_ = lean_array_fset(v_vs_1356_, v_x_1352_, v_x_1354_);
lean_dec(v_x_1352_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1376_);
lean_ctor_set(v___x_1358_, 0, v___x_1375_);
v___x_1378_ = v___x_1358_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1381_, lean_object* v_k_1382_, lean_object* v_v_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1381_, v___x_1384_, v_k_1382_, v_v_1383_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1387_, size_t v_x_1388_, size_t v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1387_) == 0)
{
lean_object* v_es_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v_j_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_es_1392_ = lean_ctor_get(v_x_1387_, 0);
v___x_1393_ = ((size_t)31ULL);
v___x_1394_ = lean_usize_land(v_x_1388_, v___x_1393_);
v_j_1395_ = lean_usize_to_nat(v___x_1394_);
v___x_1396_ = lean_array_get_size(v_es_1392_);
v___x_1397_ = lean_nat_dec_lt(v_j_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_dec(v_j_1395_);
lean_dec(v_x_1391_);
lean_dec(v_x_1390_);
return v_x_1387_;
}
else
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1436_; 
lean_inc_ref(v_es_1392_);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_x_1387_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_x_1387_, 0);
lean_dec(v_unused_1437_);
v___x_1399_ = v_x_1387_;
v_isShared_1400_ = v_isSharedCheck_1436_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v_x_1387_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1436_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_v_1401_; lean_object* v___x_1402_; lean_object* v_xs_x27_1403_; lean_object* v___y_1405_; 
v_v_1401_ = lean_array_fget(v_es_1392_, v_j_1395_);
v___x_1402_ = lean_box(0);
v_xs_x27_1403_ = lean_array_fset(v_es_1392_, v_j_1395_, v___x_1402_);
switch(lean_obj_tag(v_v_1401_))
{
case 0:
{
lean_object* v_key_1410_; lean_object* v_val_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1421_; 
v_key_1410_ = lean_ctor_get(v_v_1401_, 0);
v_val_1411_ = lean_ctor_get(v_v_1401_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_v_1401_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1413_ = v_v_1401_;
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_val_1411_);
lean_inc(v_key_1410_);
lean_dec(v_v_1401_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_name_eq(v_x_1390_, v_key_1410_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_del_object(v___x_1413_);
v___x_1416_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1410_, v_val_1411_, v_x_1390_, v_x_1391_);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
v___y_1405_ = v___x_1417_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1419_; 
lean_dec(v_val_1411_);
lean_dec(v_key_1410_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v_x_1391_);
lean_ctor_set(v___x_1413_, 0, v_x_1390_);
v___x_1419_ = v___x_1413_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_x_1390_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_x_1391_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
v___y_1405_ = v___x_1419_;
goto v___jp_1404_;
}
}
}
}
case 1:
{
lean_object* v_node_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1434_; 
v_node_1422_ = lean_ctor_get(v_v_1401_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_v_1401_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1424_ = v_v_1401_;
v_isShared_1425_ = v_isSharedCheck_1434_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_node_1422_);
lean_dec(v_v_1401_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1434_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
size_t v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1426_ = ((size_t)5ULL);
v___x_1427_ = lean_usize_shift_right(v_x_1388_, v___x_1426_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_add(v_x_1389_, v___x_1428_);
v___x_1430_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1422_, v___x_1427_, v___x_1429_, v_x_1390_, v_x_1391_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1430_);
v___x_1432_ = v___x_1424_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
v___y_1405_ = v___x_1432_;
goto v___jp_1404_;
}
}
}
default: 
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_x_1390_);
lean_ctor_set(v___x_1435_, 1, v_x_1391_);
v___y_1405_ = v___x_1435_;
goto v___jp_1404_;
}
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_array_fset(v_xs_x27_1403_, v_j_1395_, v___y_1405_);
lean_dec(v_j_1395_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1406_);
v___x_1408_ = v___x_1399_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
else
{
lean_object* v_ks_1438_; lean_object* v_vs_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1457_; 
v_ks_1438_ = lean_ctor_get(v_x_1387_, 0);
v_vs_1439_ = lean_ctor_get(v_x_1387_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_x_1387_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1441_ = v_x_1387_;
v_isShared_1442_ = v_isSharedCheck_1457_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_vs_1439_);
lean_inc(v_ks_1438_);
lean_dec(v_x_1387_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1457_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_ks_1438_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_vs_1439_);
v___x_1444_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v_newNode_1445_; size_t v___x_1446_; uint8_t v___x_1447_; 
v_newNode_1445_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1444_, v_x_1390_, v_x_1391_);
v___x_1446_ = ((size_t)7ULL);
v___x_1447_ = lean_usize_dec_le(v___x_1446_, v_x_1389_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1445_);
v___x_1449_ = lean_unsigned_to_nat(4u);
v___x_1450_ = lean_nat_dec_lt(v___x_1448_, v___x_1449_);
lean_dec(v___x_1448_);
if (v___x_1450_ == 0)
{
lean_object* v_ks_1451_; lean_object* v_vs_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_ks_1451_ = lean_ctor_get(v_newNode_1445_, 0);
lean_inc_ref(v_ks_1451_);
v_vs_1452_ = lean_ctor_get(v_newNode_1445_, 1);
lean_inc_ref(v_vs_1452_);
lean_dec_ref(v_newNode_1445_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1389_, v_ks_1451_, v_vs_1452_, v___x_1453_, v___x_1454_);
lean_dec_ref(v_vs_1452_);
lean_dec_ref(v_ks_1451_);
return v___x_1455_;
}
else
{
return v_newNode_1445_;
}
}
else
{
return v_newNode_1445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1458_, lean_object* v_keys_1459_, lean_object* v_vals_1460_, lean_object* v_i_1461_, lean_object* v_entries_1462_){
_start:
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_array_get_size(v_keys_1459_);
v___x_1464_ = lean_nat_dec_lt(v_i_1461_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v_i_1461_);
return v_entries_1462_;
}
else
{
lean_object* v_k_1465_; lean_object* v_v_1466_; uint64_t v___y_1468_; 
v_k_1465_ = lean_array_fget_borrowed(v_keys_1459_, v_i_1461_);
v_v_1466_ = lean_array_fget_borrowed(v_vals_1460_, v_i_1461_);
if (lean_obj_tag(v_k_1465_) == 0)
{
uint64_t v___x_1479_; 
v___x_1479_ = 1723ULL;
v___y_1468_ = v___x_1479_;
goto v___jp_1467_;
}
else
{
uint64_t v_hash_1480_; 
v_hash_1480_ = lean_ctor_get_uint64(v_k_1465_, sizeof(void*)*2);
v___y_1468_ = v_hash_1480_;
goto v___jp_1467_;
}
v___jp_1467_:
{
size_t v_h_1469_; size_t v___x_1470_; lean_object* v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; size_t v_h_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_h_1469_ = lean_uint64_to_usize(v___y_1468_);
v___x_1470_ = ((size_t)5ULL);
v___x_1471_ = lean_unsigned_to_nat(1u);
v___x_1472_ = ((size_t)1ULL);
v___x_1473_ = lean_usize_sub(v_depth_1458_, v___x_1472_);
v___x_1474_ = lean_usize_mul(v___x_1470_, v___x_1473_);
v_h_1475_ = lean_usize_shift_right(v_h_1469_, v___x_1474_);
v___x_1476_ = lean_nat_add(v_i_1461_, v___x_1471_);
lean_dec(v_i_1461_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
v___x_1477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1462_, v_h_1475_, v_depth_1458_, v_k_1465_, v_v_1466_);
v_i_1461_ = v___x_1476_;
v_entries_1462_ = v___x_1477_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1481_, lean_object* v_keys_1482_, lean_object* v_vals_1483_, lean_object* v_i_1484_, lean_object* v_entries_1485_){
_start:
{
size_t v_depth_boxed_1486_; lean_object* v_res_1487_; 
v_depth_boxed_1486_ = lean_unbox_usize(v_depth_1481_);
lean_dec(v_depth_1481_);
v_res_1487_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1486_, v_keys_1482_, v_vals_1483_, v_i_1484_, v_entries_1485_);
lean_dec_ref(v_vals_1483_);
lean_dec_ref(v_keys_1482_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
size_t v_x_909__boxed_1493_; size_t v_x_910__boxed_1494_; lean_object* v_res_1495_; 
v_x_909__boxed_1493_ = lean_unbox_usize(v_x_1489_);
lean_dec(v_x_1489_);
v_x_910__boxed_1494_ = lean_unbox_usize(v_x_1490_);
lean_dec(v_x_1490_);
v_res_1495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1488_, v_x_909__boxed_1493_, v_x_910__boxed_1494_, v_x_1491_, v_x_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
uint64_t v___y_1500_; 
if (lean_obj_tag(v_x_1497_) == 0)
{
uint64_t v___x_1504_; 
v___x_1504_ = 1723ULL;
v___y_1500_ = v___x_1504_;
goto v___jp_1499_;
}
else
{
uint64_t v_hash_1505_; 
v_hash_1505_ = lean_ctor_get_uint64(v_x_1497_, sizeof(void*)*2);
v___y_1500_ = v_hash_1505_;
goto v___jp_1499_;
}
v___jp_1499_:
{
size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = lean_uint64_to_usize(v___y_1500_);
v___x_1502_ = ((size_t)1ULL);
v___x_1503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1496_, v___x_1501_, v___x_1502_, v_x_1497_, v_x_1498_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1511_, lean_object* v_as_1512_, size_t v_i_1513_, size_t v_stop_1514_, lean_object* v_b_1515_){
_start:
{
lean_object* v___y_1517_; uint8_t v___x_1521_; 
v___x_1521_ = lean_usize_dec_eq(v_i_1513_, v_stop_1514_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_array_uget_borrowed(v_as_1512_, v_i_1513_);
v___x_1523_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1515_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; 
lean_inc(v_declName_1511_);
lean_inc(v___x_1522_);
v___x_1524_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1515_, v___x_1522_, v_declName_1511_);
v___y_1517_ = v___x_1524_;
goto v___jp_1516_;
}
else
{
lean_object* v_val_1525_; uint8_t v___x_1526_; 
v_val_1525_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1526_ = lean_name_eq(v_val_1525_, v_declName_1511_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1527_ = 1;
v___x_1528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1530_ = lean_unsigned_to_nat(227u);
v___x_1531_ = lean_unsigned_to_nat(10u);
v___x_1532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1522_);
v___x_1533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1522_, v___x_1527_);
v___x_1534_ = lean_string_append(v___x_1532_, v___x_1533_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1536_ = lean_string_append(v___x_1534_, v___x_1535_);
v___x_1537_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1525_, v___x_1527_);
v___x_1538_ = lean_string_append(v___x_1536_, v___x_1537_);
lean_dec_ref(v___x_1537_);
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1540_ = lean_string_append(v___x_1538_, v___x_1539_);
v___x_1541_ = l_mkPanicMessageWithDecl(v___x_1528_, v___x_1529_, v___x_1530_, v___x_1531_, v___x_1540_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = lean_panic_fn_borrowed(v_b_1515_, v___x_1541_);
lean_dec_ref(v_b_1515_);
v___y_1517_ = v___x_1542_;
goto v___jp_1516_;
}
else
{
lean_dec(v_val_1525_);
v___y_1517_ = v_b_1515_;
goto v___jp_1516_;
}
}
}
else
{
lean_dec(v_declName_1511_);
return v_b_1515_;
}
v___jp_1516_:
{
size_t v___x_1518_; size_t v___x_1519_; 
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1513_, v___x_1518_);
v_i_1513_ = v___x_1519_;
v_b_1515_ = v___y_1517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1543_, lean_object* v_as_1544_, lean_object* v_i_1545_, lean_object* v_stop_1546_, lean_object* v_b_1547_){
_start:
{
size_t v_i_boxed_1548_; size_t v_stop_boxed_1549_; lean_object* v_res_1550_; 
v_i_boxed_1548_ = lean_unbox_usize(v_i_1545_);
lean_dec(v_i_1545_);
v_stop_boxed_1549_ = lean_unbox_usize(v_stop_1546_);
lean_dec(v_stop_1546_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1543_, v_as_1544_, v_i_boxed_1548_, v_stop_boxed_1549_, v_b_1547_);
lean_dec_ref(v_as_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1551_, lean_object* v_declName_1552_, lean_object* v_s_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_array_get_size(v_eqThms_1551_);
v___x_1556_ = lean_nat_dec_lt(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_dec(v_declName_1552_);
return v_s_1553_;
}
else
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_le(v___x_1555_, v___x_1555_);
if (v___x_1557_ == 0)
{
if (v___x_1556_ == 0)
{
lean_dec(v_declName_1552_);
return v_s_1553_;
}
else
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = ((size_t)0ULL);
v___x_1559_ = lean_usize_of_nat(v___x_1555_);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1552_, v_eqThms_1551_, v___x_1558_, v___x_1559_, v_s_1553_);
return v___x_1560_;
}
}
else
{
size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = lean_usize_of_nat(v___x_1555_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1552_, v_eqThms_1551_, v___x_1561_, v___x_1562_, v_s_1553_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1564_, lean_object* v_declName_1565_, lean_object* v_s_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1564_, v_declName_1565_, v_s_1566_);
lean_dec_ref(v_eqThms_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1568_, lean_object* v_eqThms_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___f_1572_; lean_object* v___x_1573_; lean_object* v_env_1574_; lean_object* v_nextMacroScope_1575_; lean_object* v_ngen_1576_; lean_object* v_auxDeclNGen_1577_; lean_object* v_traceState_1578_; lean_object* v_recordedDeps_1579_; lean_object* v_messages_1580_; lean_object* v_infoState_1581_; lean_object* v_snapshotTasks_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1598_; 
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1572_, 0, v_eqThms_1569_);
lean_closure_set(v___f_1572_, 1, v_declName_1568_);
v___x_1573_ = lean_st_ref_take(v_a_1570_);
v_env_1574_ = lean_ctor_get(v___x_1573_, 0);
v_nextMacroScope_1575_ = lean_ctor_get(v___x_1573_, 1);
v_ngen_1576_ = lean_ctor_get(v___x_1573_, 2);
v_auxDeclNGen_1577_ = lean_ctor_get(v___x_1573_, 3);
v_traceState_1578_ = lean_ctor_get(v___x_1573_, 4);
v_recordedDeps_1579_ = lean_ctor_get(v___x_1573_, 6);
v_messages_1580_ = lean_ctor_get(v___x_1573_, 7);
v_infoState_1581_ = lean_ctor_get(v___x_1573_, 8);
v_snapshotTasks_1582_ = lean_ctor_get(v___x_1573_, 9);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v___x_1573_, 5);
lean_dec(v_unused_1599_);
v___x_1584_ = v___x_1573_;
v_isShared_1585_ = v_isSharedCheck_1598_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_snapshotTasks_1582_);
lean_inc(v_infoState_1581_);
lean_inc(v_messages_1580_);
lean_inc(v_recordedDeps_1579_);
lean_inc(v_traceState_1578_);
lean_inc(v_auxDeclNGen_1577_);
lean_inc(v_ngen_1576_);
lean_inc(v_nextMacroScope_1575_);
lean_inc(v_env_1574_);
lean_dec(v___x_1573_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1598_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v_asyncMode_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1586_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1587_ = lean_ctor_get(v___x_1586_, 2);
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_box(0);
v___x_1590_ = 1;
v___x_1591_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1586_, v_env_1574_, v___f_1572_, v_asyncMode_1587_, v___x_1589_, v___x_1590_);
v___x_1592_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 5, v___x_1592_);
lean_ctor_set(v___x_1584_, 0, v___x_1591_);
v___x_1594_ = v___x_1584_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_nextMacroScope_1575_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_ngen_1576_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_auxDeclNGen_1577_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_traceState_1578_);
lean_ctor_set(v_reuseFailAlloc_1597_, 5, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1597_, 6, v_recordedDeps_1579_);
lean_ctor_set(v_reuseFailAlloc_1597_, 7, v_messages_1580_);
lean_ctor_set(v_reuseFailAlloc_1597_, 8, v_infoState_1581_);
lean_ctor_set(v_reuseFailAlloc_1597_, 9, v_snapshotTasks_1582_);
v___x_1594_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_st_ref_put(v_a_1570_, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1588_);
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1600_, lean_object* v_eqThms_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1600_, v_eqThms_1601_, v_a_1602_);
lean_dec(v_a_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1605_, lean_object* v_eqThms_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1605_, v_eqThms_1606_, v_a_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1611_, lean_object* v_eqThms_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1611_, v_eqThms_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1618_, v_x_1619_, v_x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1622_, lean_object* v_x_1623_, size_t v_x_1624_, size_t v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1623_, v_x_1624_, v_x_1625_, v_x_1626_, v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
size_t v_x_1231__boxed_1635_; size_t v_x_1232__boxed_1636_; lean_object* v_res_1637_; 
v_x_1231__boxed_1635_ = lean_unbox_usize(v_x_1631_);
lean_dec(v_x_1631_);
v_x_1232__boxed_1636_ = lean_unbox_usize(v_x_1632_);
lean_dec(v_x_1632_);
v_res_1637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1629_, v_x_1630_, v_x_1231__boxed_1635_, v_x_1232__boxed_1636_, v_x_1633_, v_x_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1638_, lean_object* v_n_1639_, lean_object* v_k_1640_, lean_object* v_v_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1639_, v_k_1640_, v_v_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1643_, size_t v_depth_1644_, lean_object* v_keys_1645_, lean_object* v_vals_1646_, lean_object* v_heq_1647_, lean_object* v_i_1648_, lean_object* v_entries_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1644_, v_keys_1645_, v_vals_1646_, v_i_1648_, v_entries_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_depth_1652_, lean_object* v_keys_1653_, lean_object* v_vals_1654_, lean_object* v_heq_1655_, lean_object* v_i_1656_, lean_object* v_entries_1657_){
_start:
{
size_t v_depth_boxed_1658_; lean_object* v_res_1659_; 
v_depth_boxed_1658_ = lean_unbox_usize(v_depth_1652_);
lean_dec(v_depth_1652_);
v_res_1659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1651_, v_depth_boxed_1658_, v_keys_1653_, v_vals_1654_, v_heq_1655_, v_i_1656_, v_entries_1657_);
lean_dec_ref(v_vals_1654_);
lean_dec_ref(v_keys_1653_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1661_, v_x_1662_, v_x_1663_, v_x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1666_, lean_object* v_env_1667_, lean_object* v_idx_1668_, lean_object* v_eqs_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_nextEq_1676_; uint8_t v___x_1677_; 
v___x_1671_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1672_ = lean_unsigned_to_nat(1u);
v___x_1673_ = lean_nat_add(v_idx_1668_, v___x_1672_);
lean_dec(v_idx_1668_);
lean_inc(v___x_1673_);
v___x_1674_ = l_Nat_reprFast(v___x_1673_);
v___x_1675_ = lean_string_append(v___x_1671_, v___x_1674_);
lean_dec_ref(v___x_1674_);
lean_inc(v_declName_1666_);
lean_inc_ref(v_env_1667_);
v_nextEq_1676_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1667_, v_declName_1666_, v___x_1675_);
v___x_1677_ = l_Lean_Environment_containsOnBranch(v_env_1667_, v_nextEq_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
lean_dec(v_nextEq_1676_);
lean_dec(v___x_1673_);
lean_dec_ref(v_env_1667_);
lean_dec(v_declName_1666_);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_eqs_1669_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_array_push(v_eqs_1669_, v_nextEq_1676_);
v_idx_1668_ = v___x_1673_;
v_eqs_1669_ = v___x_1679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1681_, lean_object* v_env_1682_, lean_object* v_idx_1683_, lean_object* v_eqs_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1681_, v_env_1682_, v_idx_1683_, v_eqs_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1687_, lean_object* v_env_1688_, lean_object* v_idx_1689_, lean_object* v_eqs_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1687_, v_env_1688_, v_idx_1689_, v_eqs_1690_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1697_, lean_object* v_env_1698_, lean_object* v_idx_1699_, lean_object* v_eqs_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1697_, v_env_1698_, v_idx_1699_, v_eqs_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1710_; lean_object* v_env_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1710_ = lean_st_ref_get(v_a_1708_);
v_env_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc_ref_n(v_env_1711_, 3);
lean_dec(v___x_1710_);
v___x_1712_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1707_);
v___x_1713_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1711_, v_declName_1707_, v___x_1712_);
v___x_1714_ = 1;
lean_inc(v___x_1713_);
v___x_1715_ = l_Lean_Environment_contains(v_env_1711_, v___x_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec(v___x_1713_);
lean_dec_ref(v_env_1711_);
lean_dec(v_declName_1707_);
v___x_1716_ = lean_box(0);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_mk_empty_array_with_capacity(v___x_1718_);
v___x_1720_ = lean_array_push(v___x_1719_, v___x_1713_);
lean_inc(v_declName_1707_);
v___x_1721_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1707_, v_env_1711_, v___x_1718_, v___x_1720_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc_n(v_a_1722_, 2);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1707_, v_a_1722_, v_a_1708_);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v___x_1723_, 0);
lean_dec(v_unused_1732_);
v___x_1725_ = v___x_1723_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_dec(v___x_1723_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_a_1722_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_declName_1707_);
v_a_1733_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1721_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1721_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1741_, v_a_1742_);
lean_dec(v_a_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1745_, v_a_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1759_, lean_object* v_localInsts_1760_, lean_object* v_x_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1759_, v_localInsts_1760_, v_x_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1767_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1767_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1784_, lean_object* v_localInsts_1785_, lean_object* v_x_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1784_, v_localInsts_1785_, v_x_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1793_, lean_object* v_lctx_1794_, lean_object* v_localInsts_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1794_, v_localInsts_1795_, v_x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_lctx_1804_, lean_object* v_localInsts_1805_, lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1803_, v_lctx_1804_, v_localInsts_1805_, v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1816_, lean_object* v_as_x27_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
if (lean_obj_tag(v_as_x27_1817_) == 0)
{
lean_object* v___x_1824_; 
lean_dec(v_declName_1816_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1818_);
return v___x_1824_;
}
else
{
lean_object* v_head_1825_; lean_object* v_tail_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_b_1818_);
v_head_1825_ = lean_ctor_get(v_as_x27_1817_, 0);
v_tail_1826_ = lean_ctor_get(v_as_x27_1817_, 1);
v___x_1827_ = lean_box(0);
v___x_1828_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1825_);
lean_inc(v___y_1822_);
lean_inc_ref(v___y_1821_);
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1819_);
lean_inc(v_declName_1816_);
v___x_1829_ = lean_apply_6(v_head_1825_, v_declName_1816_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, lean_box(0));
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
if (lean_obj_tag(v_a_1830_) == 1)
{
lean_object* v_val_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1841_; 
v_val_1831_ = lean_ctor_get(v_a_1830_, 0);
lean_inc(v_val_1831_);
v___x_1832_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1816_, v_val_1831_, v___y_1822_);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v___x_1832_, 0);
lean_dec(v_unused_1842_);
v___x_1834_ = v___x_1832_;
v_isShared_1835_ = v_isSharedCheck_1841_;
goto v_resetjp_1833_;
}
else
{
lean_dec(v___x_1832_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1841_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1830_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set(v___x_1837_, 1, v___x_1827_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1837_);
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_dec(v_a_1830_);
v_as_x27_1817_ = v_tail_1826_;
v_b_1818_ = v___x_1828_;
goto _start;
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_declName_1816_);
v_a_1844_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1829_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1829_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1852_, lean_object* v_as_x27_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1852_, v_as_x27_1853_, v_b_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v_as_x27_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
lean_inc(v_declName_1861_);
v___x_1867_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1905_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1905_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1905_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_unbox(v_a_1868_);
lean_dec(v_a_1868_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_dec(v_declName_1861_);
v___x_1873_ = lean_box(0);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1873_);
v___x_1875_ = v___x_1870_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
else
{
lean_object* v___x_1877_; 
lean_del_object(v___x_1870_);
lean_inc(v_declName_1861_);
v___x_1877_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1861_, v___y_1865_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
if (lean_obj_tag(v_a_1878_) == 1)
{
lean_dec(v_declName_1861_);
return v___x_1877_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1880_ = lean_st_ref_get(v___x_1879_);
v___x_1881_ = lean_box(0);
v___x_1882_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1883_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1861_, v___x_1880_, v___x_1882_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___x_1880_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1896_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_fst_1888_; 
v_fst_1888_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_fst_1888_);
lean_dec(v_a_1884_);
if (lean_obj_tag(v_fst_1888_) == 0)
{
lean_object* v___x_1890_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1881_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1881_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
else
{
lean_object* v_val_1892_; lean_object* v___x_1894_; 
v_val_1892_ = lean_ctor_get(v_fst_1888_, 0);
lean_inc(v_val_1892_);
lean_dec_ref_known(v_fst_1888_, 1);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v_val_1892_);
v___x_1894_ = v___x_1886_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_val_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_a_1897_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1883_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1883_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
lean_dec(v_declName_1861_);
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_declName_1861_);
v_a_1906_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1867_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1867_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1920_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1923_ = lean_box(1);
v___x_1924_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1925_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___x_1924_);
lean_ctor_set(v___x_1926_, 2, v___x_1923_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___f_1935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1935_, 0, v_declName_1929_);
v___x_1936_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1937_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1938_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1936_, v___x_1937_, v___f_1935_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1946_, lean_object* v_as_1947_, lean_object* v_as_x27_1948_, lean_object* v_b_1949_, lean_object* v_a_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1946_, v_as_x27_1948_, v_b_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1957_, lean_object* v_as_1958_, lean_object* v_as_x27_1959_, lean_object* v_b_1960_, lean_object* v_a_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1957_, v_as_1958_, v_as_x27_1959_, v_b_1960_, v_a_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_as_x27_1959_);
lean_dec(v_as_1958_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1974_ = lean_unsigned_to_nat(32u);
v___x_1975_ = lean_mk_empty_array_with_capacity(v___x_1974_);
lean_dec_ref(v___x_1975_);
v___x_1976_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1968_);
v___x_1978_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1978_, 0, v_declName_1968_);
v___x_1979_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1979_, 0, lean_box(0));
lean_closure_set(v___x_1979_, 1, v_declName_1968_);
lean_closure_set(v___x_1979_, 2, v___x_1978_);
v___x_1980_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1976_, v___x_1977_, v___x_1979_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_1988_, lean_object* v_opt_1989_){
_start:
{
lean_object* v_name_1990_; lean_object* v_defValue_1991_; lean_object* v_map_1992_; lean_object* v___x_1993_; 
v_name_1990_ = lean_ctor_get(v_opt_1989_, 0);
v_defValue_1991_ = lean_ctor_get(v_opt_1989_, 1);
v_map_1992_ = lean_ctor_get(v_opts_1988_, 0);
v___x_1993_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1992_, v_name_1990_);
if (lean_obj_tag(v___x_1993_) == 0)
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_unbox(v_defValue_1991_);
return v___x_1994_;
}
else
{
lean_object* v_val_1995_; 
v_val_1995_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_val_1995_);
lean_dec_ref_known(v___x_1993_, 1);
if (lean_obj_tag(v_val_1995_) == 1)
{
uint8_t v_v_1996_; 
v_v_1996_ = lean_ctor_get_uint8(v_val_1995_, 0);
lean_dec_ref_known(v_val_1995_, 0);
return v_v_1996_;
}
else
{
uint8_t v___x_1997_; 
lean_dec(v_val_1995_);
v___x_1997_ = lean_unbox(v_defValue_1991_);
return v___x_1997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_1998_, lean_object* v_opt_1999_){
_start:
{
uint8_t v_res_2000_; lean_object* v_r_2001_; 
v_res_2000_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_1998_, v_opt_1999_);
lean_dec_ref(v_opt_1999_);
lean_dec_ref(v_opts_1998_);
v_r_2001_ = lean_box(v_res_2000_);
return v_r_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2002_, lean_object* v_as_2003_, size_t v_sz_2004_, size_t v_i_2005_, lean_object* v_b_2006_){
_start:
{
lean_object* v_a_2009_; uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_b_2006_);
return v___x_2014_;
}
else
{
lean_object* v_a_2015_; lean_object* v_defValue_2016_; uint8_t v___x_2017_; uint8_t v___y_2031_; uint8_t v___x_2032_; 
v_a_2015_ = lean_array_uget(v_as_2003_, v_i_2005_);
v_defValue_2016_ = lean_ctor_get(v_a_2015_, 1);
v___x_2017_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2002_, v_a_2015_);
v___x_2032_ = lean_unbox(v_defValue_2016_);
if (v___x_2032_ == 0)
{
if (v___x_2017_ == 0)
{
v___y_2031_ = v___x_2013_;
goto v___jp_2030_;
}
else
{
goto v___jp_2018_;
}
}
else
{
v___y_2031_ = v___x_2017_;
goto v___jp_2030_;
}
v___jp_2018_:
{
lean_object* v_name_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
v_name_2019_ = lean_ctor_get(v_a_2015_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v_a_2015_, 1);
lean_dec(v_unused_2029_);
v___x_2021_ = v_a_2015_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_name_2019_);
lean_dec(v_a_2015_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2023_, 0, v___x_2017_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 1, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_name_2019_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_array_push(v_b_2006_, v___x_2025_);
v_a_2009_ = v___x_2026_;
goto v___jp_2008_;
}
}
}
v___jp_2030_:
{
if (v___y_2031_ == 0)
{
goto v___jp_2018_;
}
else
{
lean_dec(v_a_2015_);
v_a_2009_ = v_b_2006_;
goto v___jp_2008_;
}
}
}
v___jp_2008_:
{
size_t v___x_2010_; size_t v___x_2011_; 
v___x_2010_ = ((size_t)1ULL);
v___x_2011_ = lean_usize_add(v_i_2005_, v___x_2010_);
v_i_2005_ = v___x_2011_;
v_b_2006_ = v_a_2009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2033_, lean_object* v_as_2034_, lean_object* v_sz_2035_, lean_object* v_i_2036_, lean_object* v_b_2037_, lean_object* v___y_2038_){
_start:
{
size_t v_sz_boxed_2039_; size_t v_i_boxed_2040_; lean_object* v_res_2041_; 
v_sz_boxed_2039_ = lean_unbox_usize(v_sz_2035_);
lean_dec(v_sz_2035_);
v_i_boxed_2040_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2033_, v_as_2034_, v_sz_boxed_2039_, v_i_boxed_2040_, v_b_2037_);
lean_dec_ref(v_as_2034_);
lean_dec_ref(v___x_2033_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v_env_2049_; uint8_t v___x_2050_; lean_object* v_env_2051_; lean_object* v___x_2052_; lean_object* v_toCold_2053_; lean_object* v_mctx_2054_; lean_object* v_lctx_2055_; lean_object* v_options_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2048_ = lean_st_ref_get(v___y_2046_);
v_env_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_ref(v_env_2049_);
lean_dec(v___x_2048_);
v___x_2050_ = 0;
v_env_2051_ = l_Lean_Environment_setRecordingDeps(v_env_2049_, v___x_2050_);
v___x_2052_ = lean_st_ref_get(v___y_2044_);
v_toCold_2053_ = lean_ctor_get(v___y_2045_, 0);
v_mctx_2054_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_mctx_2054_);
lean_dec(v___x_2052_);
v_lctx_2055_ = lean_ctor_get(v___y_2043_, 2);
v_options_2056_ = lean_ctor_get(v_toCold_2053_, 2);
lean_inc_ref(v_options_2056_);
lean_inc_ref(v_lctx_2055_);
v___x_2057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2057_, 0, v_env_2051_);
lean_ctor_set(v___x_2057_, 1, v_mctx_2054_);
lean_ctor_set(v___x_2057_, 2, v_lctx_2055_);
lean_ctor_set(v___x_2057_, 3, v_options_2056_);
v___x_2058_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v_msgData_2042_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2066_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2067_; double v___x_2068_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_float_of_nat(v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2072_, lean_object* v_msg_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_ref_2079_; lean_object* v___x_2080_; lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2126_; 
v_ref_2079_ = lean_ctor_get(v___y_2076_, 2);
v___x_2080_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2126_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2126_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v_traceState_2086_; lean_object* v_env_2087_; lean_object* v_nextMacroScope_2088_; lean_object* v_ngen_2089_; lean_object* v_auxDeclNGen_2090_; lean_object* v_cache_2091_; lean_object* v_recordedDeps_2092_; lean_object* v_messages_2093_; lean_object* v_infoState_2094_; lean_object* v_snapshotTasks_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2125_; 
v___x_2085_ = lean_st_ref_take(v___y_2077_);
v_traceState_2086_ = lean_ctor_get(v___x_2085_, 4);
v_env_2087_ = lean_ctor_get(v___x_2085_, 0);
v_nextMacroScope_2088_ = lean_ctor_get(v___x_2085_, 1);
v_ngen_2089_ = lean_ctor_get(v___x_2085_, 2);
v_auxDeclNGen_2090_ = lean_ctor_get(v___x_2085_, 3);
v_cache_2091_ = lean_ctor_get(v___x_2085_, 5);
v_recordedDeps_2092_ = lean_ctor_get(v___x_2085_, 6);
v_messages_2093_ = lean_ctor_get(v___x_2085_, 7);
v_infoState_2094_ = lean_ctor_get(v___x_2085_, 8);
v_snapshotTasks_2095_ = lean_ctor_get(v___x_2085_, 9);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2097_ = v___x_2085_;
v_isShared_2098_ = v_isSharedCheck_2125_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_snapshotTasks_2095_);
lean_inc(v_infoState_2094_);
lean_inc(v_messages_2093_);
lean_inc(v_recordedDeps_2092_);
lean_inc(v_cache_2091_);
lean_inc(v_traceState_2086_);
lean_inc(v_auxDeclNGen_2090_);
lean_inc(v_ngen_2089_);
lean_inc(v_nextMacroScope_2088_);
lean_inc(v_env_2087_);
lean_dec(v___x_2085_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2125_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
uint64_t v_tid_2099_; lean_object* v_traces_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2124_; 
v_tid_2099_ = lean_ctor_get_uint64(v_traceState_2086_, sizeof(void*)*1);
v_traces_2100_ = lean_ctor_get(v_traceState_2086_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_traceState_2086_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2102_ = v_traceState_2086_;
v_isShared_2103_ = v_isSharedCheck_2124_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_traces_2100_);
lean_dec(v_traceState_2086_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2124_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; double v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2107_ = 0;
v___x_2108_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2109_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2109_, 0, v_cls_2072_);
lean_ctor_set(v___x_2109_, 1, v___x_2105_);
lean_ctor_set(v___x_2109_, 2, v___x_2108_);
lean_ctor_set_float(v___x_2109_, sizeof(void*)*3, v___x_2106_);
lean_ctor_set_float(v___x_2109_, sizeof(void*)*3 + 8, v___x_2106_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*3 + 16, v___x_2107_);
v___x_2110_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2111_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v_a_2081_);
lean_ctor_set(v___x_2111_, 2, v___x_2110_);
lean_inc(v_ref_2079_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_ref_2079_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = l_Lean_PersistentArray_push___redArg(v_traces_2100_, v___x_2112_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2113_);
v___x_2115_ = v___x_2102_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2113_);
lean_ctor_set_uint64(v_reuseFailAlloc_2123_, sizeof(void*)*1, v_tid_2099_);
v___x_2115_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2117_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v___x_2115_);
v___x_2117_ = v___x_2097_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_env_2087_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_nextMacroScope_2088_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_ngen_2089_);
lean_ctor_set(v_reuseFailAlloc_2122_, 3, v_auxDeclNGen_2090_);
lean_ctor_set(v_reuseFailAlloc_2122_, 4, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2122_, 5, v_cache_2091_);
lean_ctor_set(v_reuseFailAlloc_2122_, 6, v_recordedDeps_2092_);
lean_ctor_set(v_reuseFailAlloc_2122_, 7, v_messages_2093_);
lean_ctor_set(v_reuseFailAlloc_2122_, 8, v_infoState_2094_);
lean_ctor_set(v_reuseFailAlloc_2122_, 9, v_snapshotTasks_2095_);
v___x_2117_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_st_ref_put(v___y_2077_, v___x_2117_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2104_);
v___x_2120_ = v___x_2083_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2104_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2127_, v_msg_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2134_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2137_; size_t v_sz_2138_; 
v___x_2137_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2138_ = lean_array_size(v___x_2137_);
return v_sz_2138_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2140_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
lean_ctor_set(v___x_2140_, 2, v___x_2139_);
lean_ctor_set(v___x_2140_, 3, v___x_2139_);
lean_ctor_set(v___x_2140_, 4, v___x_2139_);
lean_ctor_set(v___x_2140_, 5, v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2149_ = l_Lean_Name_append(v___x_2148_, v___x_2147_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; size_t v_sz_2163_; size_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2159_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2156_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2162_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2163_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2164_ = ((size_t)0ULL);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2159_, v___x_2162_, v_sz_2163_, v___x_2164_, v___x_2161_);
lean_dec_ref(v___x_2159_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2229_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2229_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2229_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___y_2173_; lean_object* v___y_2174_; 
v___x_2170_ = lean_array_get_size(v_a_2166_);
v___x_2171_ = lean_nat_dec_eq(v___x_2170_, v___x_2160_);
if (v___x_2171_ == 0)
{
lean_object* v_toCold_2216_; lean_object* v_options_2217_; uint8_t v_hasTrace_2218_; 
v_toCold_2216_ = lean_ctor_get(v_a_2156_, 0);
v_options_2217_ = lean_ctor_get(v_toCold_2216_, 2);
v_hasTrace_2218_ = lean_ctor_get_uint8(v_options_2217_, sizeof(void*)*1);
if (v_hasTrace_2218_ == 0)
{
v___y_2173_ = v_a_2155_;
v___y_2174_ = v_a_2157_;
goto v___jp_2172_;
}
else
{
lean_object* v_inheritedTraceOptions_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_inheritedTraceOptions_2219_ = lean_ctor_get(v_toCold_2216_, 11);
v___x_2220_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2221_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2222_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2219_, v_options_2217_, v___x_2221_);
if (v___x_2222_ == 0)
{
v___y_2173_ = v_a_2155_;
v___y_2174_ = v_a_2157_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2223_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2153_);
v___x_2224_ = l_Lean_MessageData_ofName(v_declName_2153_);
v___x_2225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2220_, v___x_2225_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_dec_ref_known(v___x_2226_, 1);
v___y_2173_ = v_a_2155_;
v___y_2174_ = v_a_2157_;
goto v___jp_2172_;
}
else
{
lean_del_object(v___x_2168_);
lean_dec(v_a_2166_);
lean_dec(v_declName_2153_);
return v___x_2226_;
}
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_del_object(v___x_2168_);
lean_dec(v_a_2166_);
lean_dec(v_declName_2153_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
v___jp_2172_:
{
lean_object* v___x_2175_; lean_object* v_env_2176_; lean_object* v_nextMacroScope_2177_; lean_object* v_ngen_2178_; lean_object* v_auxDeclNGen_2179_; lean_object* v_traceState_2180_; lean_object* v_recordedDeps_2181_; lean_object* v_messages_2182_; lean_object* v_infoState_2183_; lean_object* v_snapshotTasks_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2214_; 
v___x_2175_ = lean_st_ref_take(v___y_2174_);
v_env_2176_ = lean_ctor_get(v___x_2175_, 0);
v_nextMacroScope_2177_ = lean_ctor_get(v___x_2175_, 1);
v_ngen_2178_ = lean_ctor_get(v___x_2175_, 2);
v_auxDeclNGen_2179_ = lean_ctor_get(v___x_2175_, 3);
v_traceState_2180_ = lean_ctor_get(v___x_2175_, 4);
v_recordedDeps_2181_ = lean_ctor_get(v___x_2175_, 6);
v_messages_2182_ = lean_ctor_get(v___x_2175_, 7);
v_infoState_2183_ = lean_ctor_get(v___x_2175_, 8);
v_snapshotTasks_2184_ = lean_ctor_get(v___x_2175_, 9);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2175_, 5);
lean_dec(v_unused_2215_);
v___x_2186_ = v___x_2175_;
v_isShared_2187_ = v_isSharedCheck_2214_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snapshotTasks_2184_);
lean_inc(v_infoState_2183_);
lean_inc(v_messages_2182_);
lean_inc(v_recordedDeps_2181_);
lean_inc(v_traceState_2180_);
lean_inc(v_auxDeclNGen_2179_);
lean_inc(v_ngen_2178_);
lean_inc(v_nextMacroScope_2177_);
lean_inc(v_env_2176_);
lean_dec(v___x_2175_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2214_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2188_ = l_Lean_Meta_eqnOptionsExt;
v___x_2189_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2188_, v_env_2176_, v_declName_2153_, v_a_2166_, v___x_2171_);
v___x_2190_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 5, v___x_2190_);
lean_ctor_set(v___x_2186_, 0, v___x_2189_);
v___x_2192_ = v___x_2186_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_nextMacroScope_2177_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_ngen_2178_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v_auxDeclNGen_2179_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v_traceState_2180_);
lean_ctor_set(v_reuseFailAlloc_2213_, 5, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2213_, 6, v_recordedDeps_2181_);
lean_ctor_set(v_reuseFailAlloc_2213_, 7, v_messages_2182_);
lean_ctor_set(v_reuseFailAlloc_2213_, 8, v_infoState_2183_);
lean_ctor_set(v_reuseFailAlloc_2213_, 9, v_snapshotTasks_2184_);
v___x_2192_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v_mctx_2195_; lean_object* v_zetaDeltaFVarIds_2196_; lean_object* v_postponed_2197_; lean_object* v_diag_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2211_; 
v___x_2193_ = lean_st_ref_put(v___y_2174_, v___x_2192_);
v___x_2194_ = lean_st_ref_take(v___y_2173_);
v_mctx_2195_ = lean_ctor_get(v___x_2194_, 0);
v_zetaDeltaFVarIds_2196_ = lean_ctor_get(v___x_2194_, 2);
v_postponed_2197_ = lean_ctor_get(v___x_2194_, 3);
v_diag_2198_ = lean_ctor_get(v___x_2194_, 4);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; 
v_unused_2212_ = lean_ctor_get(v___x_2194_, 1);
lean_dec(v_unused_2212_);
v___x_2200_ = v___x_2194_;
v_isShared_2201_ = v_isSharedCheck_2211_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_diag_2198_);
lean_inc(v_postponed_2197_);
lean_inc(v_zetaDeltaFVarIds_2196_);
lean_inc(v_mctx_2195_);
lean_dec(v___x_2194_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2211_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 1, v___x_2203_);
v___x_2205_ = v___x_2200_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_mctx_2195_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_zetaDeltaFVarIds_2196_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_postponed_2197_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_diag_2198_);
v___x_2205_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = lean_st_ref_put(v___y_2173_, v___x_2205_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2202_);
v___x_2208_ = v___x_2168_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2202_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
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
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_declName_2153_);
v_a_2230_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2165_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2165_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2245_, lean_object* v_as_2246_, size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2245_, v_as_2246_, v_sz_2247_, v_i_2248_, v_b_2249_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2256_, lean_object* v_as_2257_, lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
size_t v_sz_boxed_2266_; size_t v_i_boxed_2267_; lean_object* v_res_2268_; 
v_sz_boxed_2266_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2267_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2256_, v_as_2257_, v_sz_boxed_2266_, v_i_boxed_2267_, v_b_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2257_);
lean_dec_ref(v___x_2256_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_st_mk_ref(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2275_){
_start:
{
uint8_t v___x_2277_; 
v___x_2277_ = l_Lean_initializing();
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_f_2275_);
v___x_2278_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2280_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2281_ = lean_st_ref_take(v___x_2280_);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_f_2275_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_st_ref_put(v___x_2280_, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2291_, lean_object* v_as_x27_2292_, lean_object* v_b_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
if (lean_obj_tag(v_as_x27_2292_) == 0)
{
lean_object* v___x_2299_; 
lean_dec(v_declName_2291_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v_b_2293_);
return v___x_2299_;
}
else
{
lean_object* v_head_2300_; lean_object* v_tail_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec_ref(v_b_2293_);
v_head_2300_ = lean_ctor_get(v_as_x27_2292_, 0);
v_tail_2301_ = lean_ctor_get(v_as_x27_2292_, 1);
v___x_2302_ = lean_box(0);
v___x_2303_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2300_);
lean_inc(v___y_2297_);
lean_inc_ref(v___y_2296_);
lean_inc(v___y_2295_);
lean_inc_ref(v___y_2294_);
lean_inc(v_declName_2291_);
v___x_2304_ = lean_apply_6(v_head_2300_, v_declName_2291_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, lean_box(0));
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2315_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2315_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2315_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
if (lean_obj_tag(v_a_2305_) == 1)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_dec(v_declName_2291_);
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2305_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2302_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2310_);
v___x_2312_ = v___x_2307_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
else
{
lean_del_object(v___x_2307_);
lean_dec(v_a_2305_);
v_as_x27_2292_ = v_tail_2301_;
v_b_2293_ = v___x_2303_;
goto _start;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_declName_2291_);
v_a_2316_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2304_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2304_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2324_, lean_object* v_as_x27_2325_, lean_object* v_b_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2324_, v_as_x27_2325_, v_b_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v_as_x27_2325_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2333_, lean_object* v_declName_2334_, uint8_t v_nonRec_2335_, lean_object* v___x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2345_; lean_object* v_env_2346_; uint8_t v___x_2347_; uint8_t v___x_2348_; 
v___x_2345_ = lean_st_ref_get(v___y_2340_);
v_env_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc_ref(v_env_2346_);
lean_dec(v___x_2345_);
v___x_2347_ = 1;
lean_inc(v___x_2333_);
v___x_2348_ = l_Lean_Environment_contains(v_env_2346_, v___x_2333_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_dec(v___x_2333_);
lean_inc(v_declName_2334_);
v___x_2349_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2334_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; uint8_t v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = lean_unbox(v_a_2350_);
lean_dec(v_a_2350_);
if (v___x_2351_ == 0)
{
lean_dec_ref(v___x_2336_);
lean_dec(v_declName_2334_);
goto v___jp_2342_;
}
else
{
lean_object* v___x_2352_; 
lean_inc(v_declName_2334_);
v___x_2352_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2334_, v___y_2340_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; uint8_t v___x_2354_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = lean_unbox(v_a_2353_);
lean_dec(v_a_2353_);
if (v___x_2354_ == 0)
{
if (v_nonRec_2335_ == 0)
{
lean_dec_ref(v___x_2336_);
lean_dec(v_declName_2334_);
goto v___jp_2342_;
}
else
{
lean_object* v___x_2355_; lean_object* v_env_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2355_ = lean_st_ref_get(v___y_2340_);
v_env_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc_ref(v_env_2356_);
lean_dec(v___x_2355_);
lean_inc(v_declName_2334_);
v___x_2357_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2356_, v_declName_2334_, v___x_2336_);
v___x_2358_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2334_, v___x_2357_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2358_;
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref(v___x_2336_);
v___x_2359_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2360_ = lean_st_ref_get(v___x_2359_);
v___x_2361_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2362_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2334_, v___x_2360_, v___x_2361_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___x_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2372_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2372_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2372_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v_fst_2367_; 
v_fst_2367_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_fst_2367_);
lean_dec(v_a_2363_);
if (lean_obj_tag(v_fst_2367_) == 0)
{
lean_del_object(v___x_2365_);
goto v___jp_2342_;
}
else
{
lean_object* v_val_2368_; lean_object* v___x_2370_; 
v_val_2368_ = lean_ctor_get(v_fst_2367_, 0);
lean_inc(v_val_2368_);
lean_dec_ref_known(v_fst_2367_, 1);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v_val_2368_);
v___x_2370_ = v___x_2365_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_val_2368_);
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
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_a_2373_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2362_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2362_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v___x_2336_);
lean_dec(v_declName_2334_);
v_a_2381_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2352_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2352_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___x_2336_);
lean_dec(v_declName_2334_);
v_a_2389_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2349_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2349_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec_ref(v___x_2336_);
lean_dec(v_declName_2334_);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2333_);
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
return v___x_2398_;
}
v___jp_2342_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2399_, lean_object* v_declName_2400_, lean_object* v_nonRec_2401_, lean_object* v___x_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v_nonRec_boxed_2408_; lean_object* v_res_2409_; 
v_nonRec_boxed_2408_ = lean_unbox(v_nonRec_2401_);
v_res_2409_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2399_, v_declName_2400_, v_nonRec_boxed_2408_, v___x_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_ref_2416_; lean_object* v___x_2417_; lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_ref_2416_ = lean_ctor_get(v___y_2413_, 2);
v___x_2417_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_inc(v_ref_2416_);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_ref_2416_);
lean_ctor_set(v___x_2422_, 1, v_a_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 1);
lean_ctor_set(v___x_2420_, 0, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2434_, uint8_t v_isExporting_2435_, lean_object* v___x_2436_, lean_object* v___y_2437_, lean_object* v___x_2438_, lean_object* v_a_x3f_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v_env_2442_; lean_object* v_nextMacroScope_2443_; lean_object* v_ngen_2444_; lean_object* v_auxDeclNGen_2445_; lean_object* v_traceState_2446_; lean_object* v_recordedDeps_2447_; lean_object* v_messages_2448_; lean_object* v_infoState_2449_; lean_object* v_snapshotTasks_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2475_; 
v___x_2441_ = lean_st_ref_take(v___y_2434_);
v_env_2442_ = lean_ctor_get(v___x_2441_, 0);
v_nextMacroScope_2443_ = lean_ctor_get(v___x_2441_, 1);
v_ngen_2444_ = lean_ctor_get(v___x_2441_, 2);
v_auxDeclNGen_2445_ = lean_ctor_get(v___x_2441_, 3);
v_traceState_2446_ = lean_ctor_get(v___x_2441_, 4);
v_recordedDeps_2447_ = lean_ctor_get(v___x_2441_, 6);
v_messages_2448_ = lean_ctor_get(v___x_2441_, 7);
v_infoState_2449_ = lean_ctor_get(v___x_2441_, 8);
v_snapshotTasks_2450_ = lean_ctor_get(v___x_2441_, 9);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2441_, 5);
lean_dec(v_unused_2476_);
v___x_2452_ = v___x_2441_;
v_isShared_2453_ = v_isSharedCheck_2475_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snapshotTasks_2450_);
lean_inc(v_infoState_2449_);
lean_inc(v_messages_2448_);
lean_inc(v_recordedDeps_2447_);
lean_inc(v_traceState_2446_);
lean_inc(v_auxDeclNGen_2445_);
lean_inc(v_ngen_2444_);
lean_inc(v_nextMacroScope_2443_);
lean_inc(v_env_2442_);
lean_dec(v___x_2441_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2475_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = l_Lean_Environment_setExporting(v_env_2442_, v_isExporting_2435_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 5, v___x_2436_);
lean_ctor_set(v___x_2452_, 0, v___x_2454_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_nextMacroScope_2443_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_ngen_2444_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_auxDeclNGen_2445_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_traceState_2446_);
lean_ctor_set(v_reuseFailAlloc_2474_, 5, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2474_, 6, v_recordedDeps_2447_);
lean_ctor_set(v_reuseFailAlloc_2474_, 7, v_messages_2448_);
lean_ctor_set(v_reuseFailAlloc_2474_, 8, v_infoState_2449_);
lean_ctor_set(v_reuseFailAlloc_2474_, 9, v_snapshotTasks_2450_);
v___x_2456_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_mctx_2459_; lean_object* v_zetaDeltaFVarIds_2460_; lean_object* v_postponed_2461_; lean_object* v_diag_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2472_; 
v___x_2457_ = lean_st_ref_put(v___y_2434_, v___x_2456_);
v___x_2458_ = lean_st_ref_take(v___y_2437_);
v_mctx_2459_ = lean_ctor_get(v___x_2458_, 0);
v_zetaDeltaFVarIds_2460_ = lean_ctor_get(v___x_2458_, 2);
v_postponed_2461_ = lean_ctor_get(v___x_2458_, 3);
v_diag_2462_ = lean_ctor_get(v___x_2458_, 4);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v___x_2458_, 1);
lean_dec(v_unused_2473_);
v___x_2464_ = v___x_2458_;
v_isShared_2465_ = v_isSharedCheck_2472_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_diag_2462_);
lean_inc(v_postponed_2461_);
lean_inc(v_zetaDeltaFVarIds_2460_);
lean_inc(v_mctx_2459_);
lean_dec(v___x_2458_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2472_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2466_ = lean_box(0);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v___x_2438_);
v___x_2468_ = v___x_2464_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_mctx_2459_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_zetaDeltaFVarIds_2460_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_postponed_2461_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_diag_2462_);
v___x_2468_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_st_ref_put(v___y_2437_, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2466_);
return v___x_2470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2477_, lean_object* v_isExporting_2478_, lean_object* v___x_2479_, lean_object* v___y_2480_, lean_object* v___x_2481_, lean_object* v_a_x3f_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v_isExporting_boxed_2484_; lean_object* v_res_2485_; 
v_isExporting_boxed_2484_ = lean_unbox(v_isExporting_2478_);
v_res_2485_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2477_, v_isExporting_boxed_2484_, v___x_2479_, v___y_2480_, v___x_2481_, v_a_x3f_2482_);
lean_dec(v_a_x3f_2482_);
lean_dec(v___y_2480_);
lean_dec(v___y_2477_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2486_, uint8_t v_isExporting_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v_env_2494_; lean_object* v___x_2495_; uint8_t v_isModule_2496_; 
v___x_2493_ = lean_st_ref_get(v___y_2491_);
v_env_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc_ref(v_env_2494_);
lean_dec(v___x_2493_);
v___x_2495_ = l_Lean_Environment_header(v_env_2494_);
v_isModule_2496_ = lean_ctor_get_uint8(v___x_2495_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2495_);
if (v_isModule_2496_ == 0)
{
lean_object* v___x_2497_; 
lean_dec_ref(v_env_2494_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
v___x_2497_ = lean_apply_5(v_x_2486_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, lean_box(0));
return v___x_2497_;
}
else
{
uint8_t v_isExporting_2498_; 
v_isExporting_2498_ = lean_ctor_get_uint8(v_env_2494_, sizeof(void*)*13);
lean_dec_ref(v_env_2494_);
if (v_isExporting_2487_ == 0)
{
if (v_isExporting_2498_ == 0)
{
lean_object* v___x_2565_; 
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
v___x_2565_ = lean_apply_5(v_x_2486_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, lean_box(0));
return v___x_2565_;
}
else
{
goto v___jp_2499_;
}
}
else
{
if (v_isExporting_2498_ == 0)
{
goto v___jp_2499_;
}
else
{
lean_object* v___x_2566_; 
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
v___x_2566_ = lean_apply_5(v_x_2486_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, lean_box(0));
return v___x_2566_;
}
}
v___jp_2499_:
{
lean_object* v___x_2500_; lean_object* v_env_2501_; lean_object* v_nextMacroScope_2502_; lean_object* v_ngen_2503_; lean_object* v_auxDeclNGen_2504_; lean_object* v_traceState_2505_; lean_object* v_recordedDeps_2506_; lean_object* v_messages_2507_; lean_object* v_infoState_2508_; lean_object* v_snapshotTasks_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2563_; 
v___x_2500_ = lean_st_ref_take(v___y_2491_);
v_env_2501_ = lean_ctor_get(v___x_2500_, 0);
v_nextMacroScope_2502_ = lean_ctor_get(v___x_2500_, 1);
v_ngen_2503_ = lean_ctor_get(v___x_2500_, 2);
v_auxDeclNGen_2504_ = lean_ctor_get(v___x_2500_, 3);
v_traceState_2505_ = lean_ctor_get(v___x_2500_, 4);
v_recordedDeps_2506_ = lean_ctor_get(v___x_2500_, 6);
v_messages_2507_ = lean_ctor_get(v___x_2500_, 7);
v_infoState_2508_ = lean_ctor_get(v___x_2500_, 8);
v_snapshotTasks_2509_ = lean_ctor_get(v___x_2500_, 9);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v___x_2500_, 5);
lean_dec(v_unused_2564_);
v___x_2511_ = v___x_2500_;
v_isShared_2512_ = v_isSharedCheck_2563_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_snapshotTasks_2509_);
lean_inc(v_infoState_2508_);
lean_inc(v_messages_2507_);
lean_inc(v_recordedDeps_2506_);
lean_inc(v_traceState_2505_);
lean_inc(v_auxDeclNGen_2504_);
lean_inc(v_ngen_2503_);
lean_inc(v_nextMacroScope_2502_);
lean_inc(v_env_2501_);
lean_dec(v___x_2500_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2563_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2513_ = l_Lean_Environment_setExporting(v_env_2501_, v_isExporting_2487_);
v___x_2514_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 5, v___x_2514_);
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2516_ = v___x_2511_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_nextMacroScope_2502_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_ngen_2503_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_auxDeclNGen_2504_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_traceState_2505_);
lean_ctor_set(v_reuseFailAlloc_2562_, 5, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2562_, 6, v_recordedDeps_2506_);
lean_ctor_set(v_reuseFailAlloc_2562_, 7, v_messages_2507_);
lean_ctor_set(v_reuseFailAlloc_2562_, 8, v_infoState_2508_);
lean_ctor_set(v_reuseFailAlloc_2562_, 9, v_snapshotTasks_2509_);
v___x_2516_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_mctx_2519_; lean_object* v_zetaDeltaFVarIds_2520_; lean_object* v_postponed_2521_; lean_object* v_diag_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2560_; 
v___x_2517_ = lean_st_ref_put(v___y_2491_, v___x_2516_);
v___x_2518_ = lean_st_ref_take(v___y_2489_);
v_mctx_2519_ = lean_ctor_get(v___x_2518_, 0);
v_zetaDeltaFVarIds_2520_ = lean_ctor_get(v___x_2518_, 2);
v_postponed_2521_ = lean_ctor_get(v___x_2518_, 3);
v_diag_2522_ = lean_ctor_get(v___x_2518_, 4);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; 
v_unused_2561_ = lean_ctor_get(v___x_2518_, 1);
lean_dec(v_unused_2561_);
v___x_2524_ = v___x_2518_;
v_isShared_2525_ = v_isSharedCheck_2560_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_diag_2522_);
lean_inc(v_postponed_2521_);
lean_inc(v_zetaDeltaFVarIds_2520_);
lean_inc(v_mctx_2519_);
lean_dec(v___x_2518_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2560_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_mctx_2519_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_zetaDeltaFVarIds_2520_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_postponed_2521_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_diag_2522_);
v___x_2528_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v_r_2530_; 
v___x_2529_ = lean_st_ref_put(v___y_2489_, v___x_2528_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
v_r_2530_ = lean_apply_5(v_x_2486_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, lean_box(0));
if (lean_obj_tag(v_r_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2547_; 
v_a_2531_ = lean_ctor_get(v_r_2530_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_r_2530_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2533_ = v_r_2530_;
v_isShared_2534_ = v_isSharedCheck_2547_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v_r_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2547_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
lean_inc(v_a_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 1);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v___x_2537_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2491_, v_isExporting_2498_, v___x_2514_, v___y_2489_, v___x_2526_, v___x_2536_);
lean_dec_ref(v___x_2536_);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v___x_2537_, 0);
lean_dec(v_unused_2545_);
v___x_2539_ = v___x_2537_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_dec(v___x_2537_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v_a_2531_);
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2531_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_a_2548_ = lean_ctor_get(v_r_2530_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v_r_2530_, 1);
v___x_2549_ = lean_box(0);
v___x_2550_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2491_, v_isExporting_2498_, v___x_2514_, v___y_2489_, v___x_2526_, v___x_2549_);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v___x_2550_, 0);
lean_dec(v_unused_2558_);
v___x_2552_ = v___x_2550_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_dec(v___x_2550_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set_tag(v___x_2552_, 1);
lean_ctor_set(v___x_2552_, 0, v_a_2548_);
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2548_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2567_, lean_object* v_isExporting_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
uint8_t v_isExporting_boxed_2574_; lean_object* v_res_2575_; 
v_isExporting_boxed_2574_ = lean_unbox(v_isExporting_2568_);
v_res_2575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2567_, v_isExporting_boxed_2574_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2576_, uint8_t v_when_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
if (v_when_2577_ == 0)
{
lean_object* v___x_2583_; 
lean_inc(v___y_2581_);
lean_inc_ref(v___y_2580_);
lean_inc(v___y_2579_);
lean_inc_ref(v___y_2578_);
v___x_2583_ = lean_apply_5(v_x_2576_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, lean_box(0));
return v___x_2583_;
}
else
{
uint8_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = 0;
v___x_2585_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2576_, v___x_2584_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2586_, lean_object* v_when_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
uint8_t v_when_boxed_2593_; lean_object* v_res_2594_; 
v_when_boxed_2593_ = lean_unbox(v_when_2587_);
v_res_2594_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2586_, v_when_boxed_2593_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2594_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2597_ = l_Lean_stringToMessageData(v___x_2596_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2600_ = l_Lean_stringToMessageData(v___x_2599_);
return v___x_2600_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2603_, uint8_t v_nonRec_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; lean_object* v_env_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___f_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; 
v___x_2610_ = lean_st_ref_get(v___y_2608_);
v_env_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc_ref(v_env_2611_);
lean_dec(v___x_2610_);
v___x_2612_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2603_);
v___x_2613_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2611_, v_declName_2603_, v___x_2612_);
v___x_2614_ = lean_box(v_nonRec_2604_);
lean_inc(v___x_2613_);
v___f_2615_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2615_, 0, v___x_2613_);
lean_closure_set(v___f_2615_, 1, v_declName_2603_);
lean_closure_set(v___f_2615_, 2, v___x_2614_);
lean_closure_set(v___f_2615_, 3, v___x_2612_);
v___x_2616_ = 1;
v___x_2617_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2615_, v___x_2616_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
if (lean_obj_tag(v_a_2618_) == 1)
{
lean_object* v_val_2619_; uint8_t v___x_2620_; 
v_val_2619_ = lean_ctor_get(v_a_2618_, 0);
v___x_2620_ = lean_name_eq(v_val_2619_, v___x_2613_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_inc(v_val_2619_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2621_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2622_ = l_Lean_MessageData_ofName(v_val_2619_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = l_Lean_MessageData_ofName(v___x_2613_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2629_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
else
{
lean_dec(v___x_2613_);
return v___x_2617_;
}
}
else
{
lean_dec(v___x_2613_);
return v___x_2617_;
}
}
else
{
lean_dec(v___x_2613_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2639_, lean_object* v_nonRec_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v_nonRec_boxed_2646_; lean_object* v_res_2647_; 
v_nonRec_boxed_2646_ = lean_unbox(v_nonRec_2640_);
v_res_2647_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2639_, v_nonRec_boxed_2646_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2648_, uint8_t v_nonRec_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2655_ = lean_box(v_nonRec_2649_);
v___f_2656_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2656_, 0, v_declName_2648_);
lean_closure_set(v___f_2656_, 1, v___x_2655_);
v___x_2657_ = lean_unsigned_to_nat(32u);
v___x_2658_ = lean_mk_empty_array_with_capacity(v___x_2657_);
lean_dec_ref(v___x_2658_);
v___x_2659_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2661_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2659_, v___x_2660_, v___f_2656_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2662_, lean_object* v_nonRec_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
uint8_t v_nonRec_boxed_2669_; lean_object* v_res_2670_; 
v_nonRec_boxed_2669_ = lean_unbox(v_nonRec_2663_);
v_res_2670_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2662_, v_nonRec_boxed_2669_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2671_, lean_object* v_as_2672_, lean_object* v_as_x27_2673_, lean_object* v_b_2674_, lean_object* v_a_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2671_, v_as_x27_2673_, v_b_2674_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2682_, lean_object* v_as_2683_, lean_object* v_as_x27_2684_, lean_object* v_b_2685_, lean_object* v_a_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2682_, v_as_2683_, v_as_x27_2684_, v_b_2685_, v_a_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v_as_x27_2684_);
lean_dec(v_as_2683_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2693_, lean_object* v_x_2694_, uint8_t v_isExporting_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2694_, v_isExporting_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2702_, lean_object* v_x_2703_, lean_object* v_isExporting_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_isExporting_boxed_2710_; lean_object* v_res_2711_; 
v_isExporting_boxed_2710_ = lean_unbox(v_isExporting_2704_);
v_res_2711_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2702_, v_x_2703_, v_isExporting_boxed_2710_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2712_, lean_object* v_x_2713_, uint8_t v_when_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2713_, v_when_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2721_, lean_object* v_x_2722_, lean_object* v_when_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v_when_boxed_2729_; lean_object* v_res_2730_; 
v_when_boxed_2729_ = lean_unbox(v_when_2723_);
v_res_2730_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2721_, v_x_2722_, v_when_boxed_2729_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2731_, lean_object* v_msg_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2739_, lean_object* v_msg_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2739_, v_msg_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
return v_res_2746_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_unsigned_to_nat(32u);
v___x_2748_ = lean_mk_empty_array_with_capacity(v___x_2747_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2750_ = ((size_t)5ULL);
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = lean_unsigned_to_nat(32u);
v___x_2753_ = lean_mk_empty_array_with_capacity(v___x_2752_);
v___x_2754_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2755_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v___x_2753_);
lean_ctor_set(v___x_2755_, 2, v___x_2751_);
lean_ctor_set(v___x_2755_, 3, v___x_2751_);
lean_ctor_set_usize(v___x_2755_, 4, v___x_2750_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; lean_object* v_traceState_2759_; lean_object* v_traces_2760_; lean_object* v___x_2761_; lean_object* v_traceState_2762_; lean_object* v_env_2763_; lean_object* v_nextMacroScope_2764_; lean_object* v_ngen_2765_; lean_object* v_auxDeclNGen_2766_; lean_object* v_cache_2767_; lean_object* v_recordedDeps_2768_; lean_object* v_messages_2769_; lean_object* v_infoState_2770_; lean_object* v_snapshotTasks_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2790_; 
v___x_2758_ = lean_st_ref_get(v___y_2756_);
v_traceState_2759_ = lean_ctor_get(v___x_2758_, 4);
lean_inc_ref(v_traceState_2759_);
lean_dec(v___x_2758_);
v_traces_2760_ = lean_ctor_get(v_traceState_2759_, 0);
lean_inc_ref(v_traces_2760_);
lean_dec_ref(v_traceState_2759_);
v___x_2761_ = lean_st_ref_take(v___y_2756_);
v_traceState_2762_ = lean_ctor_get(v___x_2761_, 4);
v_env_2763_ = lean_ctor_get(v___x_2761_, 0);
v_nextMacroScope_2764_ = lean_ctor_get(v___x_2761_, 1);
v_ngen_2765_ = lean_ctor_get(v___x_2761_, 2);
v_auxDeclNGen_2766_ = lean_ctor_get(v___x_2761_, 3);
v_cache_2767_ = lean_ctor_get(v___x_2761_, 5);
v_recordedDeps_2768_ = lean_ctor_get(v___x_2761_, 6);
v_messages_2769_ = lean_ctor_get(v___x_2761_, 7);
v_infoState_2770_ = lean_ctor_get(v___x_2761_, 8);
v_snapshotTasks_2771_ = lean_ctor_get(v___x_2761_, 9);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2773_ = v___x_2761_;
v_isShared_2774_ = v_isSharedCheck_2790_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snapshotTasks_2771_);
lean_inc(v_infoState_2770_);
lean_inc(v_messages_2769_);
lean_inc(v_recordedDeps_2768_);
lean_inc(v_cache_2767_);
lean_inc(v_traceState_2762_);
lean_inc(v_auxDeclNGen_2766_);
lean_inc(v_ngen_2765_);
lean_inc(v_nextMacroScope_2764_);
lean_inc(v_env_2763_);
lean_dec(v___x_2761_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2790_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
uint64_t v_tid_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2788_; 
v_tid_2775_ = lean_ctor_get_uint64(v_traceState_2762_, sizeof(void*)*1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_traceState_2762_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v_traceState_2762_, 0);
lean_dec(v_unused_2789_);
v___x_2777_ = v_traceState_2762_;
v_isShared_2778_ = v_isSharedCheck_2788_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v_traceState_2762_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2788_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2779_);
v___x_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2779_);
lean_ctor_set_uint64(v_reuseFailAlloc_2787_, sizeof(void*)*1, v_tid_2775_);
v___x_2781_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2783_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v___x_2781_);
v___x_2783_ = v___x_2773_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_env_2763_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_nextMacroScope_2764_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_ngen_2765_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_auxDeclNGen_2766_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2786_, 5, v_cache_2767_);
lean_ctor_set(v_reuseFailAlloc_2786_, 6, v_recordedDeps_2768_);
lean_ctor_set(v_reuseFailAlloc_2786_, 7, v_messages_2769_);
lean_ctor_set(v_reuseFailAlloc_2786_, 8, v_infoState_2770_);
lean_ctor_set(v_reuseFailAlloc_2786_, 9, v_snapshotTasks_2771_);
v___x_2783_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_st_ref_put(v___y_2756_, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_traces_2760_);
return v___x_2785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2791_);
lean_dec(v___y_2791_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = 0;
v___x_2807_ = lean_box(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2813_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2816_ = l_Lean_stringToMessageData(v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2817_, lean_object* v_x_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2822_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2823_ = l_Lean_MessageData_ofName(v_name_2817_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2826_, lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2826_, v_x_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v_x_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2832_){
_start:
{
if (lean_obj_tag(v_x_2832_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_a_2834_ = lean_ctor_get(v_x_2832_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_x_2832_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v_x_2832_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v_x_2832_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set_tag(v___x_2836_, 1);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v_a_2842_ = lean_ctor_get(v_x_2832_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_x_2832_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v_x_2832_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v_x_2832_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 0);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2850_);
return v_res_2852_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2853_){
_start:
{
if (lean_obj_tag(v_e_2853_) == 0)
{
uint8_t v___x_2854_; 
v___x_2854_ = 2;
return v___x_2854_;
}
else
{
lean_object* v_a_2855_; uint8_t v___x_2856_; 
v_a_2855_ = lean_ctor_get(v_e_2853_, 0);
v___x_2856_ = lean_unbox(v_a_2855_);
if (v___x_2856_ == 0)
{
uint8_t v___x_2857_; 
v___x_2857_ = 1;
return v___x_2857_;
}
else
{
uint8_t v___x_2858_; 
v___x_2858_ = 0;
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2859_){
_start:
{
uint8_t v_res_2860_; lean_object* v_r_2861_; 
v_res_2860_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2859_);
lean_dec_ref(v_e_2859_);
v_r_2861_ = lean_box(v_res_2860_);
return v_r_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2862_, size_t v_i_2863_, lean_object* v_bs_2864_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_usize_dec_lt(v_i_2863_, v_sz_2862_);
if (v___x_2865_ == 0)
{
return v_bs_2864_;
}
else
{
lean_object* v_v_2866_; lean_object* v_msg_2867_; lean_object* v___x_2868_; lean_object* v_bs_x27_2869_; size_t v___x_2870_; size_t v___x_2871_; lean_object* v___x_2872_; 
v_v_2866_ = lean_array_uget_borrowed(v_bs_2864_, v_i_2863_);
v_msg_2867_ = lean_ctor_get(v_v_2866_, 1);
lean_inc_ref(v_msg_2867_);
v___x_2868_ = lean_unsigned_to_nat(0u);
v_bs_x27_2869_ = lean_array_uset(v_bs_2864_, v_i_2863_, v___x_2868_);
v___x_2870_ = ((size_t)1ULL);
v___x_2871_ = lean_usize_add(v_i_2863_, v___x_2870_);
v___x_2872_ = lean_array_uset(v_bs_x27_2869_, v_i_2863_, v_msg_2867_);
v_i_2863_ = v___x_2871_;
v_bs_2864_ = v___x_2872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2874_, lean_object* v_i_2875_, lean_object* v_bs_2876_){
_start:
{
size_t v_sz_boxed_2877_; size_t v_i_boxed_2878_; lean_object* v_res_2879_; 
v_sz_boxed_2877_ = lean_unbox_usize(v_sz_2874_);
lean_dec(v_sz_2874_);
v_i_boxed_2878_ = lean_unbox_usize(v_i_2875_);
lean_dec(v_i_2875_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2877_, v_i_boxed_2878_, v_bs_2876_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2880_, lean_object* v_data_2881_, lean_object* v_ref_2882_, lean_object* v_msg_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_toCold_2887_; lean_object* v_currRecDepth_2888_; lean_object* v_ref_2889_; uint16_t v_optionFlags_2890_; uint8_t v_suppressElabErrors_2891_; uint8_t v_isRecordingDeps_2892_; lean_object* v_ref_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v_traceState_2896_; lean_object* v_traces_2897_; lean_object* v___x_2898_; size_t v_sz_2899_; size_t v___x_2900_; lean_object* v___x_2901_; lean_object* v_msg_2902_; lean_object* v___x_2903_; lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2942_; 
v_toCold_2887_ = lean_ctor_get(v___y_2884_, 0);
v_currRecDepth_2888_ = lean_ctor_get(v___y_2884_, 1);
v_ref_2889_ = lean_ctor_get(v___y_2884_, 2);
v_optionFlags_2890_ = lean_ctor_get_uint16(v___y_2884_, sizeof(void*)*3);
v_suppressElabErrors_2891_ = lean_ctor_get_uint8(v___y_2884_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2892_ = lean_ctor_get_uint8(v___y_2884_, sizeof(void*)*3 + 3);
v_ref_2893_ = l_Lean_replaceRef(v_ref_2882_, v_ref_2889_);
lean_inc(v_currRecDepth_2888_);
lean_inc_ref(v_toCold_2887_);
v___x_2894_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2894_, 0, v_toCold_2887_);
lean_ctor_set(v___x_2894_, 1, v_currRecDepth_2888_);
lean_ctor_set(v___x_2894_, 2, v_ref_2893_);
lean_ctor_set_uint16(v___x_2894_, sizeof(void*)*3, v_optionFlags_2890_);
lean_ctor_set_uint8(v___x_2894_, sizeof(void*)*3 + 2, v_suppressElabErrors_2891_);
lean_ctor_set_uint8(v___x_2894_, sizeof(void*)*3 + 3, v_isRecordingDeps_2892_);
v___x_2895_ = lean_st_ref_get(v___y_2885_);
v_traceState_2896_ = lean_ctor_get(v___x_2895_, 4);
lean_inc_ref(v_traceState_2896_);
lean_dec(v___x_2895_);
v_traces_2897_ = lean_ctor_get(v_traceState_2896_, 0);
lean_inc_ref(v_traces_2897_);
lean_dec_ref(v_traceState_2896_);
v___x_2898_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2897_);
lean_dec_ref(v_traces_2897_);
v_sz_2899_ = lean_array_size(v___x_2898_);
v___x_2900_ = ((size_t)0ULL);
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2899_, v___x_2900_, v___x_2898_);
v_msg_2902_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2902_, 0, v_data_2881_);
lean_ctor_set(v_msg_2902_, 1, v_msg_2883_);
lean_ctor_set(v_msg_2902_, 2, v___x_2901_);
v___x_2903_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2902_, v___x_2894_, v___y_2885_);
lean_dec_ref_known(v___x_2894_, 3);
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2942_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2942_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v_traceState_2909_; lean_object* v_env_2910_; lean_object* v_nextMacroScope_2911_; lean_object* v_ngen_2912_; lean_object* v_auxDeclNGen_2913_; lean_object* v_cache_2914_; lean_object* v_recordedDeps_2915_; lean_object* v_messages_2916_; lean_object* v_infoState_2917_; lean_object* v_snapshotTasks_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2941_; 
v___x_2908_ = lean_st_ref_take(v___y_2885_);
v_traceState_2909_ = lean_ctor_get(v___x_2908_, 4);
v_env_2910_ = lean_ctor_get(v___x_2908_, 0);
v_nextMacroScope_2911_ = lean_ctor_get(v___x_2908_, 1);
v_ngen_2912_ = lean_ctor_get(v___x_2908_, 2);
v_auxDeclNGen_2913_ = lean_ctor_get(v___x_2908_, 3);
v_cache_2914_ = lean_ctor_get(v___x_2908_, 5);
v_recordedDeps_2915_ = lean_ctor_get(v___x_2908_, 6);
v_messages_2916_ = lean_ctor_get(v___x_2908_, 7);
v_infoState_2917_ = lean_ctor_get(v___x_2908_, 8);
v_snapshotTasks_2918_ = lean_ctor_get(v___x_2908_, 9);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2920_ = v___x_2908_;
v_isShared_2921_ = v_isSharedCheck_2941_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_snapshotTasks_2918_);
lean_inc(v_infoState_2917_);
lean_inc(v_messages_2916_);
lean_inc(v_recordedDeps_2915_);
lean_inc(v_cache_2914_);
lean_inc(v_traceState_2909_);
lean_inc(v_auxDeclNGen_2913_);
lean_inc(v_ngen_2912_);
lean_inc(v_nextMacroScope_2911_);
lean_inc(v_env_2910_);
lean_dec(v___x_2908_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2941_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
uint64_t v_tid_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2939_; 
v_tid_2922_ = lean_ctor_get_uint64(v_traceState_2909_, sizeof(void*)*1);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_traceState_2909_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; 
v_unused_2940_ = lean_ctor_get(v_traceState_2909_, 0);
lean_dec(v_unused_2940_);
v___x_2924_ = v_traceState_2909_;
v_isShared_2925_ = v_isSharedCheck_2939_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v_traceState_2909_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2939_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v_ref_2882_);
lean_ctor_set(v___x_2927_, 1, v_a_2904_);
v___x_2928_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2880_, v___x_2927_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2928_);
v___x_2930_ = v___x_2924_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2928_);
lean_ctor_set_uint64(v_reuseFailAlloc_2938_, sizeof(void*)*1, v_tid_2922_);
v___x_2930_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2932_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 4, v___x_2930_);
v___x_2932_ = v___x_2920_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_env_2910_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_nextMacroScope_2911_);
lean_ctor_set(v_reuseFailAlloc_2937_, 2, v_ngen_2912_);
lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_auxDeclNGen_2913_);
lean_ctor_set(v_reuseFailAlloc_2937_, 4, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2937_, 5, v_cache_2914_);
lean_ctor_set(v_reuseFailAlloc_2937_, 6, v_recordedDeps_2915_);
lean_ctor_set(v_reuseFailAlloc_2937_, 7, v_messages_2916_);
lean_ctor_set(v_reuseFailAlloc_2937_, 8, v_infoState_2917_);
lean_ctor_set(v_reuseFailAlloc_2937_, 9, v_snapshotTasks_2918_);
v___x_2932_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = lean_st_ref_put(v___y_2885_, v___x_2932_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2926_);
v___x_2935_ = v___x_2906_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2926_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2943_, lean_object* v_data_2944_, lean_object* v_ref_2945_, lean_object* v_msg_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2943_, v_data_2944_, v_ref_2945_, v_msg_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2950_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
return v___x_2953_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2954_; double v___x_2955_; 
v___x_2954_ = lean_unsigned_to_nat(1000u);
v___x_2955_ = lean_float_of_nat(v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2956_, uint8_t v_collapsed_2957_, lean_object* v_tag_2958_, lean_object* v_opts_2959_, uint8_t v_clsEnabled_2960_, lean_object* v_oldTraces_2961_, lean_object* v_msg_2962_, lean_object* v_resStartStop_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_fst_2967_; lean_object* v_snd_2968_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v_data_2972_; lean_object* v_fst_2983_; lean_object* v_snd_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___y_2988_; lean_object* v_a_2989_; uint8_t v___y_3004_; double v___y_3036_; 
v_fst_2967_ = lean_ctor_get(v_resStartStop_2963_, 0);
lean_inc(v_fst_2967_);
v_snd_2968_ = lean_ctor_get(v_resStartStop_2963_, 1);
lean_inc(v_snd_2968_);
lean_dec_ref(v_resStartStop_2963_);
v_fst_2983_ = lean_ctor_get(v_snd_2968_, 0);
lean_inc(v_fst_2983_);
v_snd_2984_ = lean_ctor_get(v_snd_2968_, 1);
lean_inc(v_snd_2984_);
lean_dec(v_snd_2968_);
v___x_2985_ = l_Lean_trace_profiler;
v___x_2986_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2959_, v___x_2985_);
if (v___x_2986_ == 0)
{
v___y_3004_ = v___x_2986_;
goto v___jp_3003_;
}
else
{
lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3042_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2959_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; double v___x_3045_; double v___x_3046_; double v___x_3047_; 
v___x_3043_ = l_Lean_trace_profiler_threshold;
v___x_3044_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2959_, v___x_3043_);
v___x_3045_ = lean_float_of_nat(v___x_3044_);
v___x_3046_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3047_ = lean_float_div(v___x_3045_, v___x_3046_);
v___y_3036_ = v___x_3047_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; double v___x_3050_; 
v___x_3048_ = l_Lean_trace_profiler_threshold;
v___x_3049_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2959_, v___x_3048_);
v___x_3050_ = lean_float_of_nat(v___x_3049_);
v___y_3036_ = v___x_3050_;
goto v___jp_3035_;
}
}
v___jp_2969_:
{
lean_object* v___x_2973_; 
lean_inc(v___y_2971_);
v___x_2973_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2961_, v_data_2972_, v___y_2971_, v___y_2970_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v___x_2974_; 
lean_dec_ref_known(v___x_2973_, 1);
v___x_2974_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2967_);
return v___x_2974_;
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_fst_2967_);
v_a_2975_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2973_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2973_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
v___jp_2987_:
{
uint8_t v_result_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; double v___x_2993_; lean_object* v_data_2994_; 
v_result_2990_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2967_);
v___x_2991_ = lean_box(v_result_2990_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
v___x_2993_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_2958_);
lean_inc_ref(v___x_2992_);
lean_inc(v_cls_2956_);
v_data_2994_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2994_, 0, v_cls_2956_);
lean_ctor_set(v_data_2994_, 1, v___x_2992_);
lean_ctor_set(v_data_2994_, 2, v_tag_2958_);
lean_ctor_set_float(v_data_2994_, sizeof(void*)*3, v___x_2993_);
lean_ctor_set_float(v_data_2994_, sizeof(void*)*3 + 8, v___x_2993_);
lean_ctor_set_uint8(v_data_2994_, sizeof(void*)*3 + 16, v_collapsed_2957_);
if (v___x_2986_ == 0)
{
lean_dec_ref_known(v___x_2992_, 1);
lean_dec(v_snd_2984_);
lean_dec(v_fst_2983_);
lean_dec_ref(v_tag_2958_);
lean_dec(v_cls_2956_);
v___y_2970_ = v_a_2989_;
v___y_2971_ = v___y_2988_;
v_data_2972_ = v_data_2994_;
goto v___jp_2969_;
}
else
{
lean_object* v_data_2995_; double v___x_2996_; double v___x_2997_; 
lean_dec_ref_known(v_data_2994_, 3);
v_data_2995_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2995_, 0, v_cls_2956_);
lean_ctor_set(v_data_2995_, 1, v___x_2992_);
lean_ctor_set(v_data_2995_, 2, v_tag_2958_);
v___x_2996_ = lean_unbox_float(v_fst_2983_);
lean_dec(v_fst_2983_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3, v___x_2996_);
v___x_2997_ = lean_unbox_float(v_snd_2984_);
lean_dec(v_snd_2984_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3 + 8, v___x_2997_);
lean_ctor_set_uint8(v_data_2995_, sizeof(void*)*3 + 16, v_collapsed_2957_);
v___y_2970_ = v_a_2989_;
v___y_2971_ = v___y_2988_;
v_data_2972_ = v_data_2995_;
goto v___jp_2969_;
}
}
v___jp_2998_:
{
lean_object* v_ref_2999_; lean_object* v___x_3000_; 
v_ref_2999_ = lean_ctor_get(v___y_2964_, 2);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc(v_fst_2967_);
v___x_3000_ = lean_apply_4(v_msg_2962_, v_fst_2967_, v___y_2964_, v___y_2965_, lean_box(0));
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___y_2988_ = v_ref_2999_;
v_a_2989_ = v_a_3001_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3002_; 
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2988_ = v_ref_2999_;
v_a_2989_ = v___x_3002_;
goto v___jp_2987_;
}
}
v___jp_3003_:
{
if (v_clsEnabled_2960_ == 0)
{
if (v___y_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v_traceState_3006_; lean_object* v_env_3007_; lean_object* v_nextMacroScope_3008_; lean_object* v_ngen_3009_; lean_object* v_auxDeclNGen_3010_; lean_object* v_cache_3011_; lean_object* v_recordedDeps_3012_; lean_object* v_messages_3013_; lean_object* v_infoState_3014_; lean_object* v_snapshotTasks_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_snd_2984_);
lean_dec(v_fst_2983_);
lean_dec_ref(v_msg_2962_);
lean_dec_ref(v_tag_2958_);
lean_dec(v_cls_2956_);
v___x_3005_ = lean_st_ref_take(v___y_2965_);
v_traceState_3006_ = lean_ctor_get(v___x_3005_, 4);
v_env_3007_ = lean_ctor_get(v___x_3005_, 0);
v_nextMacroScope_3008_ = lean_ctor_get(v___x_3005_, 1);
v_ngen_3009_ = lean_ctor_get(v___x_3005_, 2);
v_auxDeclNGen_3010_ = lean_ctor_get(v___x_3005_, 3);
v_cache_3011_ = lean_ctor_get(v___x_3005_, 5);
v_recordedDeps_3012_ = lean_ctor_get(v___x_3005_, 6);
v_messages_3013_ = lean_ctor_get(v___x_3005_, 7);
v_infoState_3014_ = lean_ctor_get(v___x_3005_, 8);
v_snapshotTasks_3015_ = lean_ctor_get(v___x_3005_, 9);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3017_ = v___x_3005_;
v_isShared_3018_ = v_isSharedCheck_3034_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_snapshotTasks_3015_);
lean_inc(v_infoState_3014_);
lean_inc(v_messages_3013_);
lean_inc(v_recordedDeps_3012_);
lean_inc(v_cache_3011_);
lean_inc(v_traceState_3006_);
lean_inc(v_auxDeclNGen_3010_);
lean_inc(v_ngen_3009_);
lean_inc(v_nextMacroScope_3008_);
lean_inc(v_env_3007_);
lean_dec(v___x_3005_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3034_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
uint64_t v_tid_3019_; lean_object* v_traces_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3033_; 
v_tid_3019_ = lean_ctor_get_uint64(v_traceState_3006_, sizeof(void*)*1);
v_traces_3020_ = lean_ctor_get(v_traceState_3006_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_traceState_3006_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3022_ = v_traceState_3006_;
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_traces_3020_);
lean_dec(v_traceState_3006_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3024_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2961_, v_traces_3020_);
lean_dec_ref(v_traces_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3024_);
v___x_3026_ = v___x_3022_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3024_);
lean_ctor_set_uint64(v_reuseFailAlloc_3032_, sizeof(void*)*1, v_tid_3019_);
v___x_3026_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 4, v___x_3026_);
v___x_3028_ = v___x_3017_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_env_3007_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_nextMacroScope_3008_);
lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_ngen_3009_);
lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_auxDeclNGen_3010_);
lean_ctor_set(v_reuseFailAlloc_3031_, 4, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3031_, 5, v_cache_3011_);
lean_ctor_set(v_reuseFailAlloc_3031_, 6, v_recordedDeps_3012_);
lean_ctor_set(v_reuseFailAlloc_3031_, 7, v_messages_3013_);
lean_ctor_set(v_reuseFailAlloc_3031_, 8, v_infoState_3014_);
lean_ctor_set(v_reuseFailAlloc_3031_, 9, v_snapshotTasks_3015_);
v___x_3028_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_st_ref_put(v___y_2965_, v___x_3028_);
v___x_3030_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2967_);
return v___x_3030_;
}
}
}
}
}
else
{
goto v___jp_2998_;
}
}
else
{
goto v___jp_2998_;
}
}
v___jp_3035_:
{
double v___x_3037_; double v___x_3038_; double v___x_3039_; uint8_t v___x_3040_; 
v___x_3037_ = lean_unbox_float(v_snd_2984_);
v___x_3038_ = lean_unbox_float(v_fst_2983_);
v___x_3039_ = lean_float_sub(v___x_3037_, v___x_3038_);
v___x_3040_ = lean_float_decLt(v___y_3036_, v___x_3039_);
v___y_3004_ = v___x_3040_;
goto v___jp_3003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3051_, lean_object* v_collapsed_3052_, lean_object* v_tag_3053_, lean_object* v_opts_3054_, lean_object* v_clsEnabled_3055_, lean_object* v_oldTraces_3056_, lean_object* v_msg_3057_, lean_object* v_resStartStop_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
uint8_t v_collapsed_boxed_3062_; uint8_t v_clsEnabled_boxed_3063_; lean_object* v_res_3064_; 
v_collapsed_boxed_3062_ = lean_unbox(v_collapsed_3052_);
v_clsEnabled_boxed_3063_ = lean_unbox(v_clsEnabled_3055_);
v_res_3064_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3051_, v_collapsed_boxed_3062_, v_tag_3053_, v_opts_3054_, v_clsEnabled_boxed_3063_, v_oldTraces_3056_, v_msg_3057_, v_resStartStop_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_opts_3054_);
return v_res_3064_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
lean_ctor_set(v___x_3069_, 2, v___x_3068_);
lean_ctor_set(v___x_3069_, 3, v___x_3068_);
lean_ctor_set(v___x_3069_, 4, v___x_3067_);
lean_ctor_set(v___x_3069_, 5, v___x_3067_);
lean_ctor_set(v___x_3069_, 6, v___x_3067_);
lean_ctor_set(v___x_3069_, 7, v___x_3067_);
lean_ctor_set(v___x_3069_, 8, v___x_3067_);
lean_ctor_set(v___x_3069_, 9, v___x_3067_);
lean_ctor_set(v___x_3069_, 10, v___x_3067_);
return v___x_3069_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
lean_ctor_set(v___x_3071_, 3, v___x_3070_);
lean_ctor_set(v___x_3071_, 4, v___x_3070_);
lean_ctor_set(v___x_3071_, 5, v___x_3070_);
return v___x_3071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
lean_ctor_set(v___x_3073_, 2, v___x_3072_);
lean_ctor_set(v___x_3073_, 3, v___x_3072_);
lean_ctor_set(v___x_3073_, 4, v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3079_ = l_Lean_Name_append(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3080_; double v___x_3081_; 
v___x_3080_ = lean_unsigned_to_nat(1000000000u);
v___x_3081_ = lean_float_of_nat(v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3082_, lean_object* v___f_3083_, lean_object* v_name_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_toCold_3088_; lean_object* v_options_3089_; uint8_t v_hasTrace_3090_; 
v_toCold_3088_ = lean_ctor_get(v___y_3085_, 0);
v_options_3089_ = lean_ctor_get(v_toCold_3088_, 2);
v_hasTrace_3090_ = lean_ctor_get_uint8(v_options_3089_, sizeof(void*)*1);
if (v_hasTrace_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v_env_3092_; lean_object* v___x_3093_; 
lean_dec_ref(v___f_3083_);
v___x_3091_ = lean_st_ref_get(v___y_3086_);
v_env_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_ref(v_env_3092_);
lean_dec(v___x_3091_);
lean_inc(v_name_3084_);
v___x_3093_ = l_Lean_Meta_declFromEqLikeName(v_env_3092_, v_name_3084_);
if (lean_obj_tag(v___x_3093_) == 1)
{
lean_object* v_val_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3199_; 
v_val_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3199_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_val_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3199_;
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
v___x_3100_ = lean_st_ref_get(v___y_3086_);
v_env_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_ref(v_env_3101_);
lean_dec(v___x_3100_);
v___x_3102_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3101_, v_fst_3098_, v_snd_3099_);
v___x_3103_ = lean_name_eq(v_name_3084_, v___x_3102_);
lean_dec(v___x_3102_);
lean_dec(v_name_3084_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_dec(v_snd_3099_);
lean_dec(v_fst_3098_);
lean_dec(v___x_3082_);
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
lean_dec(v___x_3082_);
v___x_3139_ = lean_box(v_hasTrace_3090_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
else
{
uint8_t v___x_3141_; uint8_t v___x_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; uint64_t v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3141_ = 1;
v___x_3142_ = 0;
v___x_3143_ = 2;
v___x_3144_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3144_, 0, v___x_3108_);
lean_ctor_set_uint8(v___x_3144_, 1, v___x_3108_);
lean_ctor_set_uint8(v___x_3144_, 2, v___x_3108_);
lean_ctor_set_uint8(v___x_3144_, 3, v___x_3108_);
lean_ctor_set_uint8(v___x_3144_, 4, v___x_3108_);
lean_ctor_set_uint8(v___x_3144_, 5, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 6, v___x_3125_);
lean_ctor_set_uint8(v___x_3144_, 7, v___x_3108_);
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
lean_ctor_set_uint8(v___x_3144_, 19, v___x_3108_);
v___x_3145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3144_);
v___x_3146_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set_uint64(v___x_3146_, sizeof(void*)*1, v___x_3145_);
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3149_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3150_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3151_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3152_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3152_, 0, v___x_3146_);
lean_ctor_set(v___x_3152_, 1, v___x_3082_);
lean_ctor_set(v___x_3152_, 2, v___x_3149_);
lean_ctor_set(v___x_3152_, 3, v___x_3150_);
lean_ctor_set(v___x_3152_, 4, v___x_3151_);
lean_ctor_set(v___x_3152_, 5, v___x_3147_);
lean_ctor_set(v___x_3152_, 6, v___x_3151_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7, v___x_3108_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7 + 1, v___x_3108_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7 + 2, v___x_3108_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*7 + 3, v___x_3103_);
v___x_3153_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3154_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3155_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3153_);
lean_ctor_set(v___x_3156_, 1, v___x_3154_);
lean_ctor_set(v___x_3156_, 2, v___x_3082_);
lean_ctor_set(v___x_3156_, 3, v___x_3148_);
lean_ctor_set(v___x_3156_, 4, v___x_3155_);
v___x_3157_ = lean_st_mk_ref(v___x_3156_);
v___x_3158_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3098_, v___x_3103_, v___x_3152_, v___x_3157_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3152_, 7);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = lean_st_ref_get(v___x_3157_);
lean_dec(v___x_3157_);
lean_dec(v___x_3160_);
v_a_3127_ = v_a_3159_;
goto v___jp_3126_;
}
else
{
lean_dec(v___x_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3161_; 
v_a_3161_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3158_, 1);
v_a_3127_ = v_a_3161_;
goto v___jp_3126_;
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3158_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3158_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
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
v___x_3128_ = lean_box(v___x_3108_);
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
uint8_t v___x_3170_; uint8_t v___x_3171_; uint8_t v___x_3172_; lean_object* v___x_3173_; uint64_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v_snd_3099_);
v___x_3170_ = 1;
v___x_3171_ = 0;
v___x_3172_ = 2;
v___x_3173_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3173_, 0, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3173_, 1, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3173_, 2, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3173_, 3, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3173_, 4, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3173_, 5, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 6, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 7, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3173_, 8, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 9, v___x_3170_);
lean_ctor_set_uint8(v___x_3173_, 10, v___x_3171_);
lean_ctor_set_uint8(v___x_3173_, 11, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 12, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 13, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 14, v___x_3172_);
lean_ctor_set_uint8(v___x_3173_, 15, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 16, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 17, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 18, v___x_3108_);
lean_ctor_set_uint8(v___x_3173_, 19, v_hasTrace_3090_);
v___x_3174_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set_uint64(v___x_3175_, sizeof(void*)*1, v___x_3174_);
v___x_3176_ = lean_unsigned_to_nat(0u);
v___x_3177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3178_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3179_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3180_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3181_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3181_, 0, v___x_3175_);
lean_ctor_set(v___x_3181_, 1, v___x_3082_);
lean_ctor_set(v___x_3181_, 2, v___x_3178_);
lean_ctor_set(v___x_3181_, 3, v___x_3179_);
lean_ctor_set(v___x_3181_, 4, v___x_3180_);
lean_ctor_set(v___x_3181_, 5, v___x_3176_);
lean_ctor_set(v___x_3181_, 6, v___x_3180_);
lean_ctor_set_uint8(v___x_3181_, sizeof(void*)*7, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3181_, sizeof(void*)*7 + 1, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3181_, sizeof(void*)*7 + 2, v_hasTrace_3090_);
lean_ctor_set_uint8(v___x_3181_, sizeof(void*)*7 + 3, v___x_3103_);
v___x_3182_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3183_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3184_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3182_);
lean_ctor_set(v___x_3185_, 1, v___x_3183_);
lean_ctor_set(v___x_3185_, 2, v___x_3082_);
lean_ctor_set(v___x_3185_, 3, v___x_3177_);
lean_ctor_set(v___x_3185_, 4, v___x_3184_);
v___x_3186_ = lean_st_mk_ref(v___x_3185_);
v___x_3187_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3098_, v___x_3181_, v___x_3186_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3181_, 7);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3189_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v___x_3189_ = lean_st_ref_get(v___x_3186_);
lean_dec(v___x_3186_);
lean_dec(v___x_3189_);
v_a_3110_ = v_a_3188_;
goto v___jp_3109_;
}
else
{
lean_dec(v___x_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3190_; 
v_a_3190_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3187_, 1);
v_a_3110_ = v_a_3190_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_del_object(v___x_3096_);
v_a_3191_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3187_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3187_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
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
lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec(v___x_3093_);
lean_dec(v_name_3084_);
lean_dec(v___x_3082_);
v___x_3200_ = lean_box(v_hasTrace_3090_);
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
return v___x_3201_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3202_; lean_object* v___f_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v_a_3211_; lean_object* v___y_3224_; lean_object* v___y_3225_; uint8_t v_a_3226_; uint8_t v___y_3230_; lean_object* v___y_3231_; uint8_t v___y_3232_; lean_object* v___y_3233_; lean_object* v_a_3234_; uint8_t v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3238_; lean_object* v___y_3239_; lean_object* v_a_3240_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v_a_3244_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v_a_3249_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v_a_3261_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v_a_3266_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; uint8_t v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v_a_3280_; lean_object* v___y_3283_; uint8_t v___y_3284_; uint8_t v___y_3285_; lean_object* v___y_3286_; lean_object* v_a_3287_; 
v_inheritedTraceOptions_3202_ = lean_ctor_get(v_toCold_3088_, 11);
lean_inc(v_name_3084_);
v___f_3203_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3203_, 0, v_name_3084_);
v___x_3204_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3205_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3206_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3207_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3202_, v_options_3089_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3416_; uint8_t v___x_3417_; 
v___x_3416_ = l_Lean_trace_profiler;
v___x_3417_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3089_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; lean_object* v_env_3419_; lean_object* v___x_3420_; 
lean_dec_ref(v___f_3203_);
lean_dec_ref(v___f_3083_);
v___x_3418_ = lean_st_ref_get(v___y_3086_);
v_env_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc_ref(v_env_3419_);
lean_dec(v___x_3418_);
lean_inc(v_name_3084_);
v___x_3420_ = l_Lean_Meta_declFromEqLikeName(v_env_3419_, v_name_3084_);
if (lean_obj_tag(v___x_3420_) == 1)
{
lean_object* v_val_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3526_; 
v_val_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3526_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_val_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3526_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v_fst_3425_; lean_object* v_snd_3426_; lean_object* v___x_3427_; lean_object* v_env_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v_fst_3425_ = lean_ctor_get(v_val_3421_, 0);
lean_inc_n(v_fst_3425_, 2);
v_snd_3426_ = lean_ctor_get(v_val_3421_, 1);
lean_inc_n(v_snd_3426_, 2);
lean_dec(v_val_3421_);
v___x_3427_ = lean_st_ref_get(v___y_3086_);
v_env_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc_ref(v_env_3428_);
lean_dec(v___x_3427_);
v___x_3429_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3428_, v_fst_3425_, v_snd_3426_);
v___x_3430_ = lean_name_eq(v_name_3084_, v___x_3429_);
lean_dec(v___x_3429_);
lean_dec(v_name_3084_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_dec(v_snd_3426_);
lean_dec(v_fst_3425_);
lean_dec(v___x_3082_);
v___x_3431_ = lean_box(v___x_3417_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3431_);
v___x_3433_ = v___x_3423_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
else
{
uint8_t v___x_3435_; lean_object* v_a_3437_; 
lean_inc(v_snd_3426_);
v___x_3435_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3426_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3451_; uint8_t v___x_3452_; lean_object* v_a_3454_; 
lean_del_object(v___x_3423_);
v___x_3451_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3452_ = lean_string_dec_eq(v_snd_3426_, v___x_3451_);
lean_dec(v_snd_3426_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec(v_fst_3425_);
lean_dec(v___x_3082_);
v___x_3466_ = lean_box(v___x_3417_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
else
{
uint8_t v___x_3468_; uint8_t v___x_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; uint64_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3468_ = 1;
v___x_3469_ = 0;
v___x_3470_ = 2;
v___x_3471_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3471_, 0, v___x_3435_);
lean_ctor_set_uint8(v___x_3471_, 1, v___x_3435_);
lean_ctor_set_uint8(v___x_3471_, 2, v___x_3435_);
lean_ctor_set_uint8(v___x_3471_, 3, v___x_3435_);
lean_ctor_set_uint8(v___x_3471_, 4, v___x_3435_);
lean_ctor_set_uint8(v___x_3471_, 5, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 6, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 7, v___x_3435_);
lean_ctor_set_uint8(v___x_3471_, 8, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 9, v___x_3468_);
lean_ctor_set_uint8(v___x_3471_, 10, v___x_3469_);
lean_ctor_set_uint8(v___x_3471_, 11, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 12, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 13, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 14, v___x_3470_);
lean_ctor_set_uint8(v___x_3471_, 15, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 16, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 17, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 18, v___x_3452_);
lean_ctor_set_uint8(v___x_3471_, 19, v___x_3435_);
v___x_3472_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3471_);
v___x_3473_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set_uint64(v___x_3473_, sizeof(void*)*1, v___x_3472_);
v___x_3474_ = lean_unsigned_to_nat(0u);
v___x_3475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3476_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3477_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3478_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3479_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3479_, 0, v___x_3473_);
lean_ctor_set(v___x_3479_, 1, v___x_3082_);
lean_ctor_set(v___x_3479_, 2, v___x_3476_);
lean_ctor_set(v___x_3479_, 3, v___x_3477_);
lean_ctor_set(v___x_3479_, 4, v___x_3478_);
lean_ctor_set(v___x_3479_, 5, v___x_3474_);
lean_ctor_set(v___x_3479_, 6, v___x_3478_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*7, v___x_3435_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*7 + 1, v___x_3435_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*7 + 2, v___x_3435_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3480_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3481_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3482_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3480_);
lean_ctor_set(v___x_3483_, 1, v___x_3481_);
lean_ctor_set(v___x_3483_, 2, v___x_3082_);
lean_ctor_set(v___x_3483_, 3, v___x_3475_);
lean_ctor_set(v___x_3483_, 4, v___x_3482_);
v___x_3484_ = lean_st_mk_ref(v___x_3483_);
v___x_3485_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3425_, v_hasTrace_3090_, v___x_3479_, v___x_3484_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3479_, 7);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = lean_st_ref_get(v___x_3484_);
lean_dec(v___x_3484_);
lean_dec(v___x_3487_);
v_a_3454_ = v_a_3486_;
goto v___jp_3453_;
}
else
{
lean_dec(v___x_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3485_, 1);
v_a_3454_ = v_a_3488_;
goto v___jp_3453_;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
v_a_3489_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3485_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3485_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
v___jp_3453_:
{
if (lean_obj_tag(v_a_3454_) == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_box(v___x_3435_);
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
return v___x_3456_;
}
else
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3464_; 
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3454_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; 
v_unused_3465_ = lean_ctor_get(v_a_3454_, 0);
lean_dec(v_unused_3465_);
v___x_3458_ = v_a_3454_;
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v_a_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = lean_box(v___x_3452_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3460_);
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
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
else
{
uint8_t v___x_3497_; uint8_t v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; uint64_t v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_dec(v_snd_3426_);
v___x_3497_ = 1;
v___x_3498_ = 0;
v___x_3499_ = 2;
v___x_3500_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3500_, 0, v___x_3417_);
lean_ctor_set_uint8(v___x_3500_, 1, v___x_3417_);
lean_ctor_set_uint8(v___x_3500_, 2, v___x_3417_);
lean_ctor_set_uint8(v___x_3500_, 3, v___x_3417_);
lean_ctor_set_uint8(v___x_3500_, 4, v___x_3417_);
lean_ctor_set_uint8(v___x_3500_, 5, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 6, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 7, v___x_3417_);
lean_ctor_set_uint8(v___x_3500_, 8, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 9, v___x_3497_);
lean_ctor_set_uint8(v___x_3500_, 10, v___x_3498_);
lean_ctor_set_uint8(v___x_3500_, 11, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 12, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 13, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 14, v___x_3499_);
lean_ctor_set_uint8(v___x_3500_, 15, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 16, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 17, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 18, v___x_3435_);
lean_ctor_set_uint8(v___x_3500_, 19, v___x_3417_);
v___x_3501_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set_uint64(v___x_3502_, sizeof(void*)*1, v___x_3501_);
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3505_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3506_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3507_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3508_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3508_, 0, v___x_3502_);
lean_ctor_set(v___x_3508_, 1, v___x_3082_);
lean_ctor_set(v___x_3508_, 2, v___x_3505_);
lean_ctor_set(v___x_3508_, 3, v___x_3506_);
lean_ctor_set(v___x_3508_, 4, v___x_3507_);
lean_ctor_set(v___x_3508_, 5, v___x_3503_);
lean_ctor_set(v___x_3508_, 6, v___x_3507_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*7, v___x_3417_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*7 + 1, v___x_3417_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*7 + 2, v___x_3417_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3509_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3510_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3511_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3509_);
lean_ctor_set(v___x_3512_, 1, v___x_3510_);
lean_ctor_set(v___x_3512_, 2, v___x_3082_);
lean_ctor_set(v___x_3512_, 3, v___x_3504_);
lean_ctor_set(v___x_3512_, 4, v___x_3511_);
v___x_3513_ = lean_st_mk_ref(v___x_3512_);
v___x_3514_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3425_, v___x_3508_, v___x_3513_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3508_, 7);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = lean_st_ref_get(v___x_3513_);
lean_dec(v___x_3513_);
lean_dec(v___x_3516_);
v_a_3437_ = v_a_3515_;
goto v___jp_3436_;
}
else
{
lean_dec(v___x_3513_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3517_; 
v_a_3517_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3514_, 1);
v_a_3437_ = v_a_3517_;
goto v___jp_3436_;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_del_object(v___x_3423_);
v_a_3518_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3514_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3514_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
v___jp_3436_:
{
if (lean_obj_tag(v_a_3437_) == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3438_ = lean_box(v___x_3417_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3438_);
v___x_3440_ = v___x_3423_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
else
{
lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3449_; 
lean_del_object(v___x_3423_);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_a_3437_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; 
v_unused_3450_ = lean_ctor_get(v_a_3437_, 0);
lean_dec(v_unused_3450_);
v___x_3443_ = v_a_3437_;
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
else
{
lean_dec(v_a_3437_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = lean_box(v___x_3435_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set_tag(v___x_3443_, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3445_);
v___x_3447_ = v___x_3443_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec(v___x_3420_);
lean_dec(v_name_3084_);
lean_dec(v___x_3082_);
v___x_3527_ = lean_box(v___x_3417_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
}
else
{
goto v___jp_3288_;
}
}
else
{
goto v___jp_3288_;
}
v___jp_3208_:
{
lean_object* v___x_3212_; double v___x_3213_; double v___x_3214_; double v___x_3215_; double v___x_3216_; double v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3212_ = lean_io_mono_nanos_now();
v___x_3213_ = lean_float_of_nat(v___y_3209_);
v___x_3214_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3215_ = lean_float_div(v___x_3213_, v___x_3214_);
v___x_3216_ = lean_float_of_nat(v___x_3212_);
v___x_3217_ = lean_float_div(v___x_3216_, v___x_3214_);
v___x_3218_ = lean_box_float(v___x_3215_);
v___x_3219_ = lean_box_float(v___x_3217_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_a_3211_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3204_, v_hasTrace_3090_, v___x_3205_, v_options_3089_, v___x_3207_, v___y_3210_, v___f_3203_, v___x_3221_, v___y_3085_, v___y_3086_);
return v___x_3222_;
}
v___jp_3223_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = lean_box(v_a_3226_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
v___y_3209_ = v___y_3224_;
v___y_3210_ = v___y_3225_;
v_a_3211_ = v___x_3228_;
goto v___jp_3208_;
}
v___jp_3229_:
{
if (lean_obj_tag(v_a_3234_) == 0)
{
v___y_3224_ = v___y_3231_;
v___y_3225_ = v___y_3233_;
v_a_3226_ = v___y_3230_;
goto v___jp_3223_;
}
else
{
lean_dec_ref_known(v_a_3234_, 1);
v___y_3224_ = v___y_3231_;
v___y_3225_ = v___y_3233_;
v_a_3226_ = v___y_3232_;
goto v___jp_3223_;
}
}
v___jp_3235_:
{
if (lean_obj_tag(v_a_3240_) == 0)
{
v___y_3224_ = v___y_3237_;
v___y_3225_ = v___y_3239_;
v_a_3226_ = v___y_3238_;
goto v___jp_3223_;
}
else
{
lean_dec_ref_known(v_a_3240_, 1);
v___y_3224_ = v___y_3237_;
v___y_3225_ = v___y_3239_;
v_a_3226_ = v___y_3236_;
goto v___jp_3223_;
}
}
v___jp_3241_:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_a_3244_);
v___y_3209_ = v___y_3242_;
v___y_3210_ = v___y_3243_;
v_a_3211_ = v___x_3245_;
goto v___jp_3208_;
}
v___jp_3246_:
{
lean_object* v___x_3250_; double v___x_3251_; double v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3250_ = lean_io_get_num_heartbeats();
v___x_3251_ = lean_float_of_nat(v___y_3247_);
v___x_3252_ = lean_float_of_nat(v___x_3250_);
v___x_3253_ = lean_box_float(v___x_3251_);
v___x_3254_ = lean_box_float(v___x_3252_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v_a_3249_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3204_, v_hasTrace_3090_, v___x_3205_, v_options_3089_, v___x_3207_, v___y_3248_, v___f_3203_, v___x_3256_, v___y_3085_, v___y_3086_);
return v___x_3257_;
}
v___jp_3258_:
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_a_3261_);
v___y_3247_ = v___y_3259_;
v___y_3248_ = v___y_3260_;
v_a_3249_ = v___x_3262_;
goto v___jp_3246_;
}
v___jp_3263_:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = lean_box(v_a_3266_);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
v___y_3247_ = v___y_3264_;
v___y_3248_ = v___y_3265_;
v_a_3249_ = v___x_3268_;
goto v___jp_3246_;
}
v___jp_3269_:
{
if (lean_obj_tag(v___y_3272_) == 0)
{
lean_object* v_a_3273_; uint8_t v___x_3274_; 
v_a_3273_ = lean_ctor_get(v___y_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___y_3272_, 1);
v___x_3274_ = lean_unbox(v_a_3273_);
lean_dec(v_a_3273_);
v___y_3264_ = v___y_3270_;
v___y_3265_ = v___y_3271_;
v_a_3266_ = v___x_3274_;
goto v___jp_3263_;
}
else
{
lean_object* v_a_3275_; 
v_a_3275_ = lean_ctor_get(v___y_3272_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___y_3272_, 1);
v___y_3259_ = v___y_3270_;
v___y_3260_ = v___y_3271_;
v_a_3261_ = v_a_3275_;
goto v___jp_3258_;
}
}
v___jp_3276_:
{
if (lean_obj_tag(v_a_3280_) == 0)
{
uint8_t v___x_3281_; 
v___x_3281_ = 0;
v___y_3264_ = v___y_3278_;
v___y_3265_ = v___y_3279_;
v_a_3266_ = v___x_3281_;
goto v___jp_3263_;
}
else
{
lean_dec_ref_known(v_a_3280_, 1);
v___y_3264_ = v___y_3278_;
v___y_3265_ = v___y_3279_;
v_a_3266_ = v___y_3277_;
goto v___jp_3263_;
}
}
v___jp_3282_:
{
if (lean_obj_tag(v_a_3287_) == 0)
{
v___y_3264_ = v___y_3283_;
v___y_3265_ = v___y_3286_;
v_a_3266_ = v___y_3284_;
goto v___jp_3263_;
}
else
{
lean_dec_ref_known(v_a_3287_, 1);
v___y_3264_ = v___y_3283_;
v___y_3265_ = v___y_3286_;
v_a_3266_ = v___y_3285_;
goto v___jp_3263_;
}
}
v___jp_3288_:
{
lean_object* v___x_3289_; lean_object* v_a_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3289_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3086_);
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref(v___x_3289_);
v___x_3291_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3292_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3089_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_env_3295_; lean_object* v___x_3296_; 
lean_dec_ref(v___f_3083_);
v___x_3293_ = lean_io_mono_nanos_now();
v___x_3294_ = lean_st_ref_get(v___y_3086_);
v_env_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc_ref(v_env_3295_);
lean_dec(v___x_3294_);
lean_inc(v_name_3084_);
v___x_3296_ = l_Lean_Meta_declFromEqLikeName(v_env_3295_, v_name_3084_);
if (lean_obj_tag(v___x_3296_) == 1)
{
lean_object* v_val_3297_; lean_object* v_fst_3298_; lean_object* v_snd_3299_; lean_object* v___x_3300_; lean_object* v_env_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v_val_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_val_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v_fst_3298_ = lean_ctor_get(v_val_3297_, 0);
lean_inc_n(v_fst_3298_, 2);
v_snd_3299_ = lean_ctor_get(v_val_3297_, 1);
lean_inc_n(v_snd_3299_, 2);
lean_dec(v_val_3297_);
v___x_3300_ = lean_st_ref_get(v___y_3086_);
v_env_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_env_3301_);
lean_dec(v___x_3300_);
v___x_3302_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3301_, v_fst_3298_, v_snd_3299_);
v___x_3303_ = lean_name_eq(v_name_3084_, v___x_3302_);
lean_dec(v___x_3302_);
lean_dec(v_name_3084_);
if (v___x_3303_ == 0)
{
lean_dec(v_snd_3299_);
lean_dec(v_fst_3298_);
lean_dec(v___x_3082_);
v___y_3224_ = v___x_3293_;
v___y_3225_ = v_a_3290_;
v_a_3226_ = v___x_3292_;
goto v___jp_3223_;
}
else
{
uint8_t v___x_3304_; 
lean_inc(v_snd_3299_);
v___x_3304_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3299_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; uint8_t v___x_3306_; 
v___x_3305_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3306_ = lean_string_dec_eq(v_snd_3299_, v___x_3305_);
lean_dec(v_snd_3299_);
if (v___x_3306_ == 0)
{
lean_dec(v_fst_3298_);
lean_dec(v___x_3082_);
v___y_3224_ = v___x_3293_;
v___y_3225_ = v_a_3290_;
v_a_3226_ = v___x_3292_;
goto v___jp_3223_;
}
else
{
uint8_t v___x_3307_; uint8_t v___x_3308_; uint8_t v___x_3309_; lean_object* v___x_3310_; uint64_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3307_ = 1;
v___x_3308_ = 0;
v___x_3309_ = 2;
v___x_3310_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3310_, 0, v___x_3304_);
lean_ctor_set_uint8(v___x_3310_, 1, v___x_3304_);
lean_ctor_set_uint8(v___x_3310_, 2, v___x_3304_);
lean_ctor_set_uint8(v___x_3310_, 3, v___x_3304_);
lean_ctor_set_uint8(v___x_3310_, 4, v___x_3304_);
lean_ctor_set_uint8(v___x_3310_, 5, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 6, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 7, v___x_3304_);
lean_ctor_set_uint8(v___x_3310_, 8, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 9, v___x_3307_);
lean_ctor_set_uint8(v___x_3310_, 10, v___x_3308_);
lean_ctor_set_uint8(v___x_3310_, 11, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 12, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 13, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 14, v___x_3309_);
lean_ctor_set_uint8(v___x_3310_, 15, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 16, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 17, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 18, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, 19, v___x_3304_);
v___x_3311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set_uint64(v___x_3312_, sizeof(void*)*1, v___x_3311_);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3317_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3318_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3318_, 0, v___x_3312_);
lean_ctor_set(v___x_3318_, 1, v___x_3082_);
lean_ctor_set(v___x_3318_, 2, v___x_3315_);
lean_ctor_set(v___x_3318_, 3, v___x_3316_);
lean_ctor_set(v___x_3318_, 4, v___x_3317_);
lean_ctor_set(v___x_3318_, 5, v___x_3313_);
lean_ctor_set(v___x_3318_, 6, v___x_3317_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7, v___x_3304_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7 + 1, v___x_3304_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7 + 2, v___x_3304_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3319_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3320_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3319_);
lean_ctor_set(v___x_3322_, 1, v___x_3320_);
lean_ctor_set(v___x_3322_, 2, v___x_3082_);
lean_ctor_set(v___x_3322_, 3, v___x_3314_);
lean_ctor_set(v___x_3322_, 4, v___x_3321_);
v___x_3323_ = lean_st_mk_ref(v___x_3322_);
v___x_3324_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3298_, v_hasTrace_3090_, v___x_3318_, v___x_3323_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3318_, 7);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v___x_3326_ = lean_st_ref_get(v___x_3323_);
lean_dec(v___x_3323_);
lean_dec(v___x_3326_);
v___y_3230_ = v___x_3304_;
v___y_3231_ = v___x_3293_;
v___y_3232_ = v___x_3306_;
v___y_3233_ = v_a_3290_;
v_a_3234_ = v_a_3325_;
goto v___jp_3229_;
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
v___y_3230_ = v___x_3304_;
v___y_3231_ = v___x_3293_;
v___y_3232_ = v___x_3306_;
v___y_3233_ = v_a_3290_;
v_a_3234_ = v_a_3327_;
goto v___jp_3229_;
}
else
{
lean_object* v_a_3328_; 
v_a_3328_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3324_, 1);
v___y_3242_ = v___x_3293_;
v___y_3243_ = v_a_3290_;
v_a_3244_ = v_a_3328_;
goto v___jp_3241_;
}
}
}
}
else
{
uint8_t v___x_3329_; uint8_t v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; uint64_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec(v_snd_3299_);
v___x_3329_ = 1;
v___x_3330_ = 0;
v___x_3331_ = 2;
v___x_3332_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3332_, 0, v___x_3292_);
lean_ctor_set_uint8(v___x_3332_, 1, v___x_3292_);
lean_ctor_set_uint8(v___x_3332_, 2, v___x_3292_);
lean_ctor_set_uint8(v___x_3332_, 3, v___x_3292_);
lean_ctor_set_uint8(v___x_3332_, 4, v___x_3292_);
lean_ctor_set_uint8(v___x_3332_, 5, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 6, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 7, v___x_3292_);
lean_ctor_set_uint8(v___x_3332_, 8, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 9, v___x_3329_);
lean_ctor_set_uint8(v___x_3332_, 10, v___x_3330_);
lean_ctor_set_uint8(v___x_3332_, 11, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 12, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 13, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 14, v___x_3331_);
lean_ctor_set_uint8(v___x_3332_, 15, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 16, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 17, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 18, v___x_3304_);
lean_ctor_set_uint8(v___x_3332_, 19, v___x_3292_);
v___x_3333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3332_);
v___x_3334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set_uint64(v___x_3334_, sizeof(void*)*1, v___x_3333_);
v___x_3335_ = lean_unsigned_to_nat(0u);
v___x_3336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3337_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3339_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3340_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3340_, 0, v___x_3334_);
lean_ctor_set(v___x_3340_, 1, v___x_3082_);
lean_ctor_set(v___x_3340_, 2, v___x_3337_);
lean_ctor_set(v___x_3340_, 3, v___x_3338_);
lean_ctor_set(v___x_3340_, 4, v___x_3339_);
lean_ctor_set(v___x_3340_, 5, v___x_3335_);
lean_ctor_set(v___x_3340_, 6, v___x_3339_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7, v___x_3292_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7 + 1, v___x_3292_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7 + 2, v___x_3292_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7 + 3, v_hasTrace_3090_);
v___x_3341_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3342_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3343_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3341_);
lean_ctor_set(v___x_3344_, 1, v___x_3342_);
lean_ctor_set(v___x_3344_, 2, v___x_3082_);
lean_ctor_set(v___x_3344_, 3, v___x_3336_);
lean_ctor_set(v___x_3344_, 4, v___x_3343_);
v___x_3345_ = lean_st_mk_ref(v___x_3344_);
v___x_3346_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3298_, v___x_3340_, v___x_3345_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3340_, 7);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = lean_st_ref_get(v___x_3345_);
lean_dec(v___x_3345_);
lean_dec(v___x_3348_);
v___y_3236_ = v___x_3304_;
v___y_3237_ = v___x_3293_;
v___y_3238_ = v___x_3292_;
v___y_3239_ = v_a_3290_;
v_a_3240_ = v_a_3347_;
goto v___jp_3235_;
}
else
{
lean_dec(v___x_3345_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3349_; 
v_a_3349_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3346_, 1);
v___y_3236_ = v___x_3304_;
v___y_3237_ = v___x_3293_;
v___y_3238_ = v___x_3292_;
v___y_3239_ = v_a_3290_;
v_a_3240_ = v_a_3349_;
goto v___jp_3235_;
}
else
{
lean_object* v_a_3350_; 
v_a_3350_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3346_, 1);
v___y_3242_ = v___x_3293_;
v___y_3243_ = v_a_3290_;
v_a_3244_ = v_a_3350_;
goto v___jp_3241_;
}
}
}
}
}
else
{
lean_dec(v___x_3296_);
lean_dec(v_name_3084_);
lean_dec(v___x_3082_);
v___y_3224_ = v___x_3293_;
v___y_3225_ = v_a_3290_;
v_a_3226_ = v___x_3292_;
goto v___jp_3223_;
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v_env_3353_; lean_object* v___x_3354_; 
v___x_3351_ = lean_io_get_num_heartbeats();
v___x_3352_ = lean_st_ref_get(v___y_3086_);
v_env_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_ref(v_env_3353_);
lean_dec(v___x_3352_);
lean_inc(v_name_3084_);
v___x_3354_ = l_Lean_Meta_declFromEqLikeName(v_env_3353_, v_name_3084_);
if (lean_obj_tag(v___x_3354_) == 1)
{
lean_object* v_val_3355_; lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3358_; lean_object* v_env_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_val_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_val_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v_fst_3356_ = lean_ctor_get(v_val_3355_, 0);
lean_inc_n(v_fst_3356_, 2);
v_snd_3357_ = lean_ctor_get(v_val_3355_, 1);
lean_inc_n(v_snd_3357_, 2);
lean_dec(v_val_3355_);
v___x_3358_ = lean_st_ref_get(v___y_3086_);
v_env_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_ref(v_env_3359_);
lean_dec(v___x_3358_);
v___x_3360_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3359_, v_fst_3356_, v_snd_3357_);
v___x_3361_ = lean_name_eq(v_name_3084_, v___x_3360_);
lean_dec(v___x_3360_);
lean_dec(v_name_3084_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec(v_snd_3357_);
lean_dec(v_fst_3356_);
lean_dec(v___x_3082_);
v___x_3362_ = lean_box(0);
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
v___x_3363_ = lean_apply_4(v___f_3083_, v___x_3362_, v___y_3085_, v___y_3086_, lean_box(0));
v___y_3270_ = v___x_3351_;
v___y_3271_ = v_a_3290_;
v___y_3272_ = v___x_3363_;
goto v___jp_3269_;
}
else
{
uint8_t v___x_3364_; 
lean_inc(v_snd_3357_);
v___x_3364_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3357_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3365_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3366_ = lean_string_dec_eq(v_snd_3357_, v___x_3365_);
lean_dec(v_snd_3357_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec(v_fst_3356_);
lean_dec(v___x_3082_);
v___x_3367_ = lean_box(0);
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
v___x_3368_ = lean_apply_4(v___f_3083_, v___x_3367_, v___y_3085_, v___y_3086_, lean_box(0));
v___y_3270_ = v___x_3351_;
v___y_3271_ = v_a_3290_;
v___y_3272_ = v___x_3368_;
goto v___jp_3269_;
}
else
{
uint8_t v___x_3369_; uint8_t v___x_3370_; uint8_t v___x_3371_; lean_object* v___x_3372_; uint64_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec_ref(v___f_3083_);
v___x_3369_ = 1;
v___x_3370_ = 0;
v___x_3371_ = 2;
v___x_3372_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3372_, 0, v___x_3364_);
lean_ctor_set_uint8(v___x_3372_, 1, v___x_3364_);
lean_ctor_set_uint8(v___x_3372_, 2, v___x_3364_);
lean_ctor_set_uint8(v___x_3372_, 3, v___x_3364_);
lean_ctor_set_uint8(v___x_3372_, 4, v___x_3364_);
lean_ctor_set_uint8(v___x_3372_, 5, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 6, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 7, v___x_3364_);
lean_ctor_set_uint8(v___x_3372_, 8, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 9, v___x_3369_);
lean_ctor_set_uint8(v___x_3372_, 10, v___x_3370_);
lean_ctor_set_uint8(v___x_3372_, 11, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 12, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 13, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 14, v___x_3371_);
lean_ctor_set_uint8(v___x_3372_, 15, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 16, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 17, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 18, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, 19, v___x_3364_);
v___x_3373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3372_);
v___x_3374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set_uint64(v___x_3374_, sizeof(void*)*1, v___x_3373_);
v___x_3375_ = lean_unsigned_to_nat(0u);
v___x_3376_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3377_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3378_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3379_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3380_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3380_, 0, v___x_3374_);
lean_ctor_set(v___x_3380_, 1, v___x_3082_);
lean_ctor_set(v___x_3380_, 2, v___x_3377_);
lean_ctor_set(v___x_3380_, 3, v___x_3378_);
lean_ctor_set(v___x_3380_, 4, v___x_3379_);
lean_ctor_set(v___x_3380_, 5, v___x_3375_);
lean_ctor_set(v___x_3380_, 6, v___x_3379_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*7, v___x_3364_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*7 + 1, v___x_3364_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*7 + 2, v___x_3364_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*7 + 3, v___x_3292_);
v___x_3381_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3382_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3383_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3381_);
lean_ctor_set(v___x_3384_, 1, v___x_3382_);
lean_ctor_set(v___x_3384_, 2, v___x_3082_);
lean_ctor_set(v___x_3384_, 3, v___x_3376_);
lean_ctor_set(v___x_3384_, 4, v___x_3383_);
v___x_3385_ = lean_st_mk_ref(v___x_3384_);
v___x_3386_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3356_, v___x_3292_, v___x_3380_, v___x_3385_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3380_, 7);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = lean_st_ref_get(v___x_3385_);
lean_dec(v___x_3385_);
lean_dec(v___x_3388_);
v___y_3283_ = v___x_3351_;
v___y_3284_ = v___x_3364_;
v___y_3285_ = v___x_3366_;
v___y_3286_ = v_a_3290_;
v_a_3287_ = v_a_3387_;
goto v___jp_3282_;
}
else
{
lean_dec(v___x_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3389_; 
v_a_3389_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3386_, 1);
v___y_3283_ = v___x_3351_;
v___y_3284_ = v___x_3364_;
v___y_3285_ = v___x_3366_;
v___y_3286_ = v_a_3290_;
v_a_3287_ = v_a_3389_;
goto v___jp_3282_;
}
else
{
lean_object* v_a_3390_; 
v_a_3390_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3386_, 1);
v___y_3259_ = v___x_3351_;
v___y_3260_ = v_a_3290_;
v_a_3261_ = v_a_3390_;
goto v___jp_3258_;
}
}
}
}
else
{
uint8_t v___x_3391_; uint8_t v___x_3392_; uint8_t v___x_3393_; uint8_t v___x_3394_; lean_object* v___x_3395_; uint64_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_dec(v_snd_3357_);
lean_dec_ref(v___f_3083_);
v___x_3391_ = 0;
v___x_3392_ = 1;
v___x_3393_ = 0;
v___x_3394_ = 2;
v___x_3395_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3395_, 0, v___x_3391_);
lean_ctor_set_uint8(v___x_3395_, 1, v___x_3391_);
lean_ctor_set_uint8(v___x_3395_, 2, v___x_3391_);
lean_ctor_set_uint8(v___x_3395_, 3, v___x_3391_);
lean_ctor_set_uint8(v___x_3395_, 4, v___x_3391_);
lean_ctor_set_uint8(v___x_3395_, 5, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 6, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 7, v___x_3391_);
lean_ctor_set_uint8(v___x_3395_, 8, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 9, v___x_3392_);
lean_ctor_set_uint8(v___x_3395_, 10, v___x_3393_);
lean_ctor_set_uint8(v___x_3395_, 11, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 12, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 13, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 14, v___x_3394_);
lean_ctor_set_uint8(v___x_3395_, 15, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 16, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 17, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 18, v___x_3364_);
lean_ctor_set_uint8(v___x_3395_, 19, v___x_3391_);
v___x_3396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3395_);
v___x_3397_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set_uint64(v___x_3397_, sizeof(void*)*1, v___x_3396_);
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3400_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3401_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3402_ = lean_box(0);
lean_inc(v___x_3082_);
v___x_3403_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3403_, 0, v___x_3397_);
lean_ctor_set(v___x_3403_, 1, v___x_3082_);
lean_ctor_set(v___x_3403_, 2, v___x_3400_);
lean_ctor_set(v___x_3403_, 3, v___x_3401_);
lean_ctor_set(v___x_3403_, 4, v___x_3402_);
lean_ctor_set(v___x_3403_, 5, v___x_3398_);
lean_ctor_set(v___x_3403_, 6, v___x_3402_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7, v___x_3391_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7 + 1, v___x_3391_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7 + 2, v___x_3391_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7 + 3, v___x_3292_);
v___x_3404_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3405_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3404_);
lean_ctor_set(v___x_3407_, 1, v___x_3405_);
lean_ctor_set(v___x_3407_, 2, v___x_3082_);
lean_ctor_set(v___x_3407_, 3, v___x_3399_);
lean_ctor_set(v___x_3407_, 4, v___x_3406_);
v___x_3408_ = lean_st_mk_ref(v___x_3407_);
v___x_3409_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3356_, v___x_3403_, v___x_3408_, v___y_3085_, v___y_3086_);
lean_dec_ref_known(v___x_3403_, 7);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v___x_3411_ = lean_st_ref_get(v___x_3408_);
lean_dec(v___x_3408_);
lean_dec(v___x_3411_);
v___y_3277_ = v___x_3364_;
v___y_3278_ = v___x_3351_;
v___y_3279_ = v_a_3290_;
v_a_3280_ = v_a_3410_;
goto v___jp_3276_;
}
else
{
lean_dec(v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3412_; 
v_a_3412_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3277_ = v___x_3364_;
v___y_3278_ = v___x_3351_;
v___y_3279_ = v_a_3290_;
v_a_3280_ = v_a_3412_;
goto v___jp_3276_;
}
else
{
lean_object* v_a_3413_; 
v_a_3413_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3259_ = v___x_3351_;
v___y_3260_ = v_a_3290_;
v_a_3261_ = v_a_3413_;
goto v___jp_3258_;
}
}
}
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v___x_3354_);
lean_dec(v_name_3084_);
lean_dec(v___x_3082_);
v___x_3414_ = lean_box(0);
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
v___x_3415_ = lean_apply_4(v___f_3083_, v___x_3414_, v___y_3085_, v___y_3086_, lean_box(0));
v___y_3270_ = v___x_3351_;
v___y_3271_ = v_a_3290_;
v___y_3272_ = v___x_3415_;
goto v___jp_3269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3529_, lean_object* v___f_3530_, lean_object* v_name_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3529_, v___f_3530_, v_name_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
return v_res_3535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = lean_unsigned_to_nat(3137104340u);
v___x_3581_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3582_ = l_Lean_Name_num___override(v___x_3581_, v___x_3580_);
return v___x_3582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3584_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3585_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3586_ = l_Lean_Name_str___override(v___x_3585_, v___x_3584_);
return v___x_3586_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3589_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3590_ = l_Lean_Name_str___override(v___x_3589_, v___x_3588_);
return v___x_3590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = lean_unsigned_to_nat(2u);
v___x_3592_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3593_ = l_Lean_Name_num___override(v___x_3592_, v___x_3591_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3595_; lean_object* v___x_3596_; 
v___f_3595_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3596_ = l_Lean_registerReservedNameAction(v___f_3595_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec_ref_known(v___x_3596_, 1);
v___x_3597_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3598_ = 0;
v___x_3599_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3600_ = l_Lean_registerTraceClass(v___x_3597_, v___x_3598_, v___x_3599_);
return v___x_3600_;
}
else
{
return v___x_3596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3603_, lean_object* v_x_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3604_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3609_, v_x_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3614_;
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
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
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
