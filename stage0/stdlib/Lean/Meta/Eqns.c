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
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
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
static uint8_t l_Lean_Meta_withEqnOptions___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_withEqnOptions___redArg___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_saveEqnAffectingOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__0 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__0_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_saveEqnAffectingOptions___closed__1;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__2;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__3;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__4;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__5;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__6 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__6_value;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__7 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__7_value;
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__6_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__7_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 70, 141, 178, 157, 107, 140, 91)}};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__8 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__8_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__9;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "saving equation-affecting options for "};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__10 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__10_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
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
lean_object* v___x_112_; lean_object* v_fst_113_; uint8_t v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_112_ = lean_array_uget_borrowed(v_as_102_, v_i_103_);
v_fst_113_ = lean_ctor_get(v___x_112_, 0);
v___x_114_ = 1;
lean_inc_ref(v_env_101_);
v___x_115_ = l_Lean_Environment_setExporting(v_env_101_, v___x_114_);
lean_inc(v_fst_113_);
v___x_116_ = l_Lean_Environment_contains(v___x_115_, v_fst_113_, v___x_111_);
if (v___x_116_ == 0)
{
v___y_107_ = v_b_105_;
goto v___jp_106_;
}
else
{
lean_object* v___x_117_; 
lean_inc(v___x_112_);
v___x_117_ = lean_array_push(v_b_105_, v___x_112_);
v___y_107_ = v___x_117_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_118_, lean_object* v_as_119_, lean_object* v_i_120_, lean_object* v_stop_121_, lean_object* v_b_122_){
_start:
{
size_t v_i_boxed_123_; size_t v_stop_boxed_124_; lean_object* v_res_125_; 
v_i_boxed_123_ = lean_unbox_usize(v_i_120_);
lean_dec(v_i_120_);
v_stop_boxed_124_ = lean_unbox_usize(v_stop_121_);
lean_dec(v_stop_121_);
v_res_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_118_, v_as_119_, v_i_boxed_123_, v_stop_boxed_124_, v_b_122_);
lean_dec_ref(v_as_119_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v_k_128_; lean_object* v_v_129_; lean_object* v_l_130_; lean_object* v_r_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_k_128_ = lean_ctor_get(v_x_127_, 1);
v_v_129_ = lean_ctor_get(v_x_127_, 2);
v_l_130_ = lean_ctor_get(v_x_127_, 3);
v_r_131_ = lean_ctor_get(v_x_127_, 4);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_126_, v_l_130_);
lean_inc(v_v_129_);
lean_inc(v_k_128_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_k_128_);
lean_ctor_set(v___x_133_, 1, v_v_129_);
v___x_134_ = lean_array_push(v___x_132_, v___x_133_);
v_init_126_ = v___x_134_;
v_x_127_ = v_r_131_;
goto _start;
}
else
{
return v_init_126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_136_, v_x_137_);
lean_dec(v_x_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(lean_object* v_env_139_, lean_object* v_as_140_, size_t v_i_141_, size_t v_stop_142_, lean_object* v_b_143_){
_start:
{
lean_object* v___y_145_; uint8_t v___x_149_; 
v___x_149_ = lean_usize_dec_eq(v_i_141_, v_stop_142_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v_fst_151_; uint8_t v___x_152_; 
v___x_150_ = lean_array_uget_borrowed(v_as_140_, v_i_141_);
v_fst_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_fst_151_);
lean_inc_ref(v_env_139_);
v___x_152_ = l_Lean_Environment_contains(v_env_139_, v_fst_151_, v___x_149_);
if (v___x_152_ == 0)
{
v___y_145_ = v_b_143_;
goto v___jp_144_;
}
else
{
lean_object* v___x_153_; 
lean_inc(v___x_150_);
v___x_153_ = lean_array_push(v_b_143_, v___x_150_);
v___y_145_ = v___x_153_;
goto v___jp_144_;
}
}
else
{
lean_dec_ref(v_env_139_);
return v_b_143_;
}
v___jp_144_:
{
size_t v___x_146_; size_t v___x_147_; 
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_add(v_i_141_, v___x_146_);
v_i_141_ = v___x_147_;
v_b_143_ = v___y_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_154_, lean_object* v_as_155_, lean_object* v_i_156_, lean_object* v_stop_157_, lean_object* v_b_158_){
_start:
{
size_t v_i_boxed_159_; size_t v_stop_boxed_160_; lean_object* v_res_161_; 
v_i_boxed_159_ = lean_unbox_usize(v_i_156_);
lean_dec(v_i_156_);
v_stop_boxed_160_ = lean_unbox_usize(v_stop_157_);
lean_dec(v_stop_157_);
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_154_, v_as_155_, v_i_boxed_159_, v_stop_boxed_160_, v_b_158_);
lean_dec_ref(v_as_155_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(lean_object* v_env_166_, lean_object* v_s_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___y_170_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_179_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_180_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v___x_179_, v_s_167_);
v___x_181_ = lean_array_get_size(v___x_180_);
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_183_ = lean_nat_dec_lt(v___x_168_, v___x_181_);
if (v___x_183_ == 0)
{
lean_dec_ref(v___x_180_);
v___y_170_ = v___x_182_;
goto v___jp_169_;
}
else
{
size_t v___x_184_; size_t v___x_185_; lean_object* v___x_186_; 
v___x_184_ = ((size_t)0ULL);
v___x_185_ = lean_usize_of_nat(v___x_181_);
lean_inc_ref(v_env_166_);
v___x_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_166_, v___x_180_, v___x_184_, v___x_185_, v___x_182_);
lean_dec_ref(v___x_180_);
v___y_170_ = v___x_186_;
goto v___jp_169_;
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_171_ = lean_array_get_size(v___y_170_);
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_173_ = lean_nat_dec_lt(v___x_168_, v___x_171_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_dec_ref(v_env_166_);
v___x_174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___y_170_);
return v___x_174_;
}
else
{
size_t v___x_175_; size_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = ((size_t)0ULL);
v___x_176_ = lean_usize_of_nat(v___x_171_);
v___x_177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_166_, v___y_170_, v___x_175_, v___x_176_, v___x_172_);
lean_inc_ref(v___x_177_);
v___x_178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
lean_ctor_set(v___x_178_, 2, v___y_170_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_env_187_, lean_object* v_s_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(v_env_187_, v_s_188_);
lean_dec(v_s_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; 
v___f_197_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_199_ = lean_box(1);
v___x_200_ = 0;
v___x_201_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_198_, v___x_199_, v___x_200_, v___f_197_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object* v_init_204_, lean_object* v_t_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_204_, v_t_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_207_, lean_object* v_t_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_207_, v_t_208_);
lean_dec(v_t_208_);
return v_res_209_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_string_utf8_byte_size(v_s_216_);
v___x_218_ = lean_unsigned_to_nat(3u);
v___x_219_ = lean_nat_dec_le(v___x_218_, v___x_217_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_s_216_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_220_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_string_memcmp(v_s_216_, v___x_220_, v___x_221_, v___x_221_, v___x_218_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_s_216_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
lean_inc_ref(v_s_216_);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v_s_216_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set(v___x_223_, 2, v___x_217_);
v___x_224_ = l_String_Slice_Pos_nextn(v___x_223_, v___x_221_, v___x_218_);
lean_dec_ref_known(v___x_223_, 3);
v___x_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_225_, 0, v_s_216_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
lean_ctor_set(v___x_225_, 2, v___x_217_);
v___x_226_ = l_String_Slice_isNat(v___x_225_);
lean_dec_ref_known(v___x_225_, 3);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_236_ = lean_string_dec_eq(v_s_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_238_ = lean_string_dec_eq(v_s_234_, v___x_237_);
if (v___x_238_ == 0)
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_234_);
return v___x_239_;
}
else
{
lean_dec_ref(v_s_234_);
return v___x_238_;
}
}
else
{
lean_dec_ref(v_s_234_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lean_Meta_isEqnLikeSuffix(v_s_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_env_246_, lean_object* v_str_247_, lean_object* v_as_x27_248_, lean_object* v_b_249_){
_start:
{
if (lean_obj_tag(v_as_x27_248_) == 0)
{
lean_dec_ref(v_str_247_);
lean_dec_ref(v_env_246_);
lean_inc_ref(v_b_249_);
return v_b_249_;
}
else
{
lean_object* v_head_250_; lean_object* v_tail_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_head_250_ = lean_ctor_get(v_as_x27_248_, 0);
v_tail_251_ = lean_ctor_get(v_as_x27_248_, 1);
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_254_ = 0;
lean_inc_ref(v_env_246_);
v___x_255_ = l_Lean_Environment_setExporting(v_env_246_, v___x_254_);
lean_inc(v_head_250_);
v___x_256_ = l_Lean_Environment_isSafeDefinition(v___x_255_, v_head_250_);
if (v___x_256_ == 0)
{
v_as_x27_248_ = v_tail_251_;
v_b_249_ = v___x_253_;
goto _start;
}
else
{
uint8_t v___x_258_; 
lean_inc(v_head_250_);
lean_inc_ref(v_env_246_);
v___x_258_ = l_Lean_Meta_isMatcherCore(v_env_246_, v_head_250_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref(v_env_246_);
lean_inc(v_head_250_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_head_250_);
lean_ctor_set(v___x_259_, 1, v_str_247_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_252_);
return v___x_262_;
}
else
{
v_as_x27_248_ = v_tail_251_;
v_b_249_ = v___x_253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_env_264_, lean_object* v_str_265_, lean_object* v_as_x27_266_, lean_object* v_b_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_env_264_, v_str_265_, v_as_x27_266_, v_b_267_);
lean_dec_ref(v_b_267_);
lean_dec(v_as_x27_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_269_, lean_object* v_name_270_){
_start:
{
if (lean_obj_tag(v_name_270_) == 1)
{
lean_object* v_pre_271_; lean_object* v_str_272_; uint8_t v___x_273_; 
v_pre_271_ = lean_ctor_get(v_name_270_, 0);
lean_inc(v_pre_271_);
v_str_272_ = lean_ctor_get(v_name_270_, 1);
lean_inc_ref_n(v_str_272_, 2);
lean_dec_ref_known(v_name_270_, 2);
v___x_273_ = l_Lean_Meta_isEqnLikeSuffix(v_str_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec_ref(v_str_272_);
lean_dec(v_pre_271_);
lean_dec_ref(v_env_269_);
v___x_274_ = lean_box(0);
return v___x_274_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_fst_282_; 
lean_inc(v_pre_271_);
v___x_275_ = l_Lean_privateToUserName(v_pre_271_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v_pre_271_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_box(0);
v___x_280_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_281_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_env_269_, v_str_272_, v___x_278_, v___x_280_);
lean_dec_ref_known(v___x_278_, 2);
v_fst_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_fst_282_);
lean_dec_ref(v___x_281_);
if (lean_obj_tag(v_fst_282_) == 0)
{
return v___x_279_;
}
else
{
lean_object* v_val_283_; 
v_val_283_ = lean_ctor_get(v_fst_282_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v_fst_282_, 1);
return v_val_283_;
}
}
}
else
{
lean_object* v___x_284_; 
lean_dec(v_name_270_);
lean_dec_ref(v_env_269_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_env_285_, lean_object* v_str_286_, lean_object* v_as_287_, lean_object* v_as_x27_288_, lean_object* v_b_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_env_285_, v_str_286_, v_as_x27_288_, v_b_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_env_292_, lean_object* v_str_293_, lean_object* v_as_294_, lean_object* v_as_x27_295_, lean_object* v_b_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_env_292_, v_str_293_, v_as_294_, v_as_x27_295_, v_b_296_, v_a_297_);
lean_dec_ref(v_b_296_);
lean_dec(v_as_x27_295_);
lean_dec(v_as_294_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_299_, lean_object* v_declName_300_, lean_object* v_suffix_301_){
_start:
{
uint8_t v_isExposed_302_; lean_object* v_name_303_; 
lean_inc(v_declName_300_);
lean_inc_ref(v_env_299_);
v_isExposed_302_ = l_Lean_Environment_hasExposedBody(v_env_299_, v_declName_300_);
v_name_303_ = l_Lean_Name_str___override(v_declName_300_, v_suffix_301_);
if (v_isExposed_302_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_mkPrivateName(v_env_299_, v_name_303_);
lean_dec_ref(v_env_299_);
return v___x_304_;
}
else
{
lean_dec_ref(v_env_299_);
return v_name_303_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_305_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
lean_ctor_set(v___x_310_, 2, v___x_309_);
lean_ctor_set(v___x_310_, 3, v___x_309_);
lean_ctor_set(v___x_310_, 4, v___x_308_);
lean_ctor_set(v___x_310_, 5, v___x_308_);
lean_ctor_set(v___x_310_, 6, v___x_308_);
lean_ctor_set(v___x_310_, 7, v___x_308_);
lean_ctor_set(v___x_310_, 8, v___x_308_);
lean_ctor_set(v___x_310_, 9, v___x_308_);
lean_ctor_set(v___x_310_, 10, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(32u);
v___x_312_ = lean_mk_empty_array_with_capacity(v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_314_ = ((size_t)5ULL);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_unsigned_to_nat(32u);
v___x_317_ = lean_mk_empty_array_with_capacity(v___x_316_);
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_319_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_315_);
lean_ctor_set(v___x_319_, 3, v___x_315_);
lean_ctor_set_usize(v___x_319_, 4, v___x_314_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = lean_box(1);
v___x_321_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_322_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_320_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; lean_object* v_toCold_329_; lean_object* v_env_330_; lean_object* v_options_331_; uint8_t v___x_332_; lean_object* v_env_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_328_ = lean_st_ref_get(v___y_326_);
v_toCold_329_ = lean_ctor_get(v___y_325_, 0);
v_env_330_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_328_);
v_options_331_ = lean_ctor_get(v_toCold_329_, 2);
v___x_332_ = 0;
v_env_333_ = l_Lean_Environment_setRecordingDeps(v_env_330_, v___x_332_);
v___x_334_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_331_);
v___x_336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_336_, 0, v_env_333_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
lean_ctor_set(v___x_336_, 3, v_options_331_);
v___x_337_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_msgData_324_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_ref_348_; lean_object* v___x_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_ref_348_ = lean_ctor_get(v___y_345_, 2);
v___x_349_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_344_, v___y_345_, v___y_346_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
lean_inc(v_ref_348_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_ref_348_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_373_, lean_object* v_reservedName_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_378_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_379_ = 0;
v___x_380_ = l_Lean_MessageData_ofConstName(v_declName_373_, v___x_379_);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_378_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = 1;
v___x_385_ = l_Lean_MessageData_ofConstName(v_reservedName_374_, v___x_384_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_383_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_388_, v___y_375_, v___y_376_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_390_, lean_object* v_reservedName_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_390_, v_reservedName_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_396_, lean_object* v_suffix_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_reservedName_401_; lean_object* v___x_402_; lean_object* v_env_403_; uint8_t v___x_404_; uint8_t v___x_405_; 
lean_inc(v_declName_396_);
v_reservedName_401_ = l_Lean_Name_str___override(v_declName_396_, v_suffix_397_);
v___x_402_ = lean_st_ref_get(v___y_399_);
v_env_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_402_);
v___x_404_ = 1;
lean_inc(v_reservedName_401_);
v___x_405_ = l_Lean_Environment_contains(v_env_403_, v_reservedName_401_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_reservedName_401_);
lean_dec(v_declName_396_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_396_, v_reservedName_401_, v___y_398_, v___y_399_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_409_, lean_object* v_suffix_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_409_, v_suffix_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_415_);
v___x_420_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_415_, v___x_419_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref_known(v___x_420_, 1);
v___x_421_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_415_);
v___x_422_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_415_, v___x_421_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref_known(v___x_422_, 1);
v___x_423_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_424_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_415_, v___x_423_, v_a_416_, v_a_417_);
return v___x_424_;
}
else
{
lean_dec(v_declName_415_);
return v___x_422_;
}
}
else
{
lean_dec(v_declName_415_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_431_, v___y_432_, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_436_, lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_436_, v_msg_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_441_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_442_, lean_object* v_n_443_){
_start:
{
lean_object* v___x_444_; 
lean_inc(v_n_443_);
lean_inc_ref(v_env_442_);
v___x_444_ = l_Lean_Meta_declFromEqLikeName(v_env_442_, v_n_443_);
if (lean_obj_tag(v___x_444_) == 1)
{
lean_object* v_val_445_; lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_val_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v___x_444_, 1);
v_fst_446_ = lean_ctor_get(v_val_445_, 0);
lean_inc(v_fst_446_);
v_snd_447_ = lean_ctor_get(v_val_445_, 1);
lean_inc(v_snd_447_);
lean_dec(v_val_445_);
v___x_448_ = l_Lean_Meta_mkEqLikeNameFor(v_env_442_, v_fst_446_, v_snd_447_);
v___x_449_ = lean_name_eq(v_n_443_, v___x_448_);
lean_dec(v___x_448_);
lean_dec(v_n_443_);
return v___x_449_;
}
else
{
uint8_t v___x_450_; 
lean_dec(v___x_444_);
lean_dec(v_n_443_);
lean_dec_ref(v_env_442_);
v___x_450_ = 0;
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_451_, lean_object* v_n_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_451_, v_n_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_457_; lean_object* v___x_458_; 
v___f_457_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_458_ = l_Lean_registerReservedNamePredicate(v___f_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_box(0);
v___x_463_ = lean_st_mk_ref(v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_466_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_469_ = lean_mk_io_user_error(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_470_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = l_Lean_initializing();
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref(v_f_470_);
v___x_473_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_475_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_476_ = lean_st_ref_take(v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_f_470_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_st_ref_put(v___x_475_, v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_registerGetEqnsFn(v_f_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_493_; lean_object* v_env_494_; uint8_t v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_st_ref_get(v_a_487_);
v_env_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_env_494_);
lean_dec(v___x_493_);
v___x_495_ = 0;
lean_inc(v_declName_483_);
v___x_496_ = l_Lean_Environment_findAsync_x3f(v_env_494_, v_declName_483_, v___x_495_);
if (lean_obj_tag(v___x_496_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_528_; 
v_val_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_528_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_528_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_val_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_528_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v_kind_501_; 
v_kind_501_ = lean_ctor_get_uint8(v_val_497_, sizeof(void*)*3);
if (v_kind_501_ == 0)
{
lean_object* v_sig_502_; lean_object* v___x_503_; lean_object* v_env_504_; uint8_t v___x_505_; 
v_sig_502_ = lean_ctor_get(v_val_497_, 1);
lean_inc_ref(v_sig_502_);
lean_dec(v_val_497_);
v___x_503_ = lean_st_ref_get(v_a_487_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_env_504_);
lean_dec(v___x_503_);
v___x_505_ = l_Lean_Meta_isMatcherCore(v_env_504_, v_declName_483_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v_type_507_; lean_object* v___x_508_; 
lean_del_object(v___x_499_);
v___x_506_ = lean_task_get_own(v_sig_502_);
v_type_507_ = lean_ctor_get(v___x_506_, 2);
lean_inc_ref(v_type_507_);
lean_dec(v___x_506_);
v___x_508_ = l_Lean_Meta_isProp(v_type_507_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_523_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_523_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_523_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_523_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint8_t v___x_513_; 
v___x_513_ = lean_unbox(v_a_509_);
lean_dec(v_a_509_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = 1;
v___x_515_ = lean_box(v___x_514_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_515_);
v___x_517_ = v___x_511_;
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
else
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_box(v___x_505_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_519_);
v___x_521_ = v___x_511_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
return v___x_508_;
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec_ref(v_sig_502_);
v___x_524_ = lean_box(v___x_495_);
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 0);
lean_ctor_set(v___x_499_, 0, v___x_524_);
v___x_526_ = v___x_499_;
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
else
{
lean_del_object(v___x_499_);
lean_dec(v_val_497_);
lean_dec(v_declName_483_);
goto v___jp_489_;
}
}
}
else
{
lean_dec(v___x_496_);
lean_dec(v_declName_483_);
goto v___jp_489_;
}
v___jp_489_:
{
uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = 0;
v___x_491_ = lean_box(v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
return v_res_535_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object* v___x_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v___x_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_543_);
return v_res_545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_546_; lean_object* v___f_547_; 
v___x_546_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_547_, 0, v___x_546_);
return v___f_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
v___f_554_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_box(1);
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_));
v___x_558_ = 0;
v___x_559_ = 1;
v___x_560_ = l_Lean_registerEnvExtension___redArg(v___f_554_, v___x_555_, v___x_556_, v___x_557_, v___x_558_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_563_, lean_object* v_opt_564_){
_start:
{
lean_object* v_name_565_; lean_object* v_defValue_566_; lean_object* v_map_567_; lean_object* v___x_568_; 
v_name_565_ = lean_ctor_get(v_opt_564_, 0);
v_defValue_566_ = lean_ctor_get(v_opt_564_, 1);
v_map_567_ = lean_ctor_get(v_opts_563_, 0);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_567_, v_name_565_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_inc(v_defValue_566_);
return v_defValue_566_;
}
else
{
lean_object* v_val_569_; 
v_val_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_569_);
lean_dec_ref_known(v___x_568_, 1);
if (lean_obj_tag(v_val_569_) == 3)
{
lean_object* v_v_570_; 
v_v_570_ = lean_ctor_get(v_val_569_, 0);
lean_inc(v_v_570_);
lean_dec_ref_known(v_val_569_, 1);
return v_v_570_;
}
else
{
lean_dec(v_val_569_);
lean_inc(v_defValue_566_);
return v_defValue_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_571_, lean_object* v_opt_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_571_, v_opt_572_);
lean_dec_ref(v_opt_572_);
lean_dec_ref(v_opts_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_577_, size_t v_sz_578_, size_t v_i_579_, lean_object* v_b_580_){
_start:
{
lean_object* v_a_582_; uint8_t v___x_586_; 
v___x_586_ = lean_usize_dec_lt(v_i_579_, v_sz_578_);
if (v___x_586_ == 0)
{
return v_b_580_;
}
else
{
lean_object* v_a_587_; lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v_map_590_; uint8_t v_hasTrace_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_604_; 
v_a_587_ = lean_array_uget_borrowed(v_as_577_, v_i_579_);
v_fst_588_ = lean_ctor_get(v_a_587_, 0);
v_snd_589_ = lean_ctor_get(v_a_587_, 1);
v_map_590_ = lean_ctor_get(v_b_580_, 0);
v_hasTrace_591_ = lean_ctor_get_uint8(v_b_580_, sizeof(void*)*1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_b_580_);
if (v_isSharedCheck_604_ == 0)
{
v___x_593_ = v_b_580_;
v_isShared_594_ = v_isSharedCheck_604_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_map_590_);
lean_dec(v_b_580_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_604_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; 
lean_inc(v_snd_589_);
lean_inc(v_fst_588_);
v___x_595_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_588_, v_snd_589_, v_map_590_);
if (v_hasTrace_591_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_599_; 
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_597_ = l_Lean_Name_isPrefixOf(v___x_596_, v_fst_588_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_599_ = v___x_593_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_595_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*1, v___x_597_);
v_a_582_ = v___x_599_;
goto v___jp_581_;
}
}
else
{
lean_object* v___x_602_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_595_);
lean_ctor_set_uint8(v_reuseFailAlloc_603_, sizeof(void*)*1, v_hasTrace_591_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
v_a_582_ = v___x_602_;
goto v___jp_581_;
}
}
}
}
v___jp_581_:
{
size_t v___x_583_; size_t v___x_584_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_579_, v___x_583_);
v_i_579_ = v___x_584_;
v_b_580_ = v_a_582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_605_, lean_object* v_sz_606_, lean_object* v_i_607_, lean_object* v_b_608_){
_start:
{
size_t v_sz_boxed_609_; size_t v_i_boxed_610_; lean_object* v_res_611_; 
v_sz_boxed_609_ = lean_unbox_usize(v_sz_606_);
lean_dec(v_sz_606_);
v_i_boxed_610_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_605_, v_sz_boxed_609_, v_i_boxed_610_, v_b_608_);
lean_dec_ref(v_as_605_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_612_, lean_object* v_k_613_, uint8_t v_v_614_){
_start:
{
lean_object* v_map_615_; uint8_t v_hasTrace_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_630_; 
v_map_615_ = lean_ctor_get(v_o_612_, 0);
v_hasTrace_616_ = lean_ctor_get_uint8(v_o_612_, sizeof(void*)*1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_o_612_);
if (v_isSharedCheck_630_ == 0)
{
v___x_618_ = v_o_612_;
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_map_615_);
lean_dec(v_o_612_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_620_, 0, v_v_614_);
lean_inc(v_k_613_);
v___x_621_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_613_, v___x_620_, v_map_615_);
if (v_hasTrace_616_ == 0)
{
lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_625_; 
v___x_622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_623_ = l_Lean_Name_isPrefixOf(v___x_622_, v_k_613_);
lean_dec(v_k_613_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_621_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_621_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*1, v___x_623_);
return v___x_625_;
}
}
else
{
lean_object* v___x_628_; 
lean_dec(v_k_613_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_621_);
v___x_628_ = v___x_618_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_621_);
lean_ctor_set_uint8(v_reuseFailAlloc_629_, sizeof(void*)*1, v_hasTrace_616_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_631_, lean_object* v_k_632_, lean_object* v_v_633_){
_start:
{
uint8_t v_v_boxed_634_; lean_object* v_res_635_; 
v_v_boxed_634_ = lean_unbox(v_v_633_);
v_res_635_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_631_, v_k_632_, v_v_boxed_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_636_, lean_object* v_opt_637_, uint8_t v_val_638_){
_start:
{
lean_object* v_name_639_; lean_object* v___x_640_; 
v_name_639_ = lean_ctor_get(v_opt_637_, 0);
lean_inc(v_name_639_);
lean_dec_ref(v_opt_637_);
v___x_640_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_636_, v_name_639_, v_val_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_641_, lean_object* v_opt_642_, lean_object* v_val_643_){
_start:
{
uint8_t v_val_boxed_644_; lean_object* v_res_645_; 
v_val_boxed_644_ = lean_unbox(v_val_643_);
v_res_645_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_641_, v_opt_642_, v_val_boxed_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_646_, size_t v_i_647_, size_t v_stop_648_, lean_object* v_b_649_){
_start:
{
uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_eq(v_i_647_, v_stop_648_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v_defValue_652_; uint8_t v___x_653_; lean_object* v___x_654_; size_t v___x_655_; size_t v___x_656_; 
v___x_651_ = lean_array_uget_borrowed(v_as_646_, v_i_647_);
v_defValue_652_ = lean_ctor_get(v___x_651_, 1);
v___x_653_ = lean_unbox(v_defValue_652_);
lean_inc(v___x_651_);
v___x_654_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_649_, v___x_651_, v___x_653_);
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_add(v_i_647_, v___x_655_);
v_i_647_ = v___x_656_;
v_b_649_ = v___x_654_;
goto _start;
}
else
{
return v_b_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_658_, lean_object* v_i_659_, lean_object* v_stop_660_, lean_object* v_b_661_){
_start:
{
size_t v_i_boxed_662_; size_t v_stop_boxed_663_; lean_object* v_res_664_; 
v_i_boxed_662_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_stop_boxed_663_ = lean_unbox_usize(v_stop_660_);
lean_dec(v_stop_660_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_658_, v_i_boxed_662_, v_stop_boxed_663_, v_b_661_);
lean_dec_ref(v_as_658_);
return v_res_664_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = l_Lean_Meta_eqnAffectingOptions;
v___x_670_ = lean_array_get_size(v___x_669_);
return v___x_670_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_nat_dec_lt(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_674_; size_t v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_675_ = lean_usize_of_nat(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_676_, lean_object* v_act_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
uint16_t v___y_684_; lean_object* v___y_685_; lean_object* v_fileName_686_; lean_object* v_fileMap_687_; lean_object* v_currNamespace_688_; lean_object* v_openDecls_689_; lean_object* v_initHeartbeats_690_; lean_object* v_maxHeartbeats_691_; lean_object* v_quotContext_692_; lean_object* v_currMacroScope_693_; lean_object* v_cancelTk_x3f_694_; lean_object* v_inheritedTraceOptions_695_; lean_object* v_currRecDepth_696_; lean_object* v_ref_697_; uint8_t v_suppressElabErrors_698_; uint8_t v_checkDeprecated_699_; uint8_t v_isRecordingDeps_700_; lean_object* v___y_701_; lean_object* v___y_708_; uint16_t v___y_709_; uint8_t v___y_710_; lean_object* v___x_748_; lean_object* v_toCold_749_; lean_object* v_currRecDepth_750_; lean_object* v_ref_751_; uint8_t v_suppressElabErrors_752_; uint8_t v_checkDeprecated_753_; uint8_t v_isRecordingDeps_754_; lean_object* v_fileName_755_; lean_object* v_fileMap_756_; lean_object* v_options_757_; lean_object* v_currNamespace_758_; lean_object* v_openDecls_759_; lean_object* v_initHeartbeats_760_; lean_object* v_maxHeartbeats_761_; lean_object* v_quotContext_762_; lean_object* v_currMacroScope_763_; lean_object* v_cancelTk_x3f_764_; lean_object* v_inheritedTraceOptions_765_; lean_object* v___y_767_; 
v___x_748_ = lean_st_ref_get(v_a_681_);
v_toCold_749_ = lean_ctor_get(v_a_680_, 0);
v_currRecDepth_750_ = lean_ctor_get(v_a_680_, 1);
v_ref_751_ = lean_ctor_get(v_a_680_, 2);
v_suppressElabErrors_752_ = lean_ctor_get_uint8(v_a_680_, sizeof(void*)*3 + 2);
v_checkDeprecated_753_ = lean_ctor_get_uint8(v_a_680_, sizeof(void*)*3 + 3);
v_isRecordingDeps_754_ = lean_ctor_get_uint8(v_a_680_, sizeof(void*)*3 + 4);
v_fileName_755_ = lean_ctor_get(v_toCold_749_, 0);
v_fileMap_756_ = lean_ctor_get(v_toCold_749_, 1);
v_options_757_ = lean_ctor_get(v_toCold_749_, 2);
v_currNamespace_758_ = lean_ctor_get(v_toCold_749_, 4);
v_openDecls_759_ = lean_ctor_get(v_toCold_749_, 5);
v_initHeartbeats_760_ = lean_ctor_get(v_toCold_749_, 6);
v_maxHeartbeats_761_ = lean_ctor_get(v_toCold_749_, 7);
v_quotContext_762_ = lean_ctor_get(v_toCold_749_, 8);
v_currMacroScope_763_ = lean_ctor_get(v_toCold_749_, 9);
v_cancelTk_x3f_764_ = lean_ctor_get(v_toCold_749_, 10);
v_inheritedTraceOptions_765_ = lean_ctor_get(v_toCold_749_, 11);
if (v_isRecordingDeps_754_ == 0)
{
lean_object* v_env_778_; lean_object* v___x_779_; lean_object* v_toEnvExtension_780_; lean_object* v_asyncMode_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v_env_778_ = lean_ctor_get(v___x_748_, 0);
lean_inc_ref(v_env_778_);
lean_dec(v___x_748_);
v___x_779_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_780_ = lean_ctor_get(v___x_779_, 0);
v_asyncMode_781_ = lean_ctor_get(v_toEnvExtension_780_, 2);
v___x_782_ = 0;
v___x_783_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_779_, v_env_778_, v_declName_676_, v_asyncMode_781_, v___x_782_);
if (lean_obj_tag(v___x_783_) == 1)
{
lean_object* v_val_784_; lean_object* v___y_786_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_val_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_790_ = l_Lean_Meta_eqnAffectingOptions;
v___x_791_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
if (v___x_791_ == 0)
{
lean_inc_ref(v_options_757_);
v___y_786_ = v_options_757_;
goto v___jp_785_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
lean_inc_ref(v_options_757_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_790_, v___x_792_, v___x_793_, v_options_757_);
v___y_786_ = v___x_794_;
goto v___jp_785_;
}
v___jp_785_:
{
size_t v_sz_787_; size_t v___x_788_; lean_object* v___x_789_; 
v_sz_787_ = lean_array_size(v_val_784_);
v___x_788_ = ((size_t)0ULL);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_784_, v_sz_787_, v___x_788_, v___y_786_);
lean_dec(v_val_784_);
v___y_767_ = v___x_789_;
goto v___jp_766_;
}
}
else
{
lean_object* v___x_795_; uint8_t v___x_796_; 
lean_dec(v___x_783_);
v___x_795_ = l_Lean_Meta_eqnAffectingOptions;
v___x_796_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
if (v___x_796_ == 0)
{
lean_inc_ref(v_options_757_);
v___y_767_ = v_options_757_;
goto v___jp_766_;
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
v___x_797_ = ((size_t)0ULL);
v___x_798_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
lean_inc_ref(v_options_757_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_795_, v___x_797_, v___x_798_, v_options_757_);
v___y_767_ = v___x_799_;
goto v___jp_766_;
}
}
}
else
{
lean_object* v___x_800_; 
lean_dec(v___x_748_);
lean_dec(v_declName_676_);
lean_inc_ref(v_options_757_);
v___x_800_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_757_);
v___y_767_ = v___x_800_;
goto v___jp_766_;
}
v___jp_683_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_702_ = l_Lean_maxRecDepth;
v___x_703_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_685_, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_704_, 0, v_fileName_686_);
lean_ctor_set(v___x_704_, 1, v_fileMap_687_);
lean_ctor_set(v___x_704_, 2, v___y_685_);
lean_ctor_set(v___x_704_, 3, v___x_703_);
lean_ctor_set(v___x_704_, 4, v_currNamespace_688_);
lean_ctor_set(v___x_704_, 5, v_openDecls_689_);
lean_ctor_set(v___x_704_, 6, v_initHeartbeats_690_);
lean_ctor_set(v___x_704_, 7, v_maxHeartbeats_691_);
lean_ctor_set(v___x_704_, 8, v_quotContext_692_);
lean_ctor_set(v___x_704_, 9, v_currMacroScope_693_);
lean_ctor_set(v___x_704_, 10, v_cancelTk_x3f_694_);
lean_ctor_set(v___x_704_, 11, v_inheritedTraceOptions_695_);
lean_inc(v_ref_697_);
lean_inc(v_currRecDepth_696_);
v___x_705_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_currRecDepth_696_);
lean_ctor_set(v___x_705_, 2, v_ref_697_);
lean_ctor_set_uint16(v___x_705_, sizeof(void*)*3, v___y_684_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*3 + 2, v_suppressElabErrors_698_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*3 + 3, v_checkDeprecated_699_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*3 + 4, v_isRecordingDeps_700_);
lean_inc(v___y_701_);
lean_inc(v_a_679_);
lean_inc_ref(v_a_678_);
v___x_706_ = lean_apply_5(v_act_677_, v_a_678_, v_a_679_, v___x_705_, v___y_701_, lean_box(0));
return v___x_706_;
}
v___jp_707_:
{
lean_object* v___x_711_; lean_object* v_env_712_; lean_object* v_nextMacroScope_713_; lean_object* v_ngen_714_; lean_object* v_auxDeclNGen_715_; lean_object* v_traceState_716_; lean_object* v_recordedDeps_717_; lean_object* v_messages_718_; lean_object* v_infoState_719_; lean_object* v_snapshotTasks_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_746_; 
v___x_711_ = lean_st_ref_take(v_a_681_);
v_env_712_ = lean_ctor_get(v___x_711_, 0);
v_nextMacroScope_713_ = lean_ctor_get(v___x_711_, 1);
v_ngen_714_ = lean_ctor_get(v___x_711_, 2);
v_auxDeclNGen_715_ = lean_ctor_get(v___x_711_, 3);
v_traceState_716_ = lean_ctor_get(v___x_711_, 4);
v_recordedDeps_717_ = lean_ctor_get(v___x_711_, 6);
v_messages_718_ = lean_ctor_get(v___x_711_, 7);
v_infoState_719_ = lean_ctor_get(v___x_711_, 8);
v_snapshotTasks_720_ = lean_ctor_get(v___x_711_, 9);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v___x_711_, 5);
lean_dec(v_unused_747_);
v___x_722_ = v___x_711_;
v_isShared_723_ = v_isSharedCheck_746_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_snapshotTasks_720_);
lean_inc(v_infoState_719_);
lean_inc(v_messages_718_);
lean_inc(v_recordedDeps_717_);
lean_inc(v_traceState_716_);
lean_inc(v_auxDeclNGen_715_);
lean_inc(v_ngen_714_);
lean_inc(v_nextMacroScope_713_);
lean_inc(v_env_712_);
lean_dec(v___x_711_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_746_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = l_Lean_Kernel_enableDiag(v_env_712_, v___y_710_);
v___x_725_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 5, v___x_725_);
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_nextMacroScope_713_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_ngen_714_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_auxDeclNGen_715_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_traceState_716_);
lean_ctor_set(v_reuseFailAlloc_745_, 5, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_745_, 6, v_recordedDeps_717_);
lean_ctor_set(v_reuseFailAlloc_745_, 7, v_messages_718_);
lean_ctor_set(v_reuseFailAlloc_745_, 8, v_infoState_719_);
lean_ctor_set(v_reuseFailAlloc_745_, 9, v_snapshotTasks_720_);
v___x_727_ = v_reuseFailAlloc_745_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v_toCold_729_; lean_object* v_currRecDepth_730_; lean_object* v_ref_731_; uint8_t v_suppressElabErrors_732_; uint8_t v_checkDeprecated_733_; uint8_t v_isRecordingDeps_734_; lean_object* v_fileName_735_; lean_object* v_fileMap_736_; lean_object* v_currNamespace_737_; lean_object* v_openDecls_738_; lean_object* v_initHeartbeats_739_; lean_object* v_maxHeartbeats_740_; lean_object* v_quotContext_741_; lean_object* v_currMacroScope_742_; lean_object* v_cancelTk_x3f_743_; lean_object* v_inheritedTraceOptions_744_; 
v___x_728_ = lean_st_ref_put(v_a_681_, v___x_727_);
v_toCold_729_ = lean_ctor_get(v_a_680_, 0);
v_currRecDepth_730_ = lean_ctor_get(v_a_680_, 1);
v_ref_731_ = lean_ctor_get(v_a_680_, 2);
v_suppressElabErrors_732_ = lean_ctor_get_uint8(v_a_680_, sizeof(void*)*3 + 2);
v_checkDeprecated_733_ = lean_ctor_get_uint8(v_a_680_, sizeof(void*)*3 + 3);
v_isRecordingDeps_734_ = lean_ctor_get_uint8(v_a_680_, sizeof(void*)*3 + 4);
v_fileName_735_ = lean_ctor_get(v_toCold_729_, 0);
v_fileMap_736_ = lean_ctor_get(v_toCold_729_, 1);
v_currNamespace_737_ = lean_ctor_get(v_toCold_729_, 4);
v_openDecls_738_ = lean_ctor_get(v_toCold_729_, 5);
v_initHeartbeats_739_ = lean_ctor_get(v_toCold_729_, 6);
v_maxHeartbeats_740_ = lean_ctor_get(v_toCold_729_, 7);
v_quotContext_741_ = lean_ctor_get(v_toCold_729_, 8);
v_currMacroScope_742_ = lean_ctor_get(v_toCold_729_, 9);
v_cancelTk_x3f_743_ = lean_ctor_get(v_toCold_729_, 10);
v_inheritedTraceOptions_744_ = lean_ctor_get(v_toCold_729_, 11);
lean_inc_ref(v_inheritedTraceOptions_744_);
lean_inc(v_cancelTk_x3f_743_);
lean_inc(v_currMacroScope_742_);
lean_inc(v_quotContext_741_);
lean_inc(v_maxHeartbeats_740_);
lean_inc(v_initHeartbeats_739_);
lean_inc(v_openDecls_738_);
lean_inc(v_currNamespace_737_);
lean_inc_ref(v_fileMap_736_);
lean_inc_ref(v_fileName_735_);
v___y_684_ = v___y_709_;
v___y_685_ = v___y_708_;
v_fileName_686_ = v_fileName_735_;
v_fileMap_687_ = v_fileMap_736_;
v_currNamespace_688_ = v_currNamespace_737_;
v_openDecls_689_ = v_openDecls_738_;
v_initHeartbeats_690_ = v_initHeartbeats_739_;
v_maxHeartbeats_691_ = v_maxHeartbeats_740_;
v_quotContext_692_ = v_quotContext_741_;
v_currMacroScope_693_ = v_currMacroScope_742_;
v_cancelTk_x3f_694_ = v_cancelTk_x3f_743_;
v_inheritedTraceOptions_695_ = v_inheritedTraceOptions_744_;
v_currRecDepth_696_ = v_currRecDepth_730_;
v_ref_697_ = v_ref_731_;
v_suppressElabErrors_698_ = v_suppressElabErrors_732_;
v_checkDeprecated_699_ = v_checkDeprecated_733_;
v_isRecordingDeps_700_ = v_isRecordingDeps_734_;
v___y_701_ = v_a_681_;
goto v___jp_683_;
}
}
}
v___jp_766_:
{
uint16_t v___x_768_; lean_object* v___x_769_; lean_object* v_env_770_; uint8_t v___x_771_; uint16_t v___x_772_; uint16_t v___x_773_; uint16_t v___x_774_; uint8_t v___x_775_; 
v___x_768_ = l_Lean_OptionFlags_ofOptions(v___y_767_);
v___x_769_ = lean_st_ref_get(v_a_681_);
v_env_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_ref(v_env_770_);
lean_dec(v___x_769_);
v___x_771_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_770_);
lean_dec_ref(v_env_770_);
v___x_772_ = 512;
v___x_773_ = lean_uint16_land(v___x_768_, v___x_772_);
v___x_774_ = 0;
v___x_775_ = lean_uint16_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
if (v___x_771_ == 0)
{
uint8_t v___x_776_; 
v___x_776_ = 1;
v___y_708_ = v___y_767_;
v___y_709_ = v___x_768_;
v___y_710_ = v___x_776_;
goto v___jp_707_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_765_);
lean_inc(v_cancelTk_x3f_764_);
lean_inc(v_currMacroScope_763_);
lean_inc(v_quotContext_762_);
lean_inc(v_maxHeartbeats_761_);
lean_inc(v_initHeartbeats_760_);
lean_inc(v_openDecls_759_);
lean_inc(v_currNamespace_758_);
lean_inc_ref(v_fileMap_756_);
lean_inc_ref(v_fileName_755_);
v___y_684_ = v___x_768_;
v___y_685_ = v___y_767_;
v_fileName_686_ = v_fileName_755_;
v_fileMap_687_ = v_fileMap_756_;
v_currNamespace_688_ = v_currNamespace_758_;
v_openDecls_689_ = v_openDecls_759_;
v_initHeartbeats_690_ = v_initHeartbeats_760_;
v_maxHeartbeats_691_ = v_maxHeartbeats_761_;
v_quotContext_692_ = v_quotContext_762_;
v_currMacroScope_693_ = v_currMacroScope_763_;
v_cancelTk_x3f_694_ = v_cancelTk_x3f_764_;
v_inheritedTraceOptions_695_ = v_inheritedTraceOptions_765_;
v_currRecDepth_696_ = v_currRecDepth_750_;
v_ref_697_ = v_ref_751_;
v_suppressElabErrors_698_ = v_suppressElabErrors_752_;
v_checkDeprecated_699_ = v_checkDeprecated_753_;
v_isRecordingDeps_700_ = v_isRecordingDeps_754_;
v___y_701_ = v_a_681_;
goto v___jp_683_;
}
}
else
{
if (v___x_771_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_765_);
lean_inc(v_cancelTk_x3f_764_);
lean_inc(v_currMacroScope_763_);
lean_inc(v_quotContext_762_);
lean_inc(v_maxHeartbeats_761_);
lean_inc(v_initHeartbeats_760_);
lean_inc(v_openDecls_759_);
lean_inc(v_currNamespace_758_);
lean_inc_ref(v_fileMap_756_);
lean_inc_ref(v_fileName_755_);
v___y_684_ = v___x_768_;
v___y_685_ = v___y_767_;
v_fileName_686_ = v_fileName_755_;
v_fileMap_687_ = v_fileMap_756_;
v_currNamespace_688_ = v_currNamespace_758_;
v_openDecls_689_ = v_openDecls_759_;
v_initHeartbeats_690_ = v_initHeartbeats_760_;
v_maxHeartbeats_691_ = v_maxHeartbeats_761_;
v_quotContext_692_ = v_quotContext_762_;
v_currMacroScope_693_ = v_currMacroScope_763_;
v_cancelTk_x3f_694_ = v_cancelTk_x3f_764_;
v_inheritedTraceOptions_695_ = v_inheritedTraceOptions_765_;
v_currRecDepth_696_ = v_currRecDepth_750_;
v_ref_697_ = v_ref_751_;
v_suppressElabErrors_698_ = v_suppressElabErrors_752_;
v_checkDeprecated_699_ = v_checkDeprecated_753_;
v_isRecordingDeps_700_ = v_isRecordingDeps_754_;
v___y_701_ = v_a_681_;
goto v___jp_683_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = 0;
v___y_708_ = v___y_767_;
v___y_709_ = v___x_768_;
v___y_710_ = v___x_777_;
goto v___jp_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_801_, lean_object* v_act_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_801_, v_act_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_809_, lean_object* v_declName_810_, lean_object* v_act_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_810_, v_act_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_818_, lean_object* v_declName_819_, lean_object* v_act_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_818_, v_declName_819_, v_act_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_env_831_; lean_object* v_toConstantVal_832_; lean_object* v_value_833_; lean_object* v_all_834_; lean_object* v_type_841_; uint8_t v___x_842_; 
v___x_830_ = lean_st_ref_get(v___y_828_);
v_env_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref_n(v_env_831_, 2);
lean_dec(v___x_830_);
v_toConstantVal_832_ = lean_ctor_get(v_thm_827_, 0);
v_value_833_ = lean_ctor_get(v_thm_827_, 1);
v_all_834_ = lean_ctor_get(v_thm_827_, 2);
v_type_841_ = lean_ctor_get(v_toConstantVal_832_, 2);
v___x_842_ = l_Lean_Environment_hasUnsafe(v_env_831_, v_type_841_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = l_Lean_Environment_hasUnsafe(v_env_831_, v_value_833_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_844_, 0, v_thm_827_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
else
{
lean_inc(v_all_834_);
lean_inc_ref(v_value_833_);
lean_inc_ref(v_toConstantVal_832_);
lean_dec_ref(v_thm_827_);
goto v___jp_835_;
}
}
else
{
lean_inc(v_all_834_);
lean_inc_ref(v_value_833_);
lean_inc_ref(v_toConstantVal_832_);
lean_dec_ref(v_env_831_);
lean_dec_ref(v_thm_827_);
goto v___jp_835_;
}
v___jp_835_:
{
lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_836_ = lean_box(0);
v___x_837_ = 0;
v___x_838_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_838_, 0, v_toConstantVal_832_);
lean_ctor_set(v___x_838_, 1, v_value_833_);
lean_ctor_set(v___x_838_, 2, v___x_836_);
lean_ctor_set(v___x_838_, 3, v_all_834_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*4, v___x_837_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_846_, v___y_847_);
lean_dec(v___y_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_850_, v___y_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_864_, lean_object* v_b_865_, lean_object* v_c_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
lean_inc(v___y_870_);
lean_inc_ref(v___y_869_);
lean_inc(v___y_868_);
lean_inc_ref(v___y_867_);
v___x_872_ = lean_apply_7(v_k_864_, v_b_865_, v_c_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, lean_box(0));
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_873_, lean_object* v_b_874_, lean_object* v_c_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_873_, v_b_874_, v_c_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_882_, lean_object* v_k_883_, uint8_t v_cleanupAnnotations_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___f_890_; uint8_t v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_890_, 0, v_k_883_);
v___x_891_ = 1;
v___x_892_ = 0;
v___x_893_ = lean_box(0);
v___x_894_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_882_, v___x_891_, v___x_892_, v___x_891_, v___x_892_, v___x_893_, v___f_890_, v_cleanupAnnotations_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_a_903_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_894_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_894_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_911_, lean_object* v_k_912_, lean_object* v_cleanupAnnotations_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_919_; lean_object* v_res_920_; 
v_cleanupAnnotations_boxed_919_ = lean_unbox(v_cleanupAnnotations_913_);
v_res_920_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_911_, v_k_912_, v_cleanupAnnotations_boxed_919_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_921_, lean_object* v_e_922_, lean_object* v_k_923_, uint8_t v_cleanupAnnotations_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_922_, v_k_923_, v_cleanupAnnotations_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_931_, lean_object* v_e_932_, lean_object* v_k_933_, lean_object* v_cleanupAnnotations_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_940_; lean_object* v_res_941_; 
v_cleanupAnnotations_boxed_940_ = lean_unbox(v_cleanupAnnotations_934_);
v_res_941_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_931_, v_e_932_, v_k_933_, v_cleanupAnnotations_boxed_940_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
if (lean_obj_tag(v_a_942_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = l_List_reverse___redArg(v_a_943_);
return v___x_944_;
}
else
{
lean_object* v_head_945_; lean_object* v_tail_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_955_; 
v_head_945_ = lean_ctor_get(v_a_942_, 0);
v_tail_946_ = lean_ctor_get(v_a_942_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_a_942_);
if (v_isSharedCheck_955_ == 0)
{
v___x_948_ = v_a_942_;
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_tail_946_);
lean_inc(v_head_945_);
lean_dec(v_a_942_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = l_Lean_mkLevelParam(v_head_945_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_a_943_);
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_a_943_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
v_a_942_ = v_tail_946_;
v_a_943_ = v___x_952_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_956_, lean_object* v_name_957_, lean_object* v_xs_958_, lean_object* v_body_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_name_965_; lean_object* v_levelParams_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1036_; 
v_name_965_ = lean_ctor_get(v_toConstantVal_956_, 0);
v_levelParams_966_ = lean_ctor_get(v_toConstantVal_956_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_toConstantVal_956_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v_toConstantVal_956_, 2);
lean_dec(v_unused_1037_);
v___x_968_ = v_toConstantVal_956_;
v_isShared_969_ = v_isSharedCheck_1036_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_levelParams_966_);
lean_inc(v_name_965_);
lean_dec(v_toConstantVal_956_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1036_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_lhs_973_; lean_object* v___x_974_; 
v___x_970_ = lean_box(0);
lean_inc(v_levelParams_966_);
v___x_971_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_966_, v___x_970_);
v___x_972_ = l_Lean_mkConst(v_name_965_, v___x_971_);
v_lhs_973_ = l_Lean_mkAppN(v___x_972_, v_xs_958_);
lean_inc_ref(v_lhs_973_);
v___x_974_ = l_Lean_Meta_mkEq(v_lhs_973_, v_body_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; uint8_t v___x_976_; uint8_t v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = 0;
v___x_977_ = 1;
v___x_978_ = 1;
v___x_979_ = l_Lean_Meta_mkForallFVars(v_xs_958_, v_a_975_, v___x_976_, v___x_977_, v___x_977_, v___x_978_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Lean_Meta_letToHave(v_a_980_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l_Lean_Meta_mkEqRefl(v_lhs_973_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l_Lean_Meta_mkLambdaFVars(v_xs_958_, v_a_984_, v___x_976_, v___x_977_, v___x_976_, v___x_977_, v___x_978_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
lean_inc(v_name_957_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 2, v_a_982_);
lean_ctor_set(v___x_968_, 0, v_name_957_);
v___x_988_ = v___x_968_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_name_957_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_levelParams_966_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_a_982_);
v___x_988_ = v_reuseFailAlloc_995_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_a_992_; lean_object* v___x_993_; 
lean_inc(v_name_957_);
v___x_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_989_, 0, v_name_957_);
lean_ctor_set(v___x_989_, 1, v___x_970_);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v_a_986_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
v___x_991_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_990_, v___y_963_);
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v___x_991_);
v___x_993_ = l_Lean_addDecl(v_a_992_, v___x_976_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; 
lean_dec_ref_known(v___x_993_, 1);
v___x_994_ = l_Lean_inferDefEqAttr(v_name_957_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
return v___x_994_;
}
else
{
lean_dec(v_name_957_);
return v___x_993_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_982_);
lean_del_object(v___x_968_);
lean_dec(v_levelParams_966_);
lean_dec(v_name_957_);
v_a_996_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_985_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_985_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_a_982_);
lean_del_object(v___x_968_);
lean_dec(v_levelParams_966_);
lean_dec(v_name_957_);
v_a_1004_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_983_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_983_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_lhs_973_);
lean_del_object(v___x_968_);
lean_dec(v_levelParams_966_);
lean_dec(v_name_957_);
v_a_1012_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_981_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_981_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_lhs_973_);
lean_del_object(v___x_968_);
lean_dec(v_levelParams_966_);
lean_dec(v_name_957_);
v_a_1020_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_979_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_979_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v_lhs_973_);
lean_del_object(v___x_968_);
lean_dec(v_levelParams_966_);
lean_dec(v_name_957_);
v_a_1028_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_974_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_974_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1038_, lean_object* v_name_1039_, lean_object* v_xs_1040_, lean_object* v_body_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1038_, v_name_1039_, v_xs_1040_, v_body_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_xs_1040_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1048_, lean_object* v_info_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_toConstantVal_1055_; lean_object* v_value_1056_; lean_object* v___f_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; 
v_toConstantVal_1055_ = lean_ctor_get(v_info_1049_, 0);
lean_inc_ref(v_toConstantVal_1055_);
v_value_1056_ = lean_ctor_get(v_info_1049_, 1);
lean_inc_ref(v_value_1056_);
lean_dec_ref(v_info_1049_);
v___f_1057_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1057_, 0, v_toConstantVal_1055_);
lean_closure_set(v___f_1057_, 1, v_name_1048_);
v___x_1058_ = 1;
v___x_1059_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1056_, v___f_1057_, v___x_1058_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1060_, lean_object* v_info_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1060_, v_info_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1068_, lean_object* v_name_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1078_; lean_object* v_env_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1078_ = lean_st_ref_get(v_a_1073_);
v_env_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_env_1079_);
lean_dec(v___x_1078_);
v___x_1080_ = 0;
lean_inc(v_declName_1068_);
v___x_1081_ = l_Lean_Environment_find_x3f(v_env_1079_, v_declName_1068_, v___x_1080_);
if (lean_obj_tag(v___x_1081_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1109_; 
v_val_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1109_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_val_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1109_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
if (lean_obj_tag(v_val_1082_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_val_1086_ = lean_ctor_get(v_val_1082_, 0);
lean_inc_ref(v_val_1086_);
lean_dec_ref_known(v_val_1082_, 1);
lean_inc_n(v_name_1069_, 2);
v___x_1087_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1087_, 0, v_name_1069_);
lean_closure_set(v___x_1087_, 1, v_val_1086_);
lean_inc(v_declName_1068_);
v___x_1088_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1088_, 0, lean_box(0));
lean_closure_set(v___x_1088_, 1, v_declName_1068_);
lean_closure_set(v___x_1088_, 2, v___x_1087_);
v___x_1089_ = l_Lean_Meta_realizeConst(v_declName_1068_, v_name_1069_, v___x_1088_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1099_; 
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1100_);
v___x_1091_ = v___x_1089_;
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v___x_1089_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v_name_1069_);
v___x_1094_ = v___x_1084_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_name_1069_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1094_);
v___x_1096_ = v___x_1091_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_del_object(v___x_1084_);
lean_dec(v_name_1069_);
v_a_1101_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1089_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1089_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_del_object(v___x_1084_);
lean_dec(v_val_1082_);
lean_dec(v_name_1069_);
lean_dec(v_declName_1068_);
goto v___jp_1075_;
}
}
}
else
{
lean_dec(v___x_1081_);
lean_dec(v_name_1069_);
lean_dec(v_declName_1068_);
goto v___jp_1075_;
}
v___jp_1075_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1110_, lean_object* v_name_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1110_, v_name_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1118_, lean_object* v_vals_1119_, lean_object* v_i_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_array_get_size(v_keys_1118_);
v___x_1123_ = lean_nat_dec_lt(v_i_1120_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec(v_i_1120_);
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
else
{
lean_object* v_k_x27_1125_; uint8_t v___x_1126_; 
v_k_x27_1125_ = lean_array_fget_borrowed(v_keys_1118_, v_i_1120_);
v___x_1126_ = lean_name_eq(v_k_1121_, v_k_x27_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_i_1120_, v___x_1127_);
lean_dec(v_i_1120_);
v_i_1120_ = v___x_1128_;
goto _start;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_array_fget_borrowed(v_vals_1119_, v_i_1120_);
lean_dec(v_i_1120_);
lean_inc(v___x_1130_);
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1132_, lean_object* v_vals_1133_, lean_object* v_i_1134_, lean_object* v_k_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1132_, v_vals_1133_, v_i_1134_, v_k_1135_);
lean_dec(v_k_1135_);
lean_dec_ref(v_vals_1133_);
lean_dec_ref(v_keys_1132_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1137_, size_t v_x_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1137_) == 0)
{
lean_object* v_es_1140_; lean_object* v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; lean_object* v_j_1144_; lean_object* v___x_1145_; 
v_es_1140_ = lean_ctor_get(v_x_1137_, 0);
v___x_1141_ = lean_box(2);
v___x_1142_ = ((size_t)31ULL);
v___x_1143_ = lean_usize_land(v_x_1138_, v___x_1142_);
v_j_1144_ = lean_usize_to_nat(v___x_1143_);
v___x_1145_ = lean_array_get_borrowed(v___x_1141_, v_es_1140_, v_j_1144_);
lean_dec(v_j_1144_);
switch(lean_obj_tag(v___x_1145_))
{
case 0:
{
lean_object* v_key_1146_; lean_object* v_val_1147_; uint8_t v___x_1148_; 
v_key_1146_ = lean_ctor_get(v___x_1145_, 0);
v_val_1147_ = lean_ctor_get(v___x_1145_, 1);
v___x_1148_ = lean_name_eq(v_x_1139_, v_key_1146_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
else
{
lean_object* v___x_1150_; 
lean_inc(v_val_1147_);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_val_1147_);
return v___x_1150_;
}
}
case 1:
{
lean_object* v_node_1151_; size_t v___x_1152_; size_t v___x_1153_; 
v_node_1151_ = lean_ctor_get(v___x_1145_, 0);
v___x_1152_ = ((size_t)5ULL);
v___x_1153_ = lean_usize_shift_right(v_x_1138_, v___x_1152_);
v_x_1137_ = v_node_1151_;
v_x_1138_ = v___x_1153_;
goto _start;
}
default: 
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_box(0);
return v___x_1155_;
}
}
}
else
{
lean_object* v_ks_1156_; lean_object* v_vs_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_ks_1156_ = lean_ctor_get(v_x_1137_, 0);
v_vs_1157_ = lean_ctor_get(v_x_1137_, 1);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1156_, v_vs_1157_, v___x_1158_, v_x_1139_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
size_t v_x_344__boxed_1163_; lean_object* v_res_1164_; 
v_x_344__boxed_1163_ = lean_unbox_usize(v_x_1161_);
lean_dec(v_x_1161_);
v_res_1164_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1160_, v_x_344__boxed_1163_, v_x_1162_);
lean_dec(v_x_1162_);
lean_dec_ref(v_x_1160_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
uint64_t v___y_1168_; 
if (lean_obj_tag(v_x_1166_) == 0)
{
uint64_t v___x_1171_; 
v___x_1171_ = 1723ULL;
v___y_1168_ = v___x_1171_;
goto v___jp_1167_;
}
else
{
uint64_t v_hash_1172_; 
v_hash_1172_ = lean_ctor_get_uint64(v_x_1166_, sizeof(void*)*2);
v___y_1168_ = v_hash_1172_;
goto v___jp_1167_;
}
v___jp_1167_:
{
size_t v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_uint64_to_usize(v___y_1168_);
v___x_1170_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1165_, v___x_1169_, v_x_1166_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1173_, v_x_1174_);
lean_dec(v_x_1174_);
lean_dec_ref(v_x_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_env_1181_; lean_object* v___x_1182_; lean_object* v_asyncMode_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1179_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1180_ = lean_st_ref_get(v_a_1177_);
v_env_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_ref(v_env_1181_);
lean_dec(v___x_1180_);
v___x_1182_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1183_ = lean_ctor_get(v___x_1182_, 2);
v___x_1184_ = lean_box(0);
v___x_1185_ = 0;
v___x_1186_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1179_, v___x_1182_, v_env_1181_, v_asyncMode_1183_, v___x_1184_, v___x_1185_);
v___x_1187_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1186_, v_thmName_1176_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec(v_thmName_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1193_, v_a_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_thmName_1198_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1203_, lean_object* v_x_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1204_, v_x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1207_, v_x_1208_, v_x_1209_);
lean_dec(v_x_1209_);
lean_dec_ref(v_x_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1211_, lean_object* v_x_1212_, size_t v_x_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1212_, v_x_1213_, v_x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_, lean_object* v_x_1219_){
_start:
{
size_t v_x_439__boxed_1220_; lean_object* v_res_1221_; 
v_x_439__boxed_1220_ = lean_unbox_usize(v_x_1218_);
lean_dec(v_x_1218_);
v_res_1221_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1216_, v_x_1217_, v_x_439__boxed_1220_, v_x_1219_);
lean_dec(v_x_1219_);
lean_dec_ref(v_x_1217_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1222_, lean_object* v_keys_1223_, lean_object* v_vals_1224_, lean_object* v_heq_1225_, lean_object* v_i_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1223_, v_vals_1224_, v_i_1226_, v_k_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1229_, lean_object* v_keys_1230_, lean_object* v_vals_1231_, lean_object* v_heq_1232_, lean_object* v_i_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1229_, v_keys_1230_, v_vals_1231_, v_heq_1232_, v_i_1233_, v_k_1234_);
lean_dec(v_k_1234_);
lean_dec_ref(v_vals_1231_);
lean_dec_ref(v_keys_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1236_, lean_object* v_i_1237_, lean_object* v_k_1238_){
_start:
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_array_get_size(v_keys_1236_);
v___x_1240_ = lean_nat_dec_lt(v_i_1237_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_dec(v_i_1237_);
return v___x_1240_;
}
else
{
lean_object* v_k_x27_1241_; uint8_t v___x_1242_; 
v_k_x27_1241_ = lean_array_fget_borrowed(v_keys_1236_, v_i_1237_);
v___x_1242_ = lean_name_eq(v_k_1238_, v_k_x27_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_i_1237_, v___x_1243_);
lean_dec(v_i_1237_);
v_i_1237_ = v___x_1244_;
goto _start;
}
else
{
lean_dec(v_i_1237_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1246_, lean_object* v_i_1247_, lean_object* v_k_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1246_, v_i_1247_, v_k_1248_);
lean_dec(v_k_1248_);
lean_dec_ref(v_keys_1246_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1251_, size_t v_x_1252_, lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
lean_object* v_es_1254_; lean_object* v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; lean_object* v_j_1258_; lean_object* v___x_1259_; 
v_es_1254_ = lean_ctor_get(v_x_1251_, 0);
v___x_1255_ = lean_box(2);
v___x_1256_ = ((size_t)31ULL);
v___x_1257_ = lean_usize_land(v_x_1252_, v___x_1256_);
v_j_1258_ = lean_usize_to_nat(v___x_1257_);
v___x_1259_ = lean_array_get_borrowed(v___x_1255_, v_es_1254_, v_j_1258_);
lean_dec(v_j_1258_);
switch(lean_obj_tag(v___x_1259_))
{
case 0:
{
lean_object* v_key_1260_; uint8_t v___x_1261_; 
v_key_1260_ = lean_ctor_get(v___x_1259_, 0);
v___x_1261_ = lean_name_eq(v_x_1253_, v_key_1260_);
return v___x_1261_;
}
case 1:
{
lean_object* v_node_1262_; size_t v___x_1263_; size_t v___x_1264_; 
v_node_1262_ = lean_ctor_get(v___x_1259_, 0);
v___x_1263_ = ((size_t)5ULL);
v___x_1264_ = lean_usize_shift_right(v_x_1252_, v___x_1263_);
v_x_1251_ = v_node_1262_;
v_x_1252_ = v___x_1264_;
goto _start;
}
default: 
{
uint8_t v___x_1266_; 
v___x_1266_ = 0;
return v___x_1266_;
}
}
}
else
{
lean_object* v_ks_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_ks_1267_ = lean_ctor_get(v_x_1251_, 0);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1267_, v___x_1268_, v_x_1253_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
size_t v_x_328__boxed_1273_; uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_x_328__boxed_1273_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_res_1274_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1270_, v_x_328__boxed_1273_, v_x_1272_);
lean_dec(v_x_1272_);
lean_dec_ref(v_x_1270_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
uint64_t v___y_1279_; 
if (lean_obj_tag(v_x_1277_) == 0)
{
uint64_t v___x_1282_; 
v___x_1282_ = 1723ULL;
v___y_1279_ = v___x_1282_;
goto v___jp_1278_;
}
else
{
uint64_t v_hash_1283_; 
v_hash_1283_ = lean_ctor_get_uint64(v_x_1277_, sizeof(void*)*2);
v___y_1279_ = v_hash_1283_;
goto v___jp_1278_;
}
v___jp_1278_:
{
size_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_uint64_to_usize(v___y_1279_);
v___x_1281_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1276_, v___x_1280_, v_x_1277_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1284_, v_x_1285_);
lean_dec(v_x_1285_);
lean_dec_ref(v_x_1284_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_env_1293_; lean_object* v___x_1294_; lean_object* v_asyncMode_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1291_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1292_ = lean_st_ref_get(v_a_1289_);
v_env_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_ref(v_env_1293_);
lean_dec(v___x_1292_);
v___x_1294_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1295_ = lean_ctor_get(v___x_1294_, 2);
v___x_1296_ = lean_box(0);
v___x_1297_ = 0;
v___x_1298_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1291_, v___x_1294_, v_env_1293_, v_asyncMode_1295_, v___x_1296_, v___x_1297_);
v___x_1299_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1298_, v_thmName_1288_);
lean_dec(v___x_1298_);
v___x_1300_ = lean_box(v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec(v_thmName_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1306_, v_a_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Meta_isEqnThm(v_thmName_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_thmName_1311_);
return v_res_1315_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
uint8_t v_res_1323_; lean_object* v_r_1324_; 
v_res_1323_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1320_, v_x_1321_, v_x_1322_);
lean_dec(v_x_1322_);
lean_dec_ref(v_x_1321_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1325_, lean_object* v_x_1326_, size_t v_x_1327_, lean_object* v_x_1328_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1326_, v_x_1327_, v_x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
size_t v_x_419__boxed_1334_; uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_x_419__boxed_1334_ = lean_unbox_usize(v_x_1332_);
lean_dec(v_x_1332_);
v_res_1335_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1330_, v_x_1331_, v_x_419__boxed_1334_, v_x_1333_);
lean_dec(v_x_1333_);
lean_dec_ref(v_x_1331_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1337_, lean_object* v_keys_1338_, lean_object* v_vals_1339_, lean_object* v_heq_1340_, lean_object* v_i_1341_, lean_object* v_k_1342_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1338_, v_i_1341_, v_k_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1344_, lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_heq_1347_, lean_object* v_i_1348_, lean_object* v_k_1349_){
_start:
{
uint8_t v_res_1350_; lean_object* v_r_1351_; 
v_res_1350_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1344_, v_keys_1345_, v_vals_1346_, v_heq_1347_, v_i_1348_, v_k_1349_);
lean_dec(v_k_1349_);
lean_dec_ref(v_vals_1346_);
lean_dec_ref(v_keys_1345_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1352_, lean_object* v_msg_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_panic_fn_borrowed(v_x1_1352_, v_msg_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1355_, lean_object* v_msg_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1355_, v_msg_1356_);
lean_dec_ref(v_x1_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
lean_object* v_ks_1362_; lean_object* v_vs_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1387_; 
v_ks_1362_ = lean_ctor_get(v_x_1358_, 0);
v_vs_1363_ = lean_ctor_get(v_x_1358_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1365_ = v_x_1358_;
v_isShared_1366_ = v_isSharedCheck_1387_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_vs_1363_);
lean_inc(v_ks_1362_);
lean_dec(v_x_1358_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1387_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_ks_1362_);
v___x_1368_ = lean_nat_dec_lt(v_x_1359_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec(v_x_1359_);
v___x_1369_ = lean_array_push(v_ks_1362_, v_x_1360_);
v___x_1370_ = lean_array_push(v_vs_1363_, v_x_1361_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1370_);
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1372_ = v___x_1365_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v_k_x27_1374_; uint8_t v___x_1375_; 
v_k_x27_1374_ = lean_array_fget_borrowed(v_ks_1362_, v_x_1359_);
v___x_1375_ = lean_name_eq(v_x_1360_, v_k_x27_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1377_; 
if (v_isShared_1366_ == 0)
{
v___x_1377_ = v___x_1365_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_ks_1362_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_vs_1363_);
v___x_1377_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_add(v_x_1359_, v___x_1378_);
lean_dec(v_x_1359_);
v_x_1358_ = v___x_1377_;
v_x_1359_ = v___x_1379_;
goto _start;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = lean_array_fset(v_ks_1362_, v_x_1359_, v_x_1360_);
v___x_1383_ = lean_array_fset(v_vs_1363_, v_x_1359_, v_x_1361_);
lean_dec(v_x_1359_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1383_);
lean_ctor_set(v___x_1365_, 0, v___x_1382_);
v___x_1385_ = v___x_1365_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1388_, lean_object* v_k_1389_, lean_object* v_v_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1388_, v___x_1391_, v_k_1389_, v_v_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1394_, size_t v_x_1395_, size_t v_x_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 0)
{
lean_object* v_es_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v_j_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_es_1399_ = lean_ctor_get(v_x_1394_, 0);
v___x_1400_ = ((size_t)31ULL);
v___x_1401_ = lean_usize_land(v_x_1395_, v___x_1400_);
v_j_1402_ = lean_usize_to_nat(v___x_1401_);
v___x_1403_ = lean_array_get_size(v_es_1399_);
v___x_1404_ = lean_nat_dec_lt(v_j_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_dec(v_j_1402_);
lean_dec(v_x_1398_);
lean_dec(v_x_1397_);
return v_x_1394_;
}
else
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1443_; 
lean_inc_ref(v_es_1399_);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v_x_1394_, 0);
lean_dec(v_unused_1444_);
v___x_1406_ = v_x_1394_;
v_isShared_1407_ = v_isSharedCheck_1443_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_x_1394_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1443_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_v_1408_; lean_object* v___x_1409_; lean_object* v_xs_x27_1410_; lean_object* v___y_1412_; 
v_v_1408_ = lean_array_fget(v_es_1399_, v_j_1402_);
v___x_1409_ = lean_box(0);
v_xs_x27_1410_ = lean_array_fset(v_es_1399_, v_j_1402_, v___x_1409_);
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
v___x_1422_ = lean_name_eq(v_x_1397_, v_key_1417_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_del_object(v___x_1420_);
v___x_1423_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1417_, v_val_1418_, v_x_1397_, v_x_1398_);
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
lean_ctor_set(v___x_1420_, 1, v_x_1398_);
lean_ctor_set(v___x_1420_, 0, v_x_1397_);
v___x_1426_ = v___x_1420_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_x_1397_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_x_1398_);
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
lean_object* v_node_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1441_; 
v_node_1429_ = lean_ctor_get(v_v_1408_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_v_1408_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1431_ = v_v_1408_;
v_isShared_1432_ = v_isSharedCheck_1441_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_node_1429_);
lean_dec(v_v_1408_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1441_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
size_t v___x_1433_; size_t v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1433_ = ((size_t)5ULL);
v___x_1434_ = lean_usize_shift_right(v_x_1395_, v___x_1433_);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_add(v_x_1396_, v___x_1435_);
v___x_1437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1429_, v___x_1434_, v___x_1436_, v_x_1397_, v_x_1398_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1437_);
v___x_1439_ = v___x_1431_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v___y_1412_ = v___x_1439_;
goto v___jp_1411_;
}
}
}
default: 
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_x_1397_);
lean_ctor_set(v___x_1442_, 1, v_x_1398_);
v___y_1412_ = v___x_1442_;
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
lean_object* v_ks_1445_; lean_object* v_vs_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1464_; 
v_ks_1445_ = lean_ctor_get(v_x_1394_, 0);
v_vs_1446_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1448_ = v_x_1394_;
v_isShared_1449_ = v_isSharedCheck_1464_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_vs_1446_);
lean_inc(v_ks_1445_);
lean_dec(v_x_1394_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1464_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_ks_1445_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_vs_1446_);
v___x_1451_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v_newNode_1452_; size_t v___x_1453_; uint8_t v___x_1454_; 
v_newNode_1452_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1451_, v_x_1397_, v_x_1398_);
v___x_1453_ = ((size_t)7ULL);
v___x_1454_ = lean_usize_dec_le(v___x_1453_, v_x_1396_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1452_);
v___x_1456_ = lean_unsigned_to_nat(4u);
v___x_1457_ = lean_nat_dec_lt(v___x_1455_, v___x_1456_);
lean_dec(v___x_1455_);
if (v___x_1457_ == 0)
{
lean_object* v_ks_1458_; lean_object* v_vs_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_ks_1458_ = lean_ctor_get(v_newNode_1452_, 0);
lean_inc_ref(v_ks_1458_);
v_vs_1459_ = lean_ctor_get(v_newNode_1452_, 1);
lean_inc_ref(v_vs_1459_);
lean_dec_ref(v_newNode_1452_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1396_, v_ks_1458_, v_vs_1459_, v___x_1460_, v___x_1461_);
lean_dec_ref(v_vs_1459_);
lean_dec_ref(v_ks_1458_);
return v___x_1462_;
}
else
{
return v_newNode_1452_;
}
}
else
{
return v_newNode_1452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1465_, lean_object* v_keys_1466_, lean_object* v_vals_1467_, lean_object* v_i_1468_, lean_object* v_entries_1469_){
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
v___x_1486_ = 1723ULL;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1488_, lean_object* v_keys_1489_, lean_object* v_vals_1490_, lean_object* v_i_1491_, lean_object* v_entries_1492_){
_start:
{
size_t v_depth_boxed_1493_; lean_object* v_res_1494_; 
v_depth_boxed_1493_ = lean_unbox_usize(v_depth_1488_);
lean_dec(v_depth_1488_);
v_res_1494_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1493_, v_keys_1489_, v_vals_1490_, v_i_1491_, v_entries_1492_);
lean_dec_ref(v_vals_1490_);
lean_dec_ref(v_keys_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
size_t v_x_905__boxed_1500_; size_t v_x_906__boxed_1501_; lean_object* v_res_1502_; 
v_x_905__boxed_1500_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_x_906__boxed_1501_ = lean_unbox_usize(v_x_1497_);
lean_dec(v_x_1497_);
v_res_1502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1495_, v_x_905__boxed_1500_, v_x_906__boxed_1501_, v_x_1498_, v_x_1499_);
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
v___x_1511_ = 1723ULL;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1518_, lean_object* v_as_1519_, size_t v_i_1520_, size_t v_stop_1521_, lean_object* v_b_1522_){
_start:
{
lean_object* v___y_1524_; uint8_t v___x_1528_; 
v___x_1528_ = lean_usize_dec_eq(v_i_1520_, v_stop_1521_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_array_uget_borrowed(v_as_1519_, v_i_1520_);
v___x_1530_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1522_, v___x_1529_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_declName_1518_);
lean_inc(v___x_1529_);
v___x_1531_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1522_, v___x_1529_, v_declName_1518_);
v___y_1524_ = v___x_1531_;
goto v___jp_1523_;
}
else
{
lean_object* v_val_1532_; uint8_t v___x_1533_; 
v_val_1532_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1533_ = lean_name_eq(v_val_1532_, v_declName_1518_);
if (v___x_1533_ == 0)
{
uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1534_ = 1;
v___x_1535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1537_ = lean_unsigned_to_nat(227u);
v___x_1538_ = lean_unsigned_to_nat(10u);
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1529_);
v___x_1540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1529_, v___x_1534_);
v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1543_ = lean_string_append(v___x_1541_, v___x_1542_);
v___x_1544_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1532_, v___x_1534_);
v___x_1545_ = lean_string_append(v___x_1543_, v___x_1544_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1547_ = lean_string_append(v___x_1545_, v___x_1546_);
v___x_1548_ = l_mkPanicMessageWithDecl(v___x_1535_, v___x_1536_, v___x_1537_, v___x_1538_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = lean_panic_fn_borrowed(v_b_1522_, v___x_1548_);
lean_dec_ref(v_b_1522_);
v___y_1524_ = v___x_1549_;
goto v___jp_1523_;
}
else
{
lean_dec(v_val_1532_);
v___y_1524_ = v_b_1522_;
goto v___jp_1523_;
}
}
}
else
{
lean_dec(v_declName_1518_);
return v_b_1522_;
}
v___jp_1523_:
{
size_t v___x_1525_; size_t v___x_1526_; 
v___x_1525_ = ((size_t)1ULL);
v___x_1526_ = lean_usize_add(v_i_1520_, v___x_1525_);
v_i_1520_ = v___x_1526_;
v_b_1522_ = v___y_1524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1550_, lean_object* v_as_1551_, lean_object* v_i_1552_, lean_object* v_stop_1553_, lean_object* v_b_1554_){
_start:
{
size_t v_i_boxed_1555_; size_t v_stop_boxed_1556_; lean_object* v_res_1557_; 
v_i_boxed_1555_ = lean_unbox_usize(v_i_1552_);
lean_dec(v_i_1552_);
v_stop_boxed_1556_ = lean_unbox_usize(v_stop_1553_);
lean_dec(v_stop_1553_);
v_res_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1550_, v_as_1551_, v_i_boxed_1555_, v_stop_boxed_1556_, v_b_1554_);
lean_dec_ref(v_as_1551_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1558_, lean_object* v_declName_1559_, lean_object* v_s_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = lean_array_get_size(v_eqThms_1558_);
v___x_1563_ = lean_nat_dec_lt(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_dec(v_declName_1559_);
return v_s_1560_;
}
else
{
size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = lean_usize_of_nat(v___x_1562_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1559_, v_eqThms_1558_, v___x_1564_, v___x_1565_, v_s_1560_);
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1567_, lean_object* v_declName_1568_, lean_object* v_s_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1567_, v_declName_1568_, v_s_1569_);
lean_dec_ref(v_eqThms_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1571_, lean_object* v_eqThms_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v_env_1577_; lean_object* v_nextMacroScope_1578_; lean_object* v_ngen_1579_; lean_object* v_auxDeclNGen_1580_; lean_object* v_traceState_1581_; lean_object* v_recordedDeps_1582_; lean_object* v_messages_1583_; lean_object* v_infoState_1584_; lean_object* v_snapshotTasks_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1601_; 
v___f_1575_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1575_, 0, v_eqThms_1572_);
lean_closure_set(v___f_1575_, 1, v_declName_1571_);
v___x_1576_ = lean_st_ref_take(v_a_1573_);
v_env_1577_ = lean_ctor_get(v___x_1576_, 0);
v_nextMacroScope_1578_ = lean_ctor_get(v___x_1576_, 1);
v_ngen_1579_ = lean_ctor_get(v___x_1576_, 2);
v_auxDeclNGen_1580_ = lean_ctor_get(v___x_1576_, 3);
v_traceState_1581_ = lean_ctor_get(v___x_1576_, 4);
v_recordedDeps_1582_ = lean_ctor_get(v___x_1576_, 6);
v_messages_1583_ = lean_ctor_get(v___x_1576_, 7);
v_infoState_1584_ = lean_ctor_get(v___x_1576_, 8);
v_snapshotTasks_1585_ = lean_ctor_get(v___x_1576_, 9);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1576_, 5);
lean_dec(v_unused_1602_);
v___x_1587_ = v___x_1576_;
v_isShared_1588_ = v_isSharedCheck_1601_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snapshotTasks_1585_);
lean_inc(v_infoState_1584_);
lean_inc(v_messages_1583_);
lean_inc(v_recordedDeps_1582_);
lean_inc(v_traceState_1581_);
lean_inc(v_auxDeclNGen_1580_);
lean_inc(v_ngen_1579_);
lean_inc(v_nextMacroScope_1578_);
lean_inc(v_env_1577_);
lean_dec(v___x_1576_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1601_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v_asyncMode_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1589_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1590_ = lean_ctor_get(v___x_1589_, 2);
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_box(0);
v___x_1593_ = 1;
v___x_1594_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1589_, v_env_1577_, v___f_1575_, v_asyncMode_1590_, v___x_1592_, v___x_1593_);
v___x_1595_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 5, v___x_1595_);
lean_ctor_set(v___x_1587_, 0, v___x_1594_);
v___x_1597_ = v___x_1587_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_nextMacroScope_1578_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_ngen_1579_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_auxDeclNGen_1580_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_traceState_1581_);
lean_ctor_set(v_reuseFailAlloc_1600_, 5, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1600_, 6, v_recordedDeps_1582_);
lean_ctor_set(v_reuseFailAlloc_1600_, 7, v_messages_1583_);
lean_ctor_set(v_reuseFailAlloc_1600_, 8, v_infoState_1584_);
lean_ctor_set(v_reuseFailAlloc_1600_, 9, v_snapshotTasks_1585_);
v___x_1597_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_st_ref_put(v_a_1573_, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1591_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1603_, lean_object* v_eqThms_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1603_, v_eqThms_1604_, v_a_1605_);
lean_dec(v_a_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1608_, lean_object* v_eqThms_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1608_, v_eqThms_1609_, v_a_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1614_, lean_object* v_eqThms_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1614_, v_eqThms_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1621_, v_x_1622_, v_x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1625_, lean_object* v_x_1626_, size_t v_x_1627_, size_t v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1626_, v_x_1627_, v_x_1628_, v_x_1629_, v_x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
size_t v_x_1219__boxed_1638_; size_t v_x_1220__boxed_1639_; lean_object* v_res_1640_; 
v_x_1219__boxed_1638_ = lean_unbox_usize(v_x_1634_);
lean_dec(v_x_1634_);
v_x_1220__boxed_1639_ = lean_unbox_usize(v_x_1635_);
lean_dec(v_x_1635_);
v_res_1640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1632_, v_x_1633_, v_x_1219__boxed_1638_, v_x_1220__boxed_1639_, v_x_1636_, v_x_1637_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1641_, lean_object* v_n_1642_, lean_object* v_k_1643_, lean_object* v_v_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1642_, v_k_1643_, v_v_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1646_, size_t v_depth_1647_, lean_object* v_keys_1648_, lean_object* v_vals_1649_, lean_object* v_heq_1650_, lean_object* v_i_1651_, lean_object* v_entries_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1647_, v_keys_1648_, v_vals_1649_, v_i_1651_, v_entries_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1654_, lean_object* v_depth_1655_, lean_object* v_keys_1656_, lean_object* v_vals_1657_, lean_object* v_heq_1658_, lean_object* v_i_1659_, lean_object* v_entries_1660_){
_start:
{
size_t v_depth_boxed_1661_; lean_object* v_res_1662_; 
v_depth_boxed_1661_ = lean_unbox_usize(v_depth_1655_);
lean_dec(v_depth_1655_);
v_res_1662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1654_, v_depth_boxed_1661_, v_keys_1656_, v_vals_1657_, v_heq_1658_, v_i_1659_, v_entries_1660_);
lean_dec_ref(v_vals_1657_);
lean_dec_ref(v_keys_1656_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1664_, v_x_1665_, v_x_1666_, v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1669_, lean_object* v_env_1670_, lean_object* v_idx_1671_, lean_object* v_eqs_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_nextEq_1679_; uint8_t v___x_1680_; 
v___x_1674_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_nat_add(v_idx_1671_, v___x_1675_);
lean_dec(v_idx_1671_);
lean_inc(v___x_1676_);
v___x_1677_ = l_Nat_reprFast(v___x_1676_);
v___x_1678_ = lean_string_append(v___x_1674_, v___x_1677_);
lean_dec_ref(v___x_1677_);
lean_inc(v_declName_1669_);
lean_inc_ref(v_env_1670_);
v_nextEq_1679_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1670_, v_declName_1669_, v___x_1678_);
v___x_1680_ = l_Lean_Environment_containsOnBranch(v_env_1670_, v_nextEq_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec(v_nextEq_1679_);
lean_dec(v___x_1676_);
lean_dec_ref(v_env_1670_);
lean_dec(v_declName_1669_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_eqs_1672_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_array_push(v_eqs_1672_, v_nextEq_1679_);
v_idx_1671_ = v___x_1676_;
v_eqs_1672_ = v___x_1682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1684_, lean_object* v_env_1685_, lean_object* v_idx_1686_, lean_object* v_eqs_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1684_, v_env_1685_, v_idx_1686_, v_eqs_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1690_, lean_object* v_env_1691_, lean_object* v_idx_1692_, lean_object* v_eqs_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1690_, v_env_1691_, v_idx_1692_, v_eqs_1693_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1700_, lean_object* v_env_1701_, lean_object* v_idx_1702_, lean_object* v_eqs_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1700_, v_env_1701_, v_idx_1702_, v_eqs_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v_env_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; uint8_t v___x_1718_; 
v___x_1713_ = lean_st_ref_get(v_a_1711_);
v_env_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc_ref_n(v_env_1714_, 3);
lean_dec(v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1710_);
v___x_1716_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1714_, v_declName_1710_, v___x_1715_);
v___x_1717_ = 1;
lean_inc(v___x_1716_);
v___x_1718_ = l_Lean_Environment_contains(v_env_1714_, v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec(v___x_1716_);
lean_dec_ref(v_env_1714_);
lean_dec(v_declName_1710_);
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_mk_empty_array_with_capacity(v___x_1721_);
v___x_1723_ = lean_array_push(v___x_1722_, v___x_1716_);
lean_inc(v_declName_1710_);
v___x_1724_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1710_, v_env_1714_, v___x_1721_, v___x_1723_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_n(v_a_1725_, 2);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1710_, v_a_1725_, v_a_1711_);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v___x_1726_, 0);
lean_dec(v_unused_1735_);
v___x_1728_ = v___x_1726_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v___x_1726_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1725_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_declName_1710_);
v_a_1736_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1724_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1724_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1744_, v_a_1745_);
lean_dec(v_a_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1748_, v_a_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Meta_alreadyGenerated_x3f(v_declName_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1762_, lean_object* v_localInsts_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1762_, v_localInsts_1763_, v_x_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_a_1779_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1770_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1770_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1787_, lean_object* v_localInsts_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1787_, v_localInsts_1788_, v_x_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1796_, lean_object* v_lctx_1797_, lean_object* v_localInsts_1798_, lean_object* v_x_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1797_, v_localInsts_1798_, v_x_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1806_, lean_object* v_lctx_1807_, lean_object* v_localInsts_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1806_, v_lctx_1807_, v_localInsts_1808_, v_x_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1819_, lean_object* v_as_x27_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
if (lean_obj_tag(v_as_x27_1820_) == 0)
{
lean_object* v___x_1827_; 
lean_dec(v_declName_1819_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_b_1821_);
return v___x_1827_;
}
else
{
lean_object* v_head_1828_; lean_object* v_tail_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_b_1821_);
v_head_1828_ = lean_ctor_get(v_as_x27_1820_, 0);
v_tail_1829_ = lean_ctor_get(v_as_x27_1820_, 1);
v___x_1830_ = lean_box(0);
v___x_1831_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1828_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
lean_inc(v_declName_1819_);
v___x_1832_ = lean_apply_6(v_head_1828_, v_declName_1819_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, lean_box(0));
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
if (lean_obj_tag(v_a_1833_) == 1)
{
lean_object* v_val_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1844_; 
v_val_1834_ = lean_ctor_get(v_a_1833_, 0);
lean_inc(v_val_1834_);
v___x_1835_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1819_, v_val_1834_, v___y_1825_);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; 
v_unused_1845_ = lean_ctor_get(v___x_1835_, 0);
lean_dec(v_unused_1845_);
v___x_1837_ = v___x_1835_;
v_isShared_1838_ = v_isSharedCheck_1844_;
goto v_resetjp_1836_;
}
else
{
lean_dec(v___x_1835_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1844_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1839_, 0, v_a_1833_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v___x_1830_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
lean_dec(v_a_1833_);
v_as_x27_1820_ = v_tail_1829_;
v_b_1821_ = v___x_1831_;
goto _start;
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_declName_1819_);
v_a_1847_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1832_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1832_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1855_, lean_object* v_as_x27_1856_, lean_object* v_b_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1855_, v_as_x27_1856_, v_b_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v_as_x27_1856_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
lean_inc(v_declName_1864_);
v___x_1870_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1908_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1908_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1908_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_unbox(v_a_1871_);
lean_dec(v_a_1871_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_dec(v_declName_1864_);
v___x_1876_ = lean_box(0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
else
{
lean_object* v___x_1880_; 
lean_del_object(v___x_1873_);
lean_inc(v_declName_1864_);
v___x_1880_ = l_Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1864_, v___y_1868_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
if (lean_obj_tag(v_a_1881_) == 1)
{
lean_dec(v_declName_1864_);
return v___x_1880_;
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1883_ = lean_st_ref_get(v___x_1882_);
v___x_1884_ = lean_box(0);
v___x_1885_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1886_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1864_, v___x_1883_, v___x_1885_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___x_1883_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1899_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1899_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1899_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_fst_1891_; 
v_fst_1891_ = lean_ctor_get(v_a_1887_, 0);
lean_inc(v_fst_1891_);
lean_dec(v_a_1887_);
if (lean_obj_tag(v_fst_1891_) == 0)
{
lean_object* v___x_1893_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1884_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1884_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v_val_1895_; lean_object* v___x_1897_; 
v_val_1895_ = lean_ctor_get(v_fst_1891_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v_fst_1891_, 1);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_val_1895_);
v___x_1897_ = v___x_1889_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_val_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_a_1900_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1886_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1886_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
else
{
lean_dec(v_declName_1864_);
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_declName_1864_);
v_a_1909_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1870_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1870_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1926_ = lean_box(1);
v___x_1927_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1928_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1927_);
lean_ctor_set(v___x_1929_, 2, v___x_1926_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___f_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___f_1938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1938_, 0, v_declName_1932_);
v___x_1939_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1940_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1941_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1939_, v___x_1940_, v___f_1938_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1949_, lean_object* v_as_1950_, lean_object* v_as_x27_1951_, lean_object* v_b_1952_, lean_object* v_a_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1949_, v_as_x27_1951_, v_b_1952_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1960_, lean_object* v_as_1961_, lean_object* v_as_x27_1962_, lean_object* v_b_1963_, lean_object* v_a_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1960_, v_as_1961_, v_as_x27_1962_, v_b_1963_, v_a_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v_as_x27_1962_);
lean_dec(v_as_1961_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1977_ = lean_unsigned_to_nat(32u);
v___x_1978_ = lean_mk_empty_array_with_capacity(v___x_1977_);
lean_dec_ref(v___x_1978_);
v___x_1979_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1980_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1971_);
v___x_1981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1981_, 0, v_declName_1971_);
v___x_1982_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1982_, 0, lean_box(0));
lean_closure_set(v___x_1982_, 1, v_declName_1971_);
lean_closure_set(v___x_1982_, 2, v___x_1981_);
v___x_1983_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1979_, v___x_1980_, v___x_1982_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
return v_res_1990_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_1991_, lean_object* v_opt_1992_){
_start:
{
lean_object* v_name_1993_; lean_object* v_defValue_1994_; lean_object* v_map_1995_; lean_object* v___x_1996_; 
v_name_1993_ = lean_ctor_get(v_opt_1992_, 0);
v_defValue_1994_ = lean_ctor_get(v_opt_1992_, 1);
v_map_1995_ = lean_ctor_get(v_opts_1991_, 0);
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1995_, v_name_1993_);
if (lean_obj_tag(v___x_1996_) == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_unbox(v_defValue_1994_);
return v___x_1997_;
}
else
{
lean_object* v_val_1998_; 
v_val_1998_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v___x_1996_, 1);
if (lean_obj_tag(v_val_1998_) == 1)
{
uint8_t v_v_1999_; 
v_v_1999_ = lean_ctor_get_uint8(v_val_1998_, 0);
lean_dec_ref_known(v_val_1998_, 0);
return v_v_1999_;
}
else
{
uint8_t v___x_2000_; 
lean_dec(v_val_1998_);
v___x_2000_ = lean_unbox(v_defValue_1994_);
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_2001_, lean_object* v_opt_2002_){
_start:
{
uint8_t v_res_2003_; lean_object* v_r_2004_; 
v_res_2003_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2001_, v_opt_2002_);
lean_dec_ref(v_opt_2002_);
lean_dec_ref(v_opts_2001_);
v_r_2004_ = lean_box(v_res_2003_);
return v_r_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2005_, lean_object* v_as_2006_, size_t v_sz_2007_, size_t v_i_2008_, lean_object* v_b_2009_){
_start:
{
lean_object* v_a_2012_; uint8_t v___x_2016_; 
v___x_2016_ = lean_usize_dec_lt(v_i_2008_, v_sz_2007_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_b_2009_);
return v___x_2017_;
}
else
{
lean_object* v_a_2018_; lean_object* v_name_2019_; lean_object* v_defValue_2020_; uint8_t v___x_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2032_; 
v_a_2018_ = lean_array_uget(v_as_2006_, v_i_2008_);
v_name_2019_ = lean_ctor_get(v_a_2018_, 0);
lean_inc(v_name_2019_);
v_defValue_2020_ = lean_ctor_get(v_a_2018_, 1);
lean_inc(v_defValue_2020_);
v___x_2021_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2005_, v_a_2018_);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_2018_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2033_ = lean_ctor_get(v_a_2018_, 1);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_a_2018_, 0);
lean_dec(v_unused_2034_);
v___x_2023_ = v_a_2018_;
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v_a_2018_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_unbox(v_defValue_2020_);
lean_dec(v_defValue_2020_);
if (v___x_2031_ == 0)
{
if (v___x_2021_ == 0)
{
lean_del_object(v___x_2023_);
lean_dec(v_name_2019_);
v_a_2012_ = v_b_2009_;
goto v___jp_2011_;
}
else
{
goto v___jp_2025_;
}
}
else
{
if (v___x_2021_ == 0)
{
goto v___jp_2025_;
}
else
{
lean_del_object(v___x_2023_);
lean_dec(v_name_2019_);
v_a_2012_ = v_b_2009_;
goto v___jp_2011_;
}
}
v___jp_2025_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2026_, 0, v___x_2021_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2026_);
v___x_2028_ = v___x_2023_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_name_2019_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_array_push(v_b_2009_, v___x_2028_);
v_a_2012_ = v___x_2029_;
goto v___jp_2011_;
}
}
}
}
v___jp_2011_:
{
size_t v___x_2013_; size_t v___x_2014_; 
v___x_2013_ = ((size_t)1ULL);
v___x_2014_ = lean_usize_add(v_i_2008_, v___x_2013_);
v_i_2008_ = v___x_2014_;
v_b_2009_ = v_a_2012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2035_, lean_object* v_as_2036_, lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_){
_start:
{
size_t v_sz_boxed_2041_; size_t v_i_boxed_2042_; lean_object* v_res_2043_; 
v_sz_boxed_2041_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2042_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2035_, v_as_2036_, v_sz_boxed_2041_, v_i_boxed_2042_, v_b_2039_);
lean_dec_ref(v_as_2036_);
lean_dec_ref(v___x_2035_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg();
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(lean_object* v_msgData_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v_env_2057_; uint8_t v___x_2058_; lean_object* v_env_2059_; lean_object* v___x_2060_; lean_object* v_toCold_2061_; lean_object* v_mctx_2062_; lean_object* v_lctx_2063_; lean_object* v_options_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2056_ = lean_st_ref_get(v___y_2054_);
v_env_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc_ref(v_env_2057_);
lean_dec(v___x_2056_);
v___x_2058_ = 0;
v_env_2059_ = l_Lean_Environment_setRecordingDeps(v_env_2057_, v___x_2058_);
v___x_2060_ = lean_st_ref_get(v___y_2052_);
v_toCold_2061_ = lean_ctor_get(v___y_2053_, 0);
v_mctx_2062_ = lean_ctor_get(v___x_2060_, 0);
lean_inc_ref(v_mctx_2062_);
lean_dec(v___x_2060_);
v_lctx_2063_ = lean_ctor_get(v___y_2051_, 2);
v_options_2064_ = lean_ctor_get(v_toCold_2061_, 2);
lean_inc_ref(v_options_2064_);
lean_inc_ref(v_lctx_2063_);
v___x_2065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2065_, 0, v_env_2059_);
lean_ctor_set(v___x_2065_, 1, v_mctx_2062_);
lean_ctor_set(v___x_2065_, 2, v_lctx_2063_);
lean_ctor_set(v___x_2065_, 3, v_options_2064_);
v___x_2066_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v_msgData_2050_);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4___boxed(lean_object* v_msgData_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msgData_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2074_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2075_; double v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = lean_float_of_nat(v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(lean_object* v_cls_2080_, lean_object* v_msg_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_ref_2087_; lean_object* v___x_2088_; lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2134_; 
v_ref_2087_ = lean_ctor_get(v___y_2084_, 2);
v___x_2088_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msg_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2134_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2134_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v_traceState_2094_; lean_object* v_env_2095_; lean_object* v_nextMacroScope_2096_; lean_object* v_ngen_2097_; lean_object* v_auxDeclNGen_2098_; lean_object* v_cache_2099_; lean_object* v_recordedDeps_2100_; lean_object* v_messages_2101_; lean_object* v_infoState_2102_; lean_object* v_snapshotTasks_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2133_; 
v___x_2093_ = lean_st_ref_take(v___y_2085_);
v_traceState_2094_ = lean_ctor_get(v___x_2093_, 4);
v_env_2095_ = lean_ctor_get(v___x_2093_, 0);
v_nextMacroScope_2096_ = lean_ctor_get(v___x_2093_, 1);
v_ngen_2097_ = lean_ctor_get(v___x_2093_, 2);
v_auxDeclNGen_2098_ = lean_ctor_get(v___x_2093_, 3);
v_cache_2099_ = lean_ctor_get(v___x_2093_, 5);
v_recordedDeps_2100_ = lean_ctor_get(v___x_2093_, 6);
v_messages_2101_ = lean_ctor_get(v___x_2093_, 7);
v_infoState_2102_ = lean_ctor_get(v___x_2093_, 8);
v_snapshotTasks_2103_ = lean_ctor_get(v___x_2093_, 9);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2105_ = v___x_2093_;
v_isShared_2106_ = v_isSharedCheck_2133_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_snapshotTasks_2103_);
lean_inc(v_infoState_2102_);
lean_inc(v_messages_2101_);
lean_inc(v_recordedDeps_2100_);
lean_inc(v_cache_2099_);
lean_inc(v_traceState_2094_);
lean_inc(v_auxDeclNGen_2098_);
lean_inc(v_ngen_2097_);
lean_inc(v_nextMacroScope_2096_);
lean_inc(v_env_2095_);
lean_dec(v___x_2093_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2133_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
uint64_t v_tid_2107_; lean_object* v_traces_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2132_; 
v_tid_2107_ = lean_ctor_get_uint64(v_traceState_2094_, sizeof(void*)*1);
v_traces_2108_ = lean_ctor_get(v_traceState_2094_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_traceState_2094_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2110_ = v_traceState_2094_;
v_isShared_2111_ = v_isSharedCheck_2132_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_traces_2108_);
lean_dec(v_traceState_2094_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2132_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; double v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2112_ = lean_box(0);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0);
v___x_2115_ = 0;
v___x_2116_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1));
v___x_2117_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2117_, 0, v_cls_2080_);
lean_ctor_set(v___x_2117_, 1, v___x_2113_);
lean_ctor_set(v___x_2117_, 2, v___x_2116_);
lean_ctor_set_float(v___x_2117_, sizeof(void*)*3, v___x_2114_);
lean_ctor_set_float(v___x_2117_, sizeof(void*)*3 + 8, v___x_2114_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*3 + 16, v___x_2115_);
v___x_2118_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__2));
v___x_2119_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v_a_2089_);
lean_ctor_set(v___x_2119_, 2, v___x_2118_);
lean_inc(v_ref_2087_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_ref_2087_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = l_Lean_PersistentArray_push___redArg(v_traces_2108_, v___x_2120_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2121_);
v___x_2123_ = v___x_2110_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2121_);
lean_ctor_set_uint64(v_reuseFailAlloc_2131_, sizeof(void*)*1, v_tid_2107_);
v___x_2123_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 4, v___x_2123_);
v___x_2125_ = v___x_2105_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_env_2095_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_nextMacroScope_2096_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_ngen_2097_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_auxDeclNGen_2098_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2130_, 5, v_cache_2099_);
lean_ctor_set(v_reuseFailAlloc_2130_, 6, v_recordedDeps_2100_);
lean_ctor_set(v_reuseFailAlloc_2130_, 7, v_messages_2101_);
lean_ctor_set(v_reuseFailAlloc_2130_, 8, v_infoState_2102_);
lean_ctor_set(v_reuseFailAlloc_2130_, 9, v_snapshotTasks_2103_);
v___x_2125_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_st_ref_put(v___y_2085_, v___x_2125_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2112_);
v___x_2128_ = v___x_2091_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2112_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___boxed(lean_object* v_cls_2135_, lean_object* v_msg_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(v_cls_2135_, v_msg_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2142_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2145_; size_t v_sz_2146_; 
v___x_2145_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2146_ = lean_array_size(v___x_2145_);
return v_sz_2146_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg();
return v___x_2147_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__3(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__4(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
lean_ctor_set(v___x_2152_, 2, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__5(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2153_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__4, &l_Lean_Meta_saveEqnAffectingOptions___closed__4_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__4);
v___x_2154_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__3, &l_Lean_Meta_saveEqnAffectingOptions___closed__3_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__3);
v___x_2155_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2156_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
v___x_2157_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___x_2155_);
lean_ctor_set(v___x_2157_, 2, v___x_2154_);
lean_ctor_set(v___x_2157_, 3, v___x_2155_);
lean_ctor_set(v___x_2157_, 4, v___x_2155_);
lean_ctor_set(v___x_2157_, 5, v___x_2155_);
lean_ctor_set(v___x_2157_, 6, v___x_2155_);
lean_ctor_set(v___x_2157_, 7, v___x_2153_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__9(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__8));
v___x_2165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2166_ = l_Lean_Name_append(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__11(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__10));
v___x_2169_ = l_Lean_stringToMessageData(v___x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; size_t v_sz_2180_; size_t v___x_2181_; lean_object* v___x_2182_; 
v___x_2176_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2173_);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2179_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2180_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2176_, v___x_2179_, v_sz_2180_, v___x_2181_, v___x_2178_);
lean_dec_ref(v___x_2176_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2246_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2246_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2246_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; uint8_t v___x_2188_; lean_object* v___y_2190_; lean_object* v___y_2191_; 
v___x_2187_ = lean_array_get_size(v_a_2183_);
v___x_2188_ = lean_nat_dec_eq(v___x_2187_, v___x_2177_);
if (v___x_2188_ == 0)
{
lean_object* v_toCold_2233_; lean_object* v_options_2234_; uint8_t v_hasTrace_2235_; 
v_toCold_2233_ = lean_ctor_get(v_a_2173_, 0);
v_options_2234_ = lean_ctor_get(v_toCold_2233_, 2);
v_hasTrace_2235_ = lean_ctor_get_uint8(v_options_2234_, sizeof(void*)*1);
if (v_hasTrace_2235_ == 0)
{
v___y_2190_ = v_a_2172_;
v___y_2191_ = v_a_2174_;
goto v___jp_2189_;
}
else
{
lean_object* v_inheritedTraceOptions_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_inheritedTraceOptions_2236_ = lean_ctor_get(v_toCold_2233_, 11);
v___x_2237_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__8));
v___x_2238_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__9, &l_Lean_Meta_saveEqnAffectingOptions___closed__9_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__9);
v___x_2239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2236_, v_options_2234_, v___x_2238_);
if (v___x_2239_ == 0)
{
v___y_2190_ = v_a_2172_;
v___y_2191_ = v_a_2174_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2240_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__11, &l_Lean_Meta_saveEqnAffectingOptions___closed__11_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__11);
lean_inc(v_declName_2170_);
v___x_2241_ = l_Lean_MessageData_ofName(v_declName_2170_);
v___x_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(v___x_2237_, v___x_2242_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_dec_ref_known(v___x_2243_, 1);
v___y_2190_ = v_a_2172_;
v___y_2191_ = v_a_2174_;
goto v___jp_2189_;
}
else
{
lean_del_object(v___x_2185_);
lean_dec(v_a_2183_);
lean_dec(v_declName_2170_);
return v___x_2243_;
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_del_object(v___x_2185_);
lean_dec(v_a_2183_);
lean_dec(v_declName_2170_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
v___jp_2189_:
{
lean_object* v___x_2192_; lean_object* v_env_2193_; lean_object* v_nextMacroScope_2194_; lean_object* v_ngen_2195_; lean_object* v_auxDeclNGen_2196_; lean_object* v_traceState_2197_; lean_object* v_recordedDeps_2198_; lean_object* v_messages_2199_; lean_object* v_infoState_2200_; lean_object* v_snapshotTasks_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2231_; 
v___x_2192_ = lean_st_ref_take(v___y_2191_);
v_env_2193_ = lean_ctor_get(v___x_2192_, 0);
v_nextMacroScope_2194_ = lean_ctor_get(v___x_2192_, 1);
v_ngen_2195_ = lean_ctor_get(v___x_2192_, 2);
v_auxDeclNGen_2196_ = lean_ctor_get(v___x_2192_, 3);
v_traceState_2197_ = lean_ctor_get(v___x_2192_, 4);
v_recordedDeps_2198_ = lean_ctor_get(v___x_2192_, 6);
v_messages_2199_ = lean_ctor_get(v___x_2192_, 7);
v_infoState_2200_ = lean_ctor_get(v___x_2192_, 8);
v_snapshotTasks_2201_ = lean_ctor_get(v___x_2192_, 9);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v___x_2192_, 5);
lean_dec(v_unused_2232_);
v___x_2203_ = v___x_2192_;
v_isShared_2204_ = v_isSharedCheck_2231_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_snapshotTasks_2201_);
lean_inc(v_infoState_2200_);
lean_inc(v_messages_2199_);
lean_inc(v_recordedDeps_2198_);
lean_inc(v_traceState_2197_);
lean_inc(v_auxDeclNGen_2196_);
lean_inc(v_ngen_2195_);
lean_inc(v_nextMacroScope_2194_);
lean_inc(v_env_2193_);
lean_dec(v___x_2192_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2231_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2205_ = l_Lean_Meta_eqnOptionsExt;
v___x_2206_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2205_, v_env_2193_, v_declName_2170_, v_a_2183_, v___x_2188_);
v___x_2207_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 5, v___x_2207_);
lean_ctor_set(v___x_2203_, 0, v___x_2206_);
v___x_2209_ = v___x_2203_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_nextMacroScope_2194_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_ngen_2195_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_auxDeclNGen_2196_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_traceState_2197_);
lean_ctor_set(v_reuseFailAlloc_2230_, 5, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2230_, 6, v_recordedDeps_2198_);
lean_ctor_set(v_reuseFailAlloc_2230_, 7, v_messages_2199_);
lean_ctor_set(v_reuseFailAlloc_2230_, 8, v_infoState_2200_);
lean_ctor_set(v_reuseFailAlloc_2230_, 9, v_snapshotTasks_2201_);
v___x_2209_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_mctx_2212_; lean_object* v_zetaDeltaFVarIds_2213_; lean_object* v_postponed_2214_; lean_object* v_diag_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2228_; 
v___x_2210_ = lean_st_ref_put(v___y_2191_, v___x_2209_);
v___x_2211_ = lean_st_ref_take(v___y_2190_);
v_mctx_2212_ = lean_ctor_get(v___x_2211_, 0);
v_zetaDeltaFVarIds_2213_ = lean_ctor_get(v___x_2211_, 2);
v_postponed_2214_ = lean_ctor_get(v___x_2211_, 3);
v_diag_2215_ = lean_ctor_get(v___x_2211_, 4);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2211_, 1);
lean_dec(v_unused_2229_);
v___x_2217_ = v___x_2211_;
v_isShared_2218_ = v_isSharedCheck_2228_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_diag_2215_);
lean_inc(v_postponed_2214_);
lean_inc(v_zetaDeltaFVarIds_2213_);
lean_inc(v_mctx_2212_);
lean_dec(v___x_2211_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2228_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__5, &l_Lean_Meta_saveEqnAffectingOptions___closed__5_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__5);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2220_);
v___x_2222_ = v___x_2217_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_mctx_2212_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_zetaDeltaFVarIds_2213_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_postponed_2214_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_diag_2215_);
v___x_2222_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_st_ref_put(v___y_2190_, v___x_2222_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2219_);
v___x_2225_ = v___x_2185_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2219_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
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
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_declName_2170_);
v_a_2247_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2182_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2182_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2262_, lean_object* v_as_2263_, size_t v_sz_2264_, size_t v_i_2265_, lean_object* v_b_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2262_, v_as_2263_, v_sz_2264_, v_i_2265_, v_b_2266_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2273_, lean_object* v_as_2274_, lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
size_t v_sz_boxed_2283_; size_t v_i_boxed_2284_; lean_object* v_res_2285_; 
v_sz_boxed_2283_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2284_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_res_2285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2273_, v_as_2274_, v_sz_boxed_2283_, v_i_boxed_2284_, v_b_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_as_2274_);
lean_dec_ref(v___x_2273_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_00_u03b2_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg(){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg___boxed(lean_object* v___dummy_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg();
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_00_u03b2_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_st_mk_ref(v___x_2295_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2300_){
_start:
{
uint8_t v___x_2302_; 
v___x_2302_ = l_Lean_initializing();
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec_ref(v_f_2300_);
v___x_2303_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2305_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2306_ = lean_st_ref_take(v___x_2305_);
v___x_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_f_2300_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_st_ref_put(v___x_2305_, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2316_, lean_object* v_as_x27_2317_, lean_object* v_b_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
if (lean_obj_tag(v_as_x27_2317_) == 0)
{
lean_object* v___x_2324_; 
lean_dec(v_declName_2316_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_b_2318_);
return v___x_2324_;
}
else
{
lean_object* v_head_2325_; lean_object* v_tail_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v_b_2318_);
v_head_2325_ = lean_ctor_get(v_as_x27_2317_, 0);
v_tail_2326_ = lean_ctor_get(v_as_x27_2317_, 1);
v___x_2327_ = lean_box(0);
v___x_2328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2325_);
lean_inc(v___y_2322_);
lean_inc_ref(v___y_2321_);
lean_inc(v___y_2320_);
lean_inc_ref(v___y_2319_);
lean_inc(v_declName_2316_);
v___x_2329_ = lean_apply_6(v_head_2325_, v_declName_2316_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, lean_box(0));
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2340_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2340_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2340_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
if (lean_obj_tag(v_a_2330_) == 1)
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_dec(v_declName_2316_);
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_a_2330_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v___x_2327_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
else
{
lean_del_object(v___x_2332_);
lean_dec(v_a_2330_);
v_as_x27_2317_ = v_tail_2326_;
v_b_2318_ = v___x_2328_;
goto _start;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_declName_2316_);
v_a_2341_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2329_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2329_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2349_, lean_object* v_as_x27_2350_, lean_object* v_b_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2349_, v_as_x27_2350_, v_b_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_as_x27_2350_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2358_, lean_object* v_declName_2359_, uint8_t v_nonRec_2360_, lean_object* v___x_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2370_; lean_object* v_env_2371_; uint8_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2370_ = lean_st_ref_get(v___y_2365_);
v_env_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc_ref(v_env_2371_);
lean_dec(v___x_2370_);
v___x_2372_ = 1;
lean_inc(v___x_2358_);
v___x_2373_ = l_Lean_Environment_contains(v_env_2371_, v___x_2358_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_dec(v___x_2358_);
lean_inc(v_declName_2359_);
v___x_2374_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2359_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; uint8_t v___x_2376_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = lean_unbox(v_a_2375_);
lean_dec(v_a_2375_);
if (v___x_2376_ == 0)
{
lean_dec_ref(v___x_2361_);
lean_dec(v_declName_2359_);
goto v___jp_2367_;
}
else
{
lean_object* v___x_2377_; 
lean_inc(v_declName_2359_);
v___x_2377_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2359_, v___y_2365_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; uint8_t v___x_2379_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2379_ = lean_unbox(v_a_2378_);
lean_dec(v_a_2378_);
if (v___x_2379_ == 0)
{
if (v_nonRec_2360_ == 0)
{
lean_dec_ref(v___x_2361_);
lean_dec(v_declName_2359_);
goto v___jp_2367_;
}
else
{
lean_object* v___x_2380_; lean_object* v_env_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2380_ = lean_st_ref_get(v___y_2365_);
v_env_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc_ref(v_env_2381_);
lean_dec(v___x_2380_);
lean_inc(v_declName_2359_);
v___x_2382_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2381_, v_declName_2359_, v___x_2361_);
v___x_2383_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2359_, v___x_2382_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2383_;
}
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec_ref(v___x_2361_);
v___x_2384_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2385_ = lean_st_ref_get(v___x_2384_);
v___x_2386_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2387_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2359_, v___x_2385_, v___x_2386_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___x_2385_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2397_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2397_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2397_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_fst_2392_; 
v_fst_2392_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_fst_2392_);
lean_dec(v_a_2388_);
if (lean_obj_tag(v_fst_2392_) == 0)
{
lean_del_object(v___x_2390_);
goto v___jp_2367_;
}
else
{
lean_object* v_val_2393_; lean_object* v___x_2395_; 
v_val_2393_ = lean_ctor_get(v_fst_2392_, 0);
lean_inc(v_val_2393_);
lean_dec_ref_known(v_fst_2392_, 1);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v_val_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_val_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v_a_2398_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2387_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2387_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v___x_2361_);
lean_dec(v_declName_2359_);
v_a_2406_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2377_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2377_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v___x_2361_);
lean_dec(v_declName_2359_);
v_a_2414_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2374_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2374_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref(v___x_2361_);
lean_dec(v_declName_2359_);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2358_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
v___jp_2367_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2424_, lean_object* v_declName_2425_, lean_object* v_nonRec_2426_, lean_object* v___x_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v_nonRec_boxed_2433_; lean_object* v_res_2434_; 
v_nonRec_boxed_2433_ = lean_unbox(v_nonRec_2426_);
v_res_2434_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2424_, v_declName_2425_, v_nonRec_boxed_2433_, v___x_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_ref_2441_; lean_object* v___x_2442_; lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_ref_2441_ = lean_ctor_get(v___y_2438_, 2);
v___x_2442_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msg_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_inc(v_ref_2441_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_ref_2441_);
lean_ctor_set(v___x_2447_, 1, v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 1);
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2459_, uint8_t v_isExporting_2460_, lean_object* v___x_2461_, lean_object* v___y_2462_, lean_object* v___x_2463_, lean_object* v_a_x3f_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v_env_2467_; lean_object* v_nextMacroScope_2468_; lean_object* v_ngen_2469_; lean_object* v_auxDeclNGen_2470_; lean_object* v_traceState_2471_; lean_object* v_recordedDeps_2472_; lean_object* v_messages_2473_; lean_object* v_infoState_2474_; lean_object* v_snapshotTasks_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2500_; 
v___x_2466_ = lean_st_ref_take(v___y_2459_);
v_env_2467_ = lean_ctor_get(v___x_2466_, 0);
v_nextMacroScope_2468_ = lean_ctor_get(v___x_2466_, 1);
v_ngen_2469_ = lean_ctor_get(v___x_2466_, 2);
v_auxDeclNGen_2470_ = lean_ctor_get(v___x_2466_, 3);
v_traceState_2471_ = lean_ctor_get(v___x_2466_, 4);
v_recordedDeps_2472_ = lean_ctor_get(v___x_2466_, 6);
v_messages_2473_ = lean_ctor_get(v___x_2466_, 7);
v_infoState_2474_ = lean_ctor_get(v___x_2466_, 8);
v_snapshotTasks_2475_ = lean_ctor_get(v___x_2466_, 9);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v___x_2466_, 5);
lean_dec(v_unused_2501_);
v___x_2477_ = v___x_2466_;
v_isShared_2478_ = v_isSharedCheck_2500_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_snapshotTasks_2475_);
lean_inc(v_infoState_2474_);
lean_inc(v_messages_2473_);
lean_inc(v_recordedDeps_2472_);
lean_inc(v_traceState_2471_);
lean_inc(v_auxDeclNGen_2470_);
lean_inc(v_ngen_2469_);
lean_inc(v_nextMacroScope_2468_);
lean_inc(v_env_2467_);
lean_dec(v___x_2466_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2500_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = l_Lean_Environment_setExporting(v_env_2467_, v_isExporting_2460_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 5, v___x_2461_);
lean_ctor_set(v___x_2477_, 0, v___x_2479_);
v___x_2481_ = v___x_2477_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2479_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_nextMacroScope_2468_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_ngen_2469_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_auxDeclNGen_2470_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v_traceState_2471_);
lean_ctor_set(v_reuseFailAlloc_2499_, 5, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2499_, 6, v_recordedDeps_2472_);
lean_ctor_set(v_reuseFailAlloc_2499_, 7, v_messages_2473_);
lean_ctor_set(v_reuseFailAlloc_2499_, 8, v_infoState_2474_);
lean_ctor_set(v_reuseFailAlloc_2499_, 9, v_snapshotTasks_2475_);
v___x_2481_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_mctx_2484_; lean_object* v_zetaDeltaFVarIds_2485_; lean_object* v_postponed_2486_; lean_object* v_diag_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2497_; 
v___x_2482_ = lean_st_ref_put(v___y_2459_, v___x_2481_);
v___x_2483_ = lean_st_ref_take(v___y_2462_);
v_mctx_2484_ = lean_ctor_get(v___x_2483_, 0);
v_zetaDeltaFVarIds_2485_ = lean_ctor_get(v___x_2483_, 2);
v_postponed_2486_ = lean_ctor_get(v___x_2483_, 3);
v_diag_2487_ = lean_ctor_get(v___x_2483_, 4);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2483_, 1);
lean_dec(v_unused_2498_);
v___x_2489_ = v___x_2483_;
v_isShared_2490_ = v_isSharedCheck_2497_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_diag_2487_);
lean_inc(v_postponed_2486_);
lean_inc(v_zetaDeltaFVarIds_2485_);
lean_inc(v_mctx_2484_);
lean_dec(v___x_2483_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2497_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = lean_box(0);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v___x_2463_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_mctx_2484_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_zetaDeltaFVarIds_2485_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_postponed_2486_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_diag_2487_);
v___x_2493_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_st_ref_put(v___y_2462_, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2491_);
return v___x_2495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2502_, lean_object* v_isExporting_2503_, lean_object* v___x_2504_, lean_object* v___y_2505_, lean_object* v___x_2506_, lean_object* v_a_x3f_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v_isExporting_boxed_2509_; lean_object* v_res_2510_; 
v_isExporting_boxed_2509_ = lean_unbox(v_isExporting_2503_);
v_res_2510_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2502_, v_isExporting_boxed_2509_, v___x_2504_, v___y_2505_, v___x_2506_, v_a_x3f_2507_);
lean_dec(v_a_x3f_2507_);
lean_dec(v___y_2505_);
lean_dec(v___y_2502_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2511_, uint8_t v_isExporting_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v_env_2519_; lean_object* v___x_2520_; uint8_t v_isModule_2521_; 
v___x_2518_ = lean_st_ref_get(v___y_2516_);
v_env_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_env_2519_);
lean_dec(v___x_2518_);
v___x_2520_ = l_Lean_Environment_header(v_env_2519_);
v_isModule_2521_ = lean_ctor_get_uint8(v___x_2520_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2520_);
if (v_isModule_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v_env_2519_);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
v___x_2522_ = lean_apply_5(v_x_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
return v___x_2522_;
}
else
{
uint8_t v_isExporting_2523_; 
v_isExporting_2523_ = lean_ctor_get_uint8(v_env_2519_, sizeof(void*)*13);
lean_dec_ref(v_env_2519_);
if (v_isExporting_2512_ == 0)
{
if (v_isExporting_2523_ == 0)
{
lean_object* v___x_2590_; 
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
v___x_2590_ = lean_apply_5(v_x_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
return v___x_2590_;
}
else
{
goto v___jp_2524_;
}
}
else
{
if (v_isExporting_2523_ == 0)
{
goto v___jp_2524_;
}
else
{
lean_object* v___x_2591_; 
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
v___x_2591_ = lean_apply_5(v_x_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
return v___x_2591_;
}
}
v___jp_2524_:
{
lean_object* v___x_2525_; lean_object* v_env_2526_; lean_object* v_nextMacroScope_2527_; lean_object* v_ngen_2528_; lean_object* v_auxDeclNGen_2529_; lean_object* v_traceState_2530_; lean_object* v_recordedDeps_2531_; lean_object* v_messages_2532_; lean_object* v_infoState_2533_; lean_object* v_snapshotTasks_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2588_; 
v___x_2525_ = lean_st_ref_take(v___y_2516_);
v_env_2526_ = lean_ctor_get(v___x_2525_, 0);
v_nextMacroScope_2527_ = lean_ctor_get(v___x_2525_, 1);
v_ngen_2528_ = lean_ctor_get(v___x_2525_, 2);
v_auxDeclNGen_2529_ = lean_ctor_get(v___x_2525_, 3);
v_traceState_2530_ = lean_ctor_get(v___x_2525_, 4);
v_recordedDeps_2531_ = lean_ctor_get(v___x_2525_, 6);
v_messages_2532_ = lean_ctor_get(v___x_2525_, 7);
v_infoState_2533_ = lean_ctor_get(v___x_2525_, 8);
v_snapshotTasks_2534_ = lean_ctor_get(v___x_2525_, 9);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2525_, 5);
lean_dec(v_unused_2589_);
v___x_2536_ = v___x_2525_;
v_isShared_2537_ = v_isSharedCheck_2588_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_snapshotTasks_2534_);
lean_inc(v_infoState_2533_);
lean_inc(v_messages_2532_);
lean_inc(v_recordedDeps_2531_);
lean_inc(v_traceState_2530_);
lean_inc(v_auxDeclNGen_2529_);
lean_inc(v_ngen_2528_);
lean_inc(v_nextMacroScope_2527_);
lean_inc(v_env_2526_);
lean_dec(v___x_2525_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2588_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2538_ = l_Lean_Environment_setExporting(v_env_2526_, v_isExporting_2512_);
v___x_2539_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 5, v___x_2539_);
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2541_ = v___x_2536_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_nextMacroScope_2527_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_ngen_2528_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_auxDeclNGen_2529_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_traceState_2530_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_recordedDeps_2531_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v_messages_2532_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v_infoState_2533_);
lean_ctor_set(v_reuseFailAlloc_2587_, 9, v_snapshotTasks_2534_);
v___x_2541_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_mctx_2544_; lean_object* v_zetaDeltaFVarIds_2545_; lean_object* v_postponed_2546_; lean_object* v_diag_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2585_; 
v___x_2542_ = lean_st_ref_put(v___y_2516_, v___x_2541_);
v___x_2543_ = lean_st_ref_take(v___y_2514_);
v_mctx_2544_ = lean_ctor_get(v___x_2543_, 0);
v_zetaDeltaFVarIds_2545_ = lean_ctor_get(v___x_2543_, 2);
v_postponed_2546_ = lean_ctor_get(v___x_2543_, 3);
v_diag_2547_ = lean_ctor_get(v___x_2543_, 4);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2543_, 1);
lean_dec(v_unused_2586_);
v___x_2549_ = v___x_2543_;
v_isShared_2550_ = v_isSharedCheck_2585_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_diag_2547_);
lean_inc(v_postponed_2546_);
lean_inc(v_zetaDeltaFVarIds_2545_);
lean_inc(v_mctx_2544_);
lean_dec(v___x_2543_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2585_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__5, &l_Lean_Meta_saveEqnAffectingOptions___closed__5_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__5);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 1, v___x_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_mctx_2544_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_zetaDeltaFVarIds_2545_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_postponed_2546_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_diag_2547_);
v___x_2553_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v_r_2555_; 
v___x_2554_ = lean_st_ref_put(v___y_2514_, v___x_2553_);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
v_r_2555_ = lean_apply_5(v_x_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
if (lean_obj_tag(v_r_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2572_; 
v_a_2556_ = lean_ctor_get(v_r_2555_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2558_ = v_r_2555_;
v_isShared_2559_ = v_isSharedCheck_2572_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v_r_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2572_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
lean_inc(v_a_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 1);
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v___x_2562_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2516_, v_isExporting_2523_, v___x_2539_, v___y_2514_, v___x_2551_, v___x_2561_);
lean_dec_ref(v___x_2561_);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v___x_2562_, 0);
lean_dec(v_unused_2570_);
v___x_2564_ = v___x_2562_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_dec(v___x_2562_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v_a_2556_);
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2556_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2573_ = lean_ctor_get(v_r_2555_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v_r_2555_, 1);
v___x_2574_ = lean_box(0);
v___x_2575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2516_, v_isExporting_2523_, v___x_2539_, v___y_2514_, v___x_2551_, v___x_2574_);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2575_, 0);
lean_dec(v_unused_2583_);
v___x_2577_ = v___x_2575_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_dec(v___x_2575_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v_a_2573_);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2573_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2592_, lean_object* v_isExporting_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v_isExporting_boxed_2599_; lean_object* v_res_2600_; 
v_isExporting_boxed_2599_ = lean_unbox(v_isExporting_2593_);
v_res_2600_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2592_, v_isExporting_boxed_2599_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2601_, uint8_t v_when_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
if (v_when_2602_ == 0)
{
lean_object* v___x_2608_; 
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
v___x_2608_ = lean_apply_5(v_x_2601_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2608_;
}
else
{
uint8_t v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = 0;
v___x_2610_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2601_, v___x_2609_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2611_, lean_object* v_when_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v_when_boxed_2618_; lean_object* v_res_2619_; 
v_when_boxed_2618_ = lean_unbox(v_when_2612_);
v_res_2619_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2611_, v_when_boxed_2618_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2619_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2622_ = l_Lean_stringToMessageData(v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2627_ = l_Lean_stringToMessageData(v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2628_, uint8_t v_nonRec_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; lean_object* v_env_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___f_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; 
v___x_2635_ = lean_st_ref_get(v___y_2633_);
v_env_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc_ref(v_env_2636_);
lean_dec(v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2628_);
v___x_2638_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2636_, v_declName_2628_, v___x_2637_);
v___x_2639_ = lean_box(v_nonRec_2629_);
lean_inc(v___x_2638_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2640_, 0, v___x_2638_);
lean_closure_set(v___f_2640_, 1, v_declName_2628_);
lean_closure_set(v___f_2640_, 2, v___x_2639_);
lean_closure_set(v___f_2640_, 3, v___x_2637_);
v___x_2641_ = 1;
v___x_2642_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2640_, v___x_2641_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
if (lean_obj_tag(v_a_2643_) == 1)
{
lean_object* v_val_2644_; uint8_t v___x_2645_; 
v_val_2644_ = lean_ctor_get(v_a_2643_, 0);
v___x_2645_ = lean_name_eq(v_val_2644_, v___x_2638_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_inc(v_val_2644_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2646_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2647_ = l_Lean_MessageData_ofName(v_val_2644_);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2646_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2648_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = l_Lean_MessageData_ofName(v___x_2638_);
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2654_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_dec(v___x_2638_);
return v___x_2642_;
}
}
else
{
lean_dec(v___x_2638_);
return v___x_2642_;
}
}
else
{
lean_dec(v___x_2638_);
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2664_, lean_object* v_nonRec_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
uint8_t v_nonRec_boxed_2671_; lean_object* v_res_2672_; 
v_nonRec_boxed_2671_ = lean_unbox(v_nonRec_2665_);
v_res_2672_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2664_, v_nonRec_boxed_2671_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2673_, uint8_t v_nonRec_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___x_2680_; lean_object* v___f_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2680_ = lean_box(v_nonRec_2674_);
v___f_2681_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2681_, 0, v_declName_2673_);
lean_closure_set(v___f_2681_, 1, v___x_2680_);
v___x_2682_ = lean_unsigned_to_nat(32u);
v___x_2683_ = lean_mk_empty_array_with_capacity(v___x_2682_);
lean_dec_ref(v___x_2683_);
v___x_2684_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2686_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2684_, v___x_2685_, v___f_2681_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2687_, lean_object* v_nonRec_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
uint8_t v_nonRec_boxed_2694_; lean_object* v_res_2695_; 
v_nonRec_boxed_2694_ = lean_unbox(v_nonRec_2688_);
v_res_2695_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2687_, v_nonRec_boxed_2694_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2696_, lean_object* v_as_2697_, lean_object* v_as_x27_2698_, lean_object* v_b_2699_, lean_object* v_a_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2696_, v_as_x27_2698_, v_b_2699_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2707_, lean_object* v_as_2708_, lean_object* v_as_x27_2709_, lean_object* v_b_2710_, lean_object* v_a_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2707_, v_as_2708_, v_as_x27_2709_, v_b_2710_, v_a_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v_as_x27_2709_);
lean_dec(v_as_2708_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2718_, lean_object* v_x_2719_, uint8_t v_when_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2719_, v_when_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_x_2728_, lean_object* v_when_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
uint8_t v_when_boxed_2735_; lean_object* v_res_2736_; 
v_when_boxed_2735_ = lean_unbox(v_when_2729_);
v_res_2736_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2727_, v_x_2728_, v_when_boxed_2735_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2737_, lean_object* v_msg_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_msg_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2745_, v_msg_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2753_, lean_object* v_x_2754_, uint8_t v_isExporting_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2754_, v_isExporting_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_x_2763_, lean_object* v_isExporting_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
uint8_t v_isExporting_boxed_2770_; lean_object* v_res_2771_; 
v_isExporting_boxed_2770_ = lean_unbox(v_isExporting_2764_);
v_res_2771_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2762_, v_x_2763_, v_isExporting_boxed_2770_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2771_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_unsigned_to_nat(32u);
v___x_2773_ = lean_mk_empty_array_with_capacity(v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
return v___x_2774_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2775_ = ((size_t)5ULL);
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_unsigned_to_nat(32u);
v___x_2778_ = lean_mk_empty_array_with_capacity(v___x_2777_);
v___x_2779_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2780_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v___x_2778_);
lean_ctor_set(v___x_2780_, 2, v___x_2776_);
lean_ctor_set(v___x_2780_, 3, v___x_2776_);
lean_ctor_set_usize(v___x_2780_, 4, v___x_2775_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; lean_object* v_traceState_2784_; lean_object* v_traces_2785_; lean_object* v___x_2786_; lean_object* v_traceState_2787_; lean_object* v_env_2788_; lean_object* v_nextMacroScope_2789_; lean_object* v_ngen_2790_; lean_object* v_auxDeclNGen_2791_; lean_object* v_cache_2792_; lean_object* v_recordedDeps_2793_; lean_object* v_messages_2794_; lean_object* v_infoState_2795_; lean_object* v_snapshotTasks_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2815_; 
v___x_2783_ = lean_st_ref_get(v___y_2781_);
v_traceState_2784_ = lean_ctor_get(v___x_2783_, 4);
lean_inc_ref(v_traceState_2784_);
lean_dec(v___x_2783_);
v_traces_2785_ = lean_ctor_get(v_traceState_2784_, 0);
lean_inc_ref(v_traces_2785_);
lean_dec_ref(v_traceState_2784_);
v___x_2786_ = lean_st_ref_take(v___y_2781_);
v_traceState_2787_ = lean_ctor_get(v___x_2786_, 4);
v_env_2788_ = lean_ctor_get(v___x_2786_, 0);
v_nextMacroScope_2789_ = lean_ctor_get(v___x_2786_, 1);
v_ngen_2790_ = lean_ctor_get(v___x_2786_, 2);
v_auxDeclNGen_2791_ = lean_ctor_get(v___x_2786_, 3);
v_cache_2792_ = lean_ctor_get(v___x_2786_, 5);
v_recordedDeps_2793_ = lean_ctor_get(v___x_2786_, 6);
v_messages_2794_ = lean_ctor_get(v___x_2786_, 7);
v_infoState_2795_ = lean_ctor_get(v___x_2786_, 8);
v_snapshotTasks_2796_ = lean_ctor_get(v___x_2786_, 9);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2798_ = v___x_2786_;
v_isShared_2799_ = v_isSharedCheck_2815_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_snapshotTasks_2796_);
lean_inc(v_infoState_2795_);
lean_inc(v_messages_2794_);
lean_inc(v_recordedDeps_2793_);
lean_inc(v_cache_2792_);
lean_inc(v_traceState_2787_);
lean_inc(v_auxDeclNGen_2791_);
lean_inc(v_ngen_2790_);
lean_inc(v_nextMacroScope_2789_);
lean_inc(v_env_2788_);
lean_dec(v___x_2786_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2815_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
uint64_t v_tid_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2813_; 
v_tid_2800_ = lean_ctor_get_uint64(v_traceState_2787_, sizeof(void*)*1);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_traceState_2787_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; 
v_unused_2814_ = lean_ctor_get(v_traceState_2787_, 0);
lean_dec(v_unused_2814_);
v___x_2802_ = v_traceState_2787_;
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
else
{
lean_dec(v_traceState_2787_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2804_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2804_);
v___x_2806_ = v___x_2802_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2804_);
lean_ctor_set_uint64(v_reuseFailAlloc_2812_, sizeof(void*)*1, v_tid_2800_);
v___x_2806_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2808_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 4, v___x_2806_);
v___x_2808_ = v___x_2798_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_env_2788_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_nextMacroScope_2789_);
lean_ctor_set(v_reuseFailAlloc_2811_, 2, v_ngen_2790_);
lean_ctor_set(v_reuseFailAlloc_2811_, 3, v_auxDeclNGen_2791_);
lean_ctor_set(v_reuseFailAlloc_2811_, 4, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2811_, 5, v_cache_2792_);
lean_ctor_set(v_reuseFailAlloc_2811_, 6, v_recordedDeps_2793_);
lean_ctor_set(v_reuseFailAlloc_2811_, 7, v_messages_2794_);
lean_ctor_set(v_reuseFailAlloc_2811_, 8, v_infoState_2795_);
lean_ctor_set(v_reuseFailAlloc_2811_, 9, v_snapshotTasks_2796_);
v___x_2808_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_st_ref_put(v___y_2781_, v___x_2808_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_traces_2785_);
return v___x_2810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2816_);
lean_dec(v___y_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2831_ = 0;
v___x_2832_ = lean_box(v___x_2831_);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
return v_res_2838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2847_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2848_ = l_Lean_MessageData_ofName(v_name_2842_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2851_, lean_object* v_x_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2851_, v_x_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec_ref(v_x_2852_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2857_){
_start:
{
if (lean_obj_tag(v_x_2857_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
v_a_2859_ = lean_ctor_get(v_x_2857_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_x_2857_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v_x_2857_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v_x_2857_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
lean_ctor_set_tag(v___x_2861_, 1);
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_a_2867_ = lean_ctor_get(v_x_2857_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_x_2857_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v_x_2857_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v_x_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set_tag(v___x_2869_, 0);
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2875_);
return v_res_2877_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2878_){
_start:
{
if (lean_obj_tag(v_e_2878_) == 0)
{
uint8_t v___x_2879_; 
v___x_2879_ = 2;
return v___x_2879_;
}
else
{
lean_object* v_a_2880_; uint8_t v___x_2881_; 
v_a_2880_ = lean_ctor_get(v_e_2878_, 0);
v___x_2881_ = lean_unbox(v_a_2880_);
if (v___x_2881_ == 0)
{
uint8_t v___x_2882_; 
v___x_2882_ = 1;
return v___x_2882_;
}
else
{
uint8_t v___x_2883_; 
v___x_2883_ = 0;
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2884_){
_start:
{
uint8_t v_res_2885_; lean_object* v_r_2886_; 
v_res_2885_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2884_);
lean_dec_ref(v_e_2884_);
v_r_2886_ = lean_box(v_res_2885_);
return v_r_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2887_, size_t v_i_2888_, lean_object* v_bs_2889_){
_start:
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_usize_dec_lt(v_i_2888_, v_sz_2887_);
if (v___x_2890_ == 0)
{
return v_bs_2889_;
}
else
{
lean_object* v_v_2891_; lean_object* v_msg_2892_; lean_object* v___x_2893_; lean_object* v_bs_x27_2894_; size_t v___x_2895_; size_t v___x_2896_; lean_object* v___x_2897_; 
v_v_2891_ = lean_array_uget_borrowed(v_bs_2889_, v_i_2888_);
v_msg_2892_ = lean_ctor_get(v_v_2891_, 1);
lean_inc_ref(v_msg_2892_);
v___x_2893_ = lean_unsigned_to_nat(0u);
v_bs_x27_2894_ = lean_array_uset(v_bs_2889_, v_i_2888_, v___x_2893_);
v___x_2895_ = ((size_t)1ULL);
v___x_2896_ = lean_usize_add(v_i_2888_, v___x_2895_);
v___x_2897_ = lean_array_uset(v_bs_x27_2894_, v_i_2888_, v_msg_2892_);
v_i_2888_ = v___x_2896_;
v_bs_2889_ = v___x_2897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2899_, lean_object* v_i_2900_, lean_object* v_bs_2901_){
_start:
{
size_t v_sz_boxed_2902_; size_t v_i_boxed_2903_; lean_object* v_res_2904_; 
v_sz_boxed_2902_ = lean_unbox_usize(v_sz_2899_);
lean_dec(v_sz_2899_);
v_i_boxed_2903_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2902_, v_i_boxed_2903_, v_bs_2901_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2905_, lean_object* v_data_2906_, lean_object* v_ref_2907_, lean_object* v_msg_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_toCold_2912_; lean_object* v_currRecDepth_2913_; lean_object* v_ref_2914_; uint16_t v_optionFlags_2915_; uint8_t v_suppressElabErrors_2916_; uint8_t v_checkDeprecated_2917_; uint8_t v_isRecordingDeps_2918_; lean_object* v_ref_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v_traceState_2922_; lean_object* v_traces_2923_; lean_object* v___x_2924_; size_t v_sz_2925_; size_t v___x_2926_; lean_object* v___x_2927_; lean_object* v_msg_2928_; lean_object* v___x_2929_; lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2968_; 
v_toCold_2912_ = lean_ctor_get(v___y_2909_, 0);
v_currRecDepth_2913_ = lean_ctor_get(v___y_2909_, 1);
v_ref_2914_ = lean_ctor_get(v___y_2909_, 2);
v_optionFlags_2915_ = lean_ctor_get_uint16(v___y_2909_, sizeof(void*)*3);
v_suppressElabErrors_2916_ = lean_ctor_get_uint8(v___y_2909_, sizeof(void*)*3 + 2);
v_checkDeprecated_2917_ = lean_ctor_get_uint8(v___y_2909_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2918_ = lean_ctor_get_uint8(v___y_2909_, sizeof(void*)*3 + 4);
v_ref_2919_ = l_Lean_replaceRef(v_ref_2907_, v_ref_2914_);
lean_inc(v_currRecDepth_2913_);
lean_inc_ref(v_toCold_2912_);
v___x_2920_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2920_, 0, v_toCold_2912_);
lean_ctor_set(v___x_2920_, 1, v_currRecDepth_2913_);
lean_ctor_set(v___x_2920_, 2, v_ref_2919_);
lean_ctor_set_uint16(v___x_2920_, sizeof(void*)*3, v_optionFlags_2915_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 2, v_suppressElabErrors_2916_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 3, v_checkDeprecated_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 4, v_isRecordingDeps_2918_);
v___x_2921_ = lean_st_ref_get(v___y_2910_);
v_traceState_2922_ = lean_ctor_get(v___x_2921_, 4);
lean_inc_ref(v_traceState_2922_);
lean_dec(v___x_2921_);
v_traces_2923_ = lean_ctor_get(v_traceState_2922_, 0);
lean_inc_ref(v_traces_2923_);
lean_dec_ref(v_traceState_2922_);
v___x_2924_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2923_);
lean_dec_ref(v_traces_2923_);
v_sz_2925_ = lean_array_size(v___x_2924_);
v___x_2926_ = ((size_t)0ULL);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2925_, v___x_2926_, v___x_2924_);
v_msg_2928_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2928_, 0, v_data_2906_);
lean_ctor_set(v_msg_2928_, 1, v_msg_2908_);
lean_ctor_set(v_msg_2928_, 2, v___x_2927_);
v___x_2929_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2928_, v___x_2920_, v___y_2910_);
lean_dec_ref_known(v___x_2920_, 3);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2968_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2968_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v_traceState_2935_; lean_object* v_env_2936_; lean_object* v_nextMacroScope_2937_; lean_object* v_ngen_2938_; lean_object* v_auxDeclNGen_2939_; lean_object* v_cache_2940_; lean_object* v_recordedDeps_2941_; lean_object* v_messages_2942_; lean_object* v_infoState_2943_; lean_object* v_snapshotTasks_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2967_; 
v___x_2934_ = lean_st_ref_take(v___y_2910_);
v_traceState_2935_ = lean_ctor_get(v___x_2934_, 4);
v_env_2936_ = lean_ctor_get(v___x_2934_, 0);
v_nextMacroScope_2937_ = lean_ctor_get(v___x_2934_, 1);
v_ngen_2938_ = lean_ctor_get(v___x_2934_, 2);
v_auxDeclNGen_2939_ = lean_ctor_get(v___x_2934_, 3);
v_cache_2940_ = lean_ctor_get(v___x_2934_, 5);
v_recordedDeps_2941_ = lean_ctor_get(v___x_2934_, 6);
v_messages_2942_ = lean_ctor_get(v___x_2934_, 7);
v_infoState_2943_ = lean_ctor_get(v___x_2934_, 8);
v_snapshotTasks_2944_ = lean_ctor_get(v___x_2934_, 9);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2946_ = v___x_2934_;
v_isShared_2947_ = v_isSharedCheck_2967_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_snapshotTasks_2944_);
lean_inc(v_infoState_2943_);
lean_inc(v_messages_2942_);
lean_inc(v_recordedDeps_2941_);
lean_inc(v_cache_2940_);
lean_inc(v_traceState_2935_);
lean_inc(v_auxDeclNGen_2939_);
lean_inc(v_ngen_2938_);
lean_inc(v_nextMacroScope_2937_);
lean_inc(v_env_2936_);
lean_dec(v___x_2934_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2967_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint64_t v_tid_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2965_; 
v_tid_2948_ = lean_ctor_get_uint64(v_traceState_2935_, sizeof(void*)*1);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_traceState_2935_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; 
v_unused_2966_ = lean_ctor_get(v_traceState_2935_, 0);
lean_dec(v_unused_2966_);
v___x_2950_ = v_traceState_2935_;
v_isShared_2951_ = v_isSharedCheck_2965_;
goto v_resetjp_2949_;
}
else
{
lean_dec(v_traceState_2935_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2965_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_ref_2907_);
lean_ctor_set(v___x_2953_, 1, v_a_2930_);
v___x_2954_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2905_, v___x_2953_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2954_);
v___x_2956_ = v___x_2950_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2954_);
lean_ctor_set_uint64(v_reuseFailAlloc_2964_, sizeof(void*)*1, v_tid_2948_);
v___x_2956_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2958_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 4, v___x_2956_);
v___x_2958_ = v___x_2946_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_env_2936_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_nextMacroScope_2937_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_ngen_2938_);
lean_ctor_set(v_reuseFailAlloc_2963_, 3, v_auxDeclNGen_2939_);
lean_ctor_set(v_reuseFailAlloc_2963_, 4, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2963_, 5, v_cache_2940_);
lean_ctor_set(v_reuseFailAlloc_2963_, 6, v_recordedDeps_2941_);
lean_ctor_set(v_reuseFailAlloc_2963_, 7, v_messages_2942_);
lean_ctor_set(v_reuseFailAlloc_2963_, 8, v_infoState_2943_);
lean_ctor_set(v_reuseFailAlloc_2963_, 9, v_snapshotTasks_2944_);
v___x_2958_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = lean_st_ref_put(v___y_2910_, v___x_2958_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2952_);
v___x_2961_ = v___x_2932_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2952_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2969_, lean_object* v_data_2970_, lean_object* v_ref_2971_, lean_object* v_msg_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2969_, v_data_2970_, v_ref_2971_, v_msg_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
return v_res_2976_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2979_ = l_Lean_stringToMessageData(v___x_2978_);
return v___x_2979_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2980_; double v___x_2981_; 
v___x_2980_ = lean_unsigned_to_nat(1000u);
v___x_2981_ = lean_float_of_nat(v___x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2982_, uint8_t v_collapsed_2983_, lean_object* v_tag_2984_, lean_object* v_opts_2985_, uint8_t v_clsEnabled_2986_, lean_object* v_oldTraces_2987_, lean_object* v_msg_2988_, lean_object* v_resStartStop_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_fst_2993_; lean_object* v_snd_2994_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v_data_2998_; lean_object* v_fst_3009_; lean_object* v_snd_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; lean_object* v___y_3014_; lean_object* v_a_3015_; uint8_t v___y_3030_; double v___y_3062_; 
v_fst_2993_ = lean_ctor_get(v_resStartStop_2989_, 0);
lean_inc(v_fst_2993_);
v_snd_2994_ = lean_ctor_get(v_resStartStop_2989_, 1);
lean_inc(v_snd_2994_);
lean_dec_ref(v_resStartStop_2989_);
v_fst_3009_ = lean_ctor_get(v_snd_2994_, 0);
lean_inc(v_fst_3009_);
v_snd_3010_ = lean_ctor_get(v_snd_2994_, 1);
lean_inc(v_snd_3010_);
lean_dec(v_snd_2994_);
v___x_3011_ = l_Lean_trace_profiler;
v___x_3012_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2985_, v___x_3011_);
if (v___x_3012_ == 0)
{
v___y_3030_ = v___x_3012_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3067_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3068_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2985_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; double v___x_3071_; double v___x_3072_; double v___x_3073_; 
v___x_3069_ = l_Lean_trace_profiler_threshold;
v___x_3070_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2985_, v___x_3069_);
v___x_3071_ = lean_float_of_nat(v___x_3070_);
v___x_3072_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3073_ = lean_float_div(v___x_3071_, v___x_3072_);
v___y_3062_ = v___x_3073_;
goto v___jp_3061_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; double v___x_3076_; 
v___x_3074_ = l_Lean_trace_profiler_threshold;
v___x_3075_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2985_, v___x_3074_);
v___x_3076_ = lean_float_of_nat(v___x_3075_);
v___y_3062_ = v___x_3076_;
goto v___jp_3061_;
}
}
v___jp_2995_:
{
lean_object* v___x_2999_; 
lean_inc(v___y_2996_);
v___x_2999_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2987_, v_data_2998_, v___y_2996_, v___y_2997_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3000_; 
lean_dec_ref_known(v___x_2999_, 1);
v___x_3000_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2993_);
return v___x_3000_;
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v_fst_2993_);
v_a_3001_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2999_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2999_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
v___jp_3013_:
{
uint8_t v_result_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; double v___x_3019_; lean_object* v_data_3020_; 
v_result_3016_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2993_);
v___x_3017_ = lean_box(v_result_3016_);
v___x_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
v___x_3019_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0);
lean_inc_ref(v_tag_2984_);
lean_inc_ref(v___x_3018_);
lean_inc(v_cls_2982_);
v_data_3020_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3020_, 0, v_cls_2982_);
lean_ctor_set(v_data_3020_, 1, v___x_3018_);
lean_ctor_set(v_data_3020_, 2, v_tag_2984_);
lean_ctor_set_float(v_data_3020_, sizeof(void*)*3, v___x_3019_);
lean_ctor_set_float(v_data_3020_, sizeof(void*)*3 + 8, v___x_3019_);
lean_ctor_set_uint8(v_data_3020_, sizeof(void*)*3 + 16, v_collapsed_2983_);
if (v___x_3012_ == 0)
{
lean_dec_ref_known(v___x_3018_, 1);
lean_dec(v_snd_3010_);
lean_dec(v_fst_3009_);
lean_dec_ref(v_tag_2984_);
lean_dec(v_cls_2982_);
v___y_2996_ = v___y_3014_;
v___y_2997_ = v_a_3015_;
v_data_2998_ = v_data_3020_;
goto v___jp_2995_;
}
else
{
lean_object* v_data_3021_; double v___x_3022_; double v___x_3023_; 
lean_dec_ref_known(v_data_3020_, 3);
v_data_3021_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3021_, 0, v_cls_2982_);
lean_ctor_set(v_data_3021_, 1, v___x_3018_);
lean_ctor_set(v_data_3021_, 2, v_tag_2984_);
v___x_3022_ = lean_unbox_float(v_fst_3009_);
lean_dec(v_fst_3009_);
lean_ctor_set_float(v_data_3021_, sizeof(void*)*3, v___x_3022_);
v___x_3023_ = lean_unbox_float(v_snd_3010_);
lean_dec(v_snd_3010_);
lean_ctor_set_float(v_data_3021_, sizeof(void*)*3 + 8, v___x_3023_);
lean_ctor_set_uint8(v_data_3021_, sizeof(void*)*3 + 16, v_collapsed_2983_);
v___y_2996_ = v___y_3014_;
v___y_2997_ = v_a_3015_;
v_data_2998_ = v_data_3021_;
goto v___jp_2995_;
}
}
v___jp_3024_:
{
lean_object* v_ref_3025_; lean_object* v___x_3026_; 
v_ref_3025_ = lean_ctor_get(v___y_2990_, 2);
lean_inc(v___y_2991_);
lean_inc_ref(v___y_2990_);
lean_inc(v_fst_2993_);
v___x_3026_ = lean_apply_4(v_msg_2988_, v_fst_2993_, v___y_2990_, v___y_2991_, lean_box(0));
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___y_3014_ = v_ref_3025_;
v_a_3015_ = v_a_3027_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3028_; 
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_3014_ = v_ref_3025_;
v_a_3015_ = v___x_3028_;
goto v___jp_3013_;
}
}
v___jp_3029_:
{
if (v_clsEnabled_2986_ == 0)
{
if (v___y_3030_ == 0)
{
lean_object* v___x_3031_; lean_object* v_traceState_3032_; lean_object* v_env_3033_; lean_object* v_nextMacroScope_3034_; lean_object* v_ngen_3035_; lean_object* v_auxDeclNGen_3036_; lean_object* v_cache_3037_; lean_object* v_recordedDeps_3038_; lean_object* v_messages_3039_; lean_object* v_infoState_3040_; lean_object* v_snapshotTasks_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v_snd_3010_);
lean_dec(v_fst_3009_);
lean_dec_ref(v_msg_2988_);
lean_dec_ref(v_tag_2984_);
lean_dec(v_cls_2982_);
v___x_3031_ = lean_st_ref_take(v___y_2991_);
v_traceState_3032_ = lean_ctor_get(v___x_3031_, 4);
v_env_3033_ = lean_ctor_get(v___x_3031_, 0);
v_nextMacroScope_3034_ = lean_ctor_get(v___x_3031_, 1);
v_ngen_3035_ = lean_ctor_get(v___x_3031_, 2);
v_auxDeclNGen_3036_ = lean_ctor_get(v___x_3031_, 3);
v_cache_3037_ = lean_ctor_get(v___x_3031_, 5);
v_recordedDeps_3038_ = lean_ctor_get(v___x_3031_, 6);
v_messages_3039_ = lean_ctor_get(v___x_3031_, 7);
v_infoState_3040_ = lean_ctor_get(v___x_3031_, 8);
v_snapshotTasks_3041_ = lean_ctor_get(v___x_3031_, 9);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3043_ = v___x_3031_;
v_isShared_3044_ = v_isSharedCheck_3060_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_snapshotTasks_3041_);
lean_inc(v_infoState_3040_);
lean_inc(v_messages_3039_);
lean_inc(v_recordedDeps_3038_);
lean_inc(v_cache_3037_);
lean_inc(v_traceState_3032_);
lean_inc(v_auxDeclNGen_3036_);
lean_inc(v_ngen_3035_);
lean_inc(v_nextMacroScope_3034_);
lean_inc(v_env_3033_);
lean_dec(v___x_3031_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3060_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
uint64_t v_tid_3045_; lean_object* v_traces_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3059_; 
v_tid_3045_ = lean_ctor_get_uint64(v_traceState_3032_, sizeof(void*)*1);
v_traces_3046_ = lean_ctor_get(v_traceState_3032_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_traceState_3032_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3048_ = v_traceState_3032_;
v_isShared_3049_ = v_isSharedCheck_3059_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_traces_3046_);
lean_dec(v_traceState_3032_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3059_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3050_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2987_, v_traces_3046_);
lean_dec_ref(v_traces_3046_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v___x_3050_);
v___x_3052_ = v___x_3048_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3050_);
lean_ctor_set_uint64(v_reuseFailAlloc_3058_, sizeof(void*)*1, v_tid_3045_);
v___x_3052_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 4, v___x_3052_);
v___x_3054_ = v___x_3043_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_env_3033_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_nextMacroScope_3034_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v_ngen_3035_);
lean_ctor_set(v_reuseFailAlloc_3057_, 3, v_auxDeclNGen_3036_);
lean_ctor_set(v_reuseFailAlloc_3057_, 4, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3057_, 5, v_cache_3037_);
lean_ctor_set(v_reuseFailAlloc_3057_, 6, v_recordedDeps_3038_);
lean_ctor_set(v_reuseFailAlloc_3057_, 7, v_messages_3039_);
lean_ctor_set(v_reuseFailAlloc_3057_, 8, v_infoState_3040_);
lean_ctor_set(v_reuseFailAlloc_3057_, 9, v_snapshotTasks_3041_);
v___x_3054_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_st_ref_put(v___y_2991_, v___x_3054_);
v___x_3056_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2993_);
return v___x_3056_;
}
}
}
}
}
else
{
goto v___jp_3024_;
}
}
else
{
goto v___jp_3024_;
}
}
v___jp_3061_:
{
double v___x_3063_; double v___x_3064_; double v___x_3065_; uint8_t v___x_3066_; 
v___x_3063_ = lean_unbox_float(v_snd_3010_);
v___x_3064_ = lean_unbox_float(v_fst_3009_);
v___x_3065_ = lean_float_sub(v___x_3063_, v___x_3064_);
v___x_3066_ = lean_float_decLt(v___y_3062_, v___x_3065_);
v___y_3030_ = v___x_3066_;
goto v___jp_3029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3077_, lean_object* v_collapsed_3078_, lean_object* v_tag_3079_, lean_object* v_opts_3080_, lean_object* v_clsEnabled_3081_, lean_object* v_oldTraces_3082_, lean_object* v_msg_3083_, lean_object* v_resStartStop_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
uint8_t v_collapsed_boxed_3088_; uint8_t v_clsEnabled_boxed_3089_; lean_object* v_res_3090_; 
v_collapsed_boxed_3088_ = lean_unbox(v_collapsed_3078_);
v_clsEnabled_boxed_3089_ = lean_unbox(v_clsEnabled_3081_);
v_res_3090_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3077_, v_collapsed_boxed_3088_, v_tag_3079_, v_opts_3080_, v_clsEnabled_boxed_3089_, v_oldTraces_3082_, v_msg_3083_, v_resStartStop_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec_ref(v_opts_3080_);
return v_res_3090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
lean_ctor_set(v___x_3095_, 2, v___x_3094_);
lean_ctor_set(v___x_3095_, 3, v___x_3094_);
lean_ctor_set(v___x_3095_, 4, v___x_3093_);
lean_ctor_set(v___x_3095_, 5, v___x_3093_);
lean_ctor_set(v___x_3095_, 6, v___x_3093_);
lean_ctor_set(v___x_3095_, 7, v___x_3093_);
lean_ctor_set(v___x_3095_, 8, v___x_3093_);
lean_ctor_set(v___x_3095_, 9, v___x_3093_);
lean_ctor_set(v___x_3095_, 10, v___x_3093_);
return v___x_3095_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
return v___x_3097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
lean_ctor_set(v___x_3100_, 2, v___x_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3101_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3102_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3103_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3104_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
v___x_3105_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v___x_3103_);
lean_ctor_set(v___x_3105_, 2, v___x_3102_);
lean_ctor_set(v___x_3105_, 3, v___x_3103_);
lean_ctor_set(v___x_3105_, 4, v___x_3103_);
lean_ctor_set(v___x_3105_, 5, v___x_3103_);
lean_ctor_set(v___x_3105_, 6, v___x_3103_);
lean_ctor_set(v___x_3105_, 7, v___x_3101_);
return v___x_3105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
lean_ctor_set(v___x_3107_, 2, v___x_3106_);
lean_ctor_set(v___x_3107_, 3, v___x_3106_);
lean_ctor_set(v___x_3107_, 4, v___x_3106_);
return v___x_3107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3113_ = l_Lean_Name_append(v___x_3112_, v___x_3111_);
return v___x_3113_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3114_; double v___x_3115_; 
v___x_3114_ = lean_unsigned_to_nat(1000000000u);
v___x_3115_ = lean_float_of_nat(v___x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3116_, lean_object* v___f_3117_, lean_object* v_name_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_toCold_3122_; lean_object* v_options_3123_; uint8_t v_hasTrace_3124_; 
v_toCold_3122_ = lean_ctor_get(v___y_3119_, 0);
v_options_3123_ = lean_ctor_get(v_toCold_3122_, 2);
v_hasTrace_3124_ = lean_ctor_get_uint8(v_options_3123_, sizeof(void*)*1);
if (v_hasTrace_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v_env_3126_; lean_object* v___x_3127_; 
lean_dec_ref(v___f_3117_);
v___x_3125_ = lean_st_ref_get(v___y_3120_);
v_env_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc_ref(v_env_3126_);
lean_dec(v___x_3125_);
lean_inc(v_name_3118_);
v___x_3127_ = l_Lean_Meta_declFromEqLikeName(v_env_3126_, v_name_3118_);
if (lean_obj_tag(v___x_3127_) == 1)
{
lean_object* v_val_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3229_; 
v_val_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3229_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_val_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3229_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v_fst_3132_; lean_object* v_snd_3133_; lean_object* v___x_3134_; lean_object* v_env_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v_fst_3132_ = lean_ctor_get(v_val_3128_, 0);
lean_inc_n(v_fst_3132_, 2);
v_snd_3133_ = lean_ctor_get(v_val_3128_, 1);
lean_inc_n(v_snd_3133_, 2);
lean_dec(v_val_3128_);
v___x_3134_ = lean_st_ref_get(v___y_3120_);
v_env_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc_ref(v_env_3135_);
lean_dec(v___x_3134_);
v___x_3136_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3135_, v_fst_3132_, v_snd_3133_);
v___x_3137_ = lean_name_eq(v_name_3118_, v___x_3136_);
lean_dec(v___x_3136_);
lean_dec(v_name_3118_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3140_; 
lean_dec(v_snd_3133_);
lean_dec(v_fst_3132_);
lean_dec(v___x_3116_);
v___x_3138_ = lean_box(v_hasTrace_3124_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3138_);
v___x_3140_ = v___x_3130_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
else
{
uint8_t v___x_3142_; 
lean_inc(v_snd_3133_);
v___x_3142_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3133_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3144_ = lean_string_dec_eq(v_snd_3133_, v___x_3143_);
lean_dec(v_snd_3133_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
lean_dec(v_fst_3132_);
lean_dec(v___x_3116_);
v___x_3145_ = lean_box(v_hasTrace_3124_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3145_);
v___x_3147_ = v___x_3130_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
else
{
uint8_t v___x_3149_; uint8_t v___x_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; uint64_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_del_object(v___x_3130_);
v___x_3149_ = 1;
v___x_3150_ = 0;
v___x_3151_ = 2;
v___x_3152_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3152_, 0, v___x_3142_);
lean_ctor_set_uint8(v___x_3152_, 1, v___x_3142_);
lean_ctor_set_uint8(v___x_3152_, 2, v___x_3142_);
lean_ctor_set_uint8(v___x_3152_, 3, v___x_3142_);
lean_ctor_set_uint8(v___x_3152_, 4, v___x_3142_);
lean_ctor_set_uint8(v___x_3152_, 5, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 6, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 7, v___x_3142_);
lean_ctor_set_uint8(v___x_3152_, 8, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 9, v___x_3149_);
lean_ctor_set_uint8(v___x_3152_, 10, v___x_3150_);
lean_ctor_set_uint8(v___x_3152_, 11, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 12, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 13, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 14, v___x_3151_);
lean_ctor_set_uint8(v___x_3152_, 15, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 16, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 17, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 18, v___x_3144_);
lean_ctor_set_uint8(v___x_3152_, 19, v___x_3142_);
v___x_3153_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3152_);
v___x_3154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set_uint64(v___x_3154_, sizeof(void*)*1, v___x_3153_);
v___x_3155_ = lean_unsigned_to_nat(0u);
v___x_3156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3157_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3158_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3159_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3160_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3160_, 0, v___x_3154_);
lean_ctor_set(v___x_3160_, 1, v___x_3116_);
lean_ctor_set(v___x_3160_, 2, v___x_3157_);
lean_ctor_set(v___x_3160_, 3, v___x_3158_);
lean_ctor_set(v___x_3160_, 4, v___x_3159_);
lean_ctor_set(v___x_3160_, 5, v___x_3155_);
lean_ctor_set(v___x_3160_, 6, v___x_3159_);
lean_ctor_set_uint8(v___x_3160_, sizeof(void*)*7, v___x_3142_);
lean_ctor_set_uint8(v___x_3160_, sizeof(void*)*7 + 1, v___x_3142_);
lean_ctor_set_uint8(v___x_3160_, sizeof(void*)*7 + 2, v___x_3142_);
lean_ctor_set_uint8(v___x_3160_, sizeof(void*)*7 + 3, v___x_3137_);
v___x_3161_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3162_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3163_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3161_);
lean_ctor_set(v___x_3164_, 1, v___x_3162_);
lean_ctor_set(v___x_3164_, 2, v___x_3116_);
lean_ctor_set(v___x_3164_, 3, v___x_3156_);
lean_ctor_set(v___x_3164_, 4, v___x_3163_);
v___x_3165_ = lean_st_mk_ref(v___x_3164_);
v___x_3166_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3132_, v___x_3137_, v___x_3160_, v___x_3165_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3160_, 7);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3180_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_st_ref_get(v___x_3165_);
lean_dec(v___x_3165_);
lean_dec(v___x_3171_);
if (lean_obj_tag(v_a_3167_) == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3172_ = lean_box(v___x_3142_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3172_);
v___x_3174_ = v___x_3169_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
lean_dec_ref_known(v_a_3167_, 1);
v___x_3176_ = lean_box(v___x_3144_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3176_);
v___x_3178_ = v___x_3169_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v___x_3165_);
v_a_3181_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3166_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3166_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
else
{
uint8_t v___x_3189_; uint8_t v___x_3190_; uint8_t v___x_3191_; lean_object* v___x_3192_; uint64_t v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec(v_snd_3133_);
lean_del_object(v___x_3130_);
v___x_3189_ = 1;
v___x_3190_ = 0;
v___x_3191_ = 2;
v___x_3192_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3192_, 0, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3192_, 1, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3192_, 2, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3192_, 3, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3192_, 4, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3192_, 5, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 6, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 7, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3192_, 8, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 9, v___x_3189_);
lean_ctor_set_uint8(v___x_3192_, 10, v___x_3190_);
lean_ctor_set_uint8(v___x_3192_, 11, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 12, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 13, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 14, v___x_3191_);
lean_ctor_set_uint8(v___x_3192_, 15, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 16, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 17, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 18, v___x_3142_);
lean_ctor_set_uint8(v___x_3192_, 19, v_hasTrace_3124_);
v___x_3193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3192_);
v___x_3194_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set_uint64(v___x_3194_, sizeof(void*)*1, v___x_3193_);
v___x_3195_ = lean_unsigned_to_nat(0u);
v___x_3196_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3197_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3198_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3199_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3200_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3200_, 0, v___x_3194_);
lean_ctor_set(v___x_3200_, 1, v___x_3116_);
lean_ctor_set(v___x_3200_, 2, v___x_3197_);
lean_ctor_set(v___x_3200_, 3, v___x_3198_);
lean_ctor_set(v___x_3200_, 4, v___x_3199_);
lean_ctor_set(v___x_3200_, 5, v___x_3195_);
lean_ctor_set(v___x_3200_, 6, v___x_3199_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7 + 1, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7 + 2, v_hasTrace_3124_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7 + 3, v___x_3137_);
v___x_3201_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3202_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3203_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3201_);
lean_ctor_set(v___x_3204_, 1, v___x_3202_);
lean_ctor_set(v___x_3204_, 2, v___x_3116_);
lean_ctor_set(v___x_3204_, 3, v___x_3196_);
lean_ctor_set(v___x_3204_, 4, v___x_3203_);
v___x_3205_ = lean_st_mk_ref(v___x_3204_);
v___x_3206_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3132_, v___x_3200_, v___x_3205_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3200_, 7);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3220_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3220_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3220_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_st_ref_get(v___x_3205_);
lean_dec(v___x_3205_);
lean_dec(v___x_3211_);
if (lean_obj_tag(v_a_3207_) == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_box(v_hasTrace_3124_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3212_);
v___x_3214_ = v___x_3209_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3218_; 
lean_dec_ref_known(v_a_3207_, 1);
v___x_3216_ = lean_box(v___x_3142_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3216_);
v___x_3218_ = v___x_3209_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v___x_3205_);
v_a_3221_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3206_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3206_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec(v___x_3127_);
lean_dec(v_name_3118_);
lean_dec(v___x_3116_);
v___x_3230_ = lean_box(v_hasTrace_3124_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3232_; lean_object* v___f_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_a_3241_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v_a_3256_; lean_object* v___y_3259_; lean_object* v___y_3260_; uint8_t v_a_3261_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v_a_3267_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v_a_3279_; lean_object* v___y_3282_; lean_object* v___y_3283_; uint8_t v_a_3284_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; 
v_inheritedTraceOptions_3232_ = lean_ctor_get(v_toCold_3122_, 11);
lean_inc(v_name_3118_);
v___f_3233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3233_, 0, v_name_3118_);
v___x_3234_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3235_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1));
v___x_3236_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3232_, v_options_3123_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3418_ = l_Lean_trace_profiler;
v___x_3419_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3123_, v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v_env_3421_; lean_object* v___x_3422_; 
lean_dec_ref(v___f_3233_);
lean_dec_ref(v___f_3117_);
v___x_3420_ = lean_st_ref_get(v___y_3120_);
v_env_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc_ref(v_env_3421_);
lean_dec(v___x_3420_);
lean_inc(v_name_3118_);
v___x_3422_ = l_Lean_Meta_declFromEqLikeName(v_env_3421_, v_name_3118_);
if (lean_obj_tag(v___x_3422_) == 1)
{
lean_object* v_val_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3524_; 
v_val_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3524_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_val_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3524_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v___x_3429_; lean_object* v_env_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v_fst_3427_ = lean_ctor_get(v_val_3423_, 0);
lean_inc_n(v_fst_3427_, 2);
v_snd_3428_ = lean_ctor_get(v_val_3423_, 1);
lean_inc_n(v_snd_3428_, 2);
lean_dec(v_val_3423_);
v___x_3429_ = lean_st_ref_get(v___y_3120_);
v_env_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc_ref(v_env_3430_);
lean_dec(v___x_3429_);
v___x_3431_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3430_, v_fst_3427_, v_snd_3428_);
v___x_3432_ = lean_name_eq(v_name_3118_, v___x_3431_);
lean_dec(v___x_3431_);
lean_dec(v_name_3118_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v___x_3116_);
v___x_3433_ = lean_box(v___x_3419_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3433_);
v___x_3435_ = v___x_3425_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
else
{
uint8_t v___x_3437_; 
lean_inc(v_snd_3428_);
v___x_3437_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3428_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3438_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3439_ = lean_string_dec_eq(v_snd_3428_, v___x_3438_);
lean_dec(v_snd_3428_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_dec(v_fst_3427_);
lean_dec(v___x_3116_);
v___x_3440_ = lean_box(v___x_3419_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3440_);
v___x_3442_ = v___x_3425_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
else
{
uint8_t v___x_3444_; uint8_t v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; uint64_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_del_object(v___x_3425_);
v___x_3444_ = 1;
v___x_3445_ = 0;
v___x_3446_ = 2;
v___x_3447_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3447_, 0, v___x_3437_);
lean_ctor_set_uint8(v___x_3447_, 1, v___x_3437_);
lean_ctor_set_uint8(v___x_3447_, 2, v___x_3437_);
lean_ctor_set_uint8(v___x_3447_, 3, v___x_3437_);
lean_ctor_set_uint8(v___x_3447_, 4, v___x_3437_);
lean_ctor_set_uint8(v___x_3447_, 5, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 6, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 7, v___x_3437_);
lean_ctor_set_uint8(v___x_3447_, 8, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 9, v___x_3444_);
lean_ctor_set_uint8(v___x_3447_, 10, v___x_3445_);
lean_ctor_set_uint8(v___x_3447_, 11, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 12, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 13, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 14, v___x_3446_);
lean_ctor_set_uint8(v___x_3447_, 15, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 16, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 17, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 18, v___x_3439_);
lean_ctor_set_uint8(v___x_3447_, 19, v___x_3437_);
v___x_3448_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3447_);
v___x_3449_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3449_, 0, v___x_3447_);
lean_ctor_set_uint64(v___x_3449_, sizeof(void*)*1, v___x_3448_);
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3453_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3454_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3455_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3455_, 0, v___x_3449_);
lean_ctor_set(v___x_3455_, 1, v___x_3116_);
lean_ctor_set(v___x_3455_, 2, v___x_3452_);
lean_ctor_set(v___x_3455_, 3, v___x_3453_);
lean_ctor_set(v___x_3455_, 4, v___x_3454_);
lean_ctor_set(v___x_3455_, 5, v___x_3450_);
lean_ctor_set(v___x_3455_, 6, v___x_3454_);
lean_ctor_set_uint8(v___x_3455_, sizeof(void*)*7, v___x_3437_);
lean_ctor_set_uint8(v___x_3455_, sizeof(void*)*7 + 1, v___x_3437_);
lean_ctor_set_uint8(v___x_3455_, sizeof(void*)*7 + 2, v___x_3437_);
lean_ctor_set_uint8(v___x_3455_, sizeof(void*)*7 + 3, v_hasTrace_3124_);
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3457_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3458_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3456_);
lean_ctor_set(v___x_3459_, 1, v___x_3457_);
lean_ctor_set(v___x_3459_, 2, v___x_3116_);
lean_ctor_set(v___x_3459_, 3, v___x_3451_);
lean_ctor_set(v___x_3459_, 4, v___x_3458_);
v___x_3460_ = lean_st_mk_ref(v___x_3459_);
v___x_3461_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3427_, v_hasTrace_3124_, v___x_3455_, v___x_3460_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3455_, 7);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3475_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3475_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3475_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_st_ref_get(v___x_3460_);
lean_dec(v___x_3460_);
lean_dec(v___x_3466_);
if (lean_obj_tag(v_a_3462_) == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_box(v___x_3437_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3467_);
v___x_3469_ = v___x_3464_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
lean_dec_ref_known(v_a_3462_, 1);
v___x_3471_ = lean_box(v___x_3439_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3471_);
v___x_3473_ = v___x_3464_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v___x_3460_);
v_a_3476_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3461_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3461_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
else
{
uint8_t v___x_3484_; uint8_t v___x_3485_; uint8_t v___x_3486_; lean_object* v___x_3487_; uint64_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_dec(v_snd_3428_);
lean_del_object(v___x_3425_);
v___x_3484_ = 1;
v___x_3485_ = 0;
v___x_3486_ = 2;
v___x_3487_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3487_, 0, v___x_3419_);
lean_ctor_set_uint8(v___x_3487_, 1, v___x_3419_);
lean_ctor_set_uint8(v___x_3487_, 2, v___x_3419_);
lean_ctor_set_uint8(v___x_3487_, 3, v___x_3419_);
lean_ctor_set_uint8(v___x_3487_, 4, v___x_3419_);
lean_ctor_set_uint8(v___x_3487_, 5, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 6, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 7, v___x_3419_);
lean_ctor_set_uint8(v___x_3487_, 8, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 9, v___x_3484_);
lean_ctor_set_uint8(v___x_3487_, 10, v___x_3485_);
lean_ctor_set_uint8(v___x_3487_, 11, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 12, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 13, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 14, v___x_3486_);
lean_ctor_set_uint8(v___x_3487_, 15, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 16, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 17, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 18, v___x_3437_);
lean_ctor_set_uint8(v___x_3487_, 19, v___x_3419_);
v___x_3488_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3487_);
v___x_3489_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set_uint64(v___x_3489_, sizeof(void*)*1, v___x_3488_);
v___x_3490_ = lean_unsigned_to_nat(0u);
v___x_3491_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3492_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3493_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3494_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3495_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3495_, 0, v___x_3489_);
lean_ctor_set(v___x_3495_, 1, v___x_3116_);
lean_ctor_set(v___x_3495_, 2, v___x_3492_);
lean_ctor_set(v___x_3495_, 3, v___x_3493_);
lean_ctor_set(v___x_3495_, 4, v___x_3494_);
lean_ctor_set(v___x_3495_, 5, v___x_3490_);
lean_ctor_set(v___x_3495_, 6, v___x_3494_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*7, v___x_3419_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*7 + 1, v___x_3419_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*7 + 2, v___x_3419_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*7 + 3, v_hasTrace_3124_);
v___x_3496_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3497_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3496_);
lean_ctor_set(v___x_3499_, 1, v___x_3497_);
lean_ctor_set(v___x_3499_, 2, v___x_3116_);
lean_ctor_set(v___x_3499_, 3, v___x_3491_);
lean_ctor_set(v___x_3499_, 4, v___x_3498_);
v___x_3500_ = lean_st_mk_ref(v___x_3499_);
v___x_3501_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3427_, v___x_3495_, v___x_3500_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3495_, 7);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3515_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3515_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3515_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_st_ref_get(v___x_3500_);
lean_dec(v___x_3500_);
lean_dec(v___x_3506_);
if (lean_obj_tag(v_a_3502_) == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3509_; 
v___x_3507_ = lean_box(v___x_3419_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3507_);
v___x_3509_ = v___x_3504_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_dec_ref_known(v_a_3502_, 1);
v___x_3511_ = lean_box(v___x_3437_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3511_);
v___x_3513_ = v___x_3504_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec(v___x_3500_);
v_a_3516_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3501_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3501_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec(v___x_3422_);
lean_dec(v_name_3118_);
lean_dec(v___x_3116_);
v___x_3525_ = lean_box(v___x_3419_);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
return v___x_3526_;
}
}
else
{
goto v___jp_3294_;
}
}
else
{
goto v___jp_3294_;
}
v___jp_3238_:
{
lean_object* v___x_3242_; double v___x_3243_; double v___x_3244_; double v___x_3245_; double v___x_3246_; double v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3242_ = lean_io_mono_nanos_now();
v___x_3243_ = lean_float_of_nat(v___y_3240_);
v___x_3244_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3245_ = lean_float_div(v___x_3243_, v___x_3244_);
v___x_3246_ = lean_float_of_nat(v___x_3242_);
v___x_3247_ = lean_float_div(v___x_3246_, v___x_3244_);
v___x_3248_ = lean_box_float(v___x_3245_);
v___x_3249_ = lean_box_float(v___x_3247_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v_a_3241_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3234_, v_hasTrace_3124_, v___x_3235_, v_options_3123_, v___x_3237_, v___y_3239_, v___f_3233_, v___x_3251_, v___y_3119_, v___y_3120_);
return v___x_3252_;
}
v___jp_3253_:
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_a_3256_);
v___y_3239_ = v___y_3254_;
v___y_3240_ = v___y_3255_;
v_a_3241_ = v___x_3257_;
goto v___jp_3238_;
}
v___jp_3258_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = lean_box(v_a_3261_);
v___x_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
v___y_3239_ = v___y_3259_;
v___y_3240_ = v___y_3260_;
v_a_3241_ = v___x_3263_;
goto v___jp_3238_;
}
v___jp_3264_:
{
lean_object* v___x_3268_; double v___x_3269_; double v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3268_ = lean_io_get_num_heartbeats();
v___x_3269_ = lean_float_of_nat(v___y_3265_);
v___x_3270_ = lean_float_of_nat(v___x_3268_);
v___x_3271_ = lean_box_float(v___x_3269_);
v___x_3272_ = lean_box_float(v___x_3270_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3271_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v_a_3267_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3234_, v_hasTrace_3124_, v___x_3235_, v_options_3123_, v___x_3237_, v___y_3266_, v___f_3233_, v___x_3274_, v___y_3119_, v___y_3120_);
return v___x_3275_;
}
v___jp_3276_:
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_a_3279_);
v___y_3265_ = v___y_3277_;
v___y_3266_ = v___y_3278_;
v_a_3267_ = v___x_3280_;
goto v___jp_3264_;
}
v___jp_3281_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_box(v_a_3284_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
v___y_3265_ = v___y_3282_;
v___y_3266_ = v___y_3283_;
v_a_3267_ = v___x_3286_;
goto v___jp_3264_;
}
v___jp_3287_:
{
if (lean_obj_tag(v___y_3290_) == 0)
{
lean_object* v_a_3291_; uint8_t v___x_3292_; 
v_a_3291_ = lean_ctor_get(v___y_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___y_3290_, 1);
v___x_3292_ = lean_unbox(v_a_3291_);
lean_dec(v_a_3291_);
v___y_3282_ = v___y_3288_;
v___y_3283_ = v___y_3289_;
v_a_3284_ = v___x_3292_;
goto v___jp_3281_;
}
else
{
lean_object* v_a_3293_; 
v_a_3293_ = lean_ctor_get(v___y_3290_, 0);
lean_inc(v_a_3293_);
lean_dec_ref_known(v___y_3290_, 1);
v___y_3277_ = v___y_3288_;
v___y_3278_ = v___y_3289_;
v_a_3279_ = v_a_3293_;
goto v___jp_3276_;
}
}
v___jp_3294_:
{
lean_object* v___x_3295_; lean_object* v_a_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3295_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3120_);
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref(v___x_3295_);
v___x_3297_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3298_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3123_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v_env_3301_; lean_object* v___x_3302_; 
lean_dec_ref(v___f_3117_);
v___x_3299_ = lean_io_mono_nanos_now();
v___x_3300_ = lean_st_ref_get(v___y_3120_);
v_env_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_env_3301_);
lean_dec(v___x_3300_);
lean_inc(v_name_3118_);
v___x_3302_ = l_Lean_Meta_declFromEqLikeName(v_env_3301_, v_name_3118_);
if (lean_obj_tag(v___x_3302_) == 1)
{
lean_object* v_val_3303_; lean_object* v_fst_3304_; lean_object* v_snd_3305_; lean_object* v___x_3306_; lean_object* v_env_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v_val_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_val_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v_fst_3304_ = lean_ctor_get(v_val_3303_, 0);
lean_inc_n(v_fst_3304_, 2);
v_snd_3305_ = lean_ctor_get(v_val_3303_, 1);
lean_inc_n(v_snd_3305_, 2);
lean_dec(v_val_3303_);
v___x_3306_ = lean_st_ref_get(v___y_3120_);
v_env_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc_ref(v_env_3307_);
lean_dec(v___x_3306_);
v___x_3308_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3307_, v_fst_3304_, v_snd_3305_);
v___x_3309_ = lean_name_eq(v_name_3118_, v___x_3308_);
lean_dec(v___x_3308_);
lean_dec(v_name_3118_);
if (v___x_3309_ == 0)
{
lean_dec(v_snd_3305_);
lean_dec(v_fst_3304_);
lean_dec(v___x_3116_);
v___y_3259_ = v_a_3296_;
v___y_3260_ = v___x_3299_;
v_a_3261_ = v___x_3298_;
goto v___jp_3258_;
}
else
{
uint8_t v___x_3310_; 
lean_inc(v_snd_3305_);
v___x_3310_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3305_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3312_ = lean_string_dec_eq(v_snd_3305_, v___x_3311_);
lean_dec(v_snd_3305_);
if (v___x_3312_ == 0)
{
lean_dec(v_fst_3304_);
lean_dec(v___x_3116_);
v___y_3259_ = v_a_3296_;
v___y_3260_ = v___x_3299_;
v_a_3261_ = v___x_3298_;
goto v___jp_3258_;
}
else
{
uint8_t v___x_3313_; uint8_t v___x_3314_; uint8_t v___x_3315_; lean_object* v___x_3316_; uint64_t v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3313_ = 1;
v___x_3314_ = 0;
v___x_3315_ = 2;
v___x_3316_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3316_, 0, v___x_3310_);
lean_ctor_set_uint8(v___x_3316_, 1, v___x_3310_);
lean_ctor_set_uint8(v___x_3316_, 2, v___x_3310_);
lean_ctor_set_uint8(v___x_3316_, 3, v___x_3310_);
lean_ctor_set_uint8(v___x_3316_, 4, v___x_3310_);
lean_ctor_set_uint8(v___x_3316_, 5, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 6, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 7, v___x_3310_);
lean_ctor_set_uint8(v___x_3316_, 8, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 9, v___x_3313_);
lean_ctor_set_uint8(v___x_3316_, 10, v___x_3314_);
lean_ctor_set_uint8(v___x_3316_, 11, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 12, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 13, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 14, v___x_3315_);
lean_ctor_set_uint8(v___x_3316_, 15, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 16, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 17, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 18, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, 19, v___x_3310_);
v___x_3317_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3316_);
v___x_3318_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set_uint64(v___x_3318_, sizeof(void*)*1, v___x_3317_);
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3320_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3323_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3324_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3324_, 0, v___x_3318_);
lean_ctor_set(v___x_3324_, 1, v___x_3116_);
lean_ctor_set(v___x_3324_, 2, v___x_3321_);
lean_ctor_set(v___x_3324_, 3, v___x_3322_);
lean_ctor_set(v___x_3324_, 4, v___x_3323_);
lean_ctor_set(v___x_3324_, 5, v___x_3319_);
lean_ctor_set(v___x_3324_, 6, v___x_3323_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*7, v___x_3310_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*7 + 1, v___x_3310_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*7 + 2, v___x_3310_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*7 + 3, v_hasTrace_3124_);
v___x_3325_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3326_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3327_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3325_);
lean_ctor_set(v___x_3328_, 1, v___x_3326_);
lean_ctor_set(v___x_3328_, 2, v___x_3116_);
lean_ctor_set(v___x_3328_, 3, v___x_3320_);
lean_ctor_set(v___x_3328_, 4, v___x_3327_);
v___x_3329_ = lean_st_mk_ref(v___x_3328_);
v___x_3330_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3304_, v_hasTrace_3124_, v___x_3324_, v___x_3329_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3324_, 7);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3332_ = lean_st_ref_get(v___x_3329_);
lean_dec(v___x_3329_);
lean_dec(v___x_3332_);
if (lean_obj_tag(v_a_3331_) == 0)
{
v___y_3259_ = v_a_3296_;
v___y_3260_ = v___x_3299_;
v_a_3261_ = v___x_3310_;
goto v___jp_3258_;
}
else
{
lean_dec_ref_known(v_a_3331_, 1);
v___y_3259_ = v_a_3296_;
v___y_3260_ = v___x_3299_;
v_a_3261_ = v___x_3312_;
goto v___jp_3258_;
}
}
else
{
lean_object* v_a_3333_; 
lean_dec(v___x_3329_);
v_a_3333_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3330_, 1);
v___y_3254_ = v_a_3296_;
v___y_3255_ = v___x_3299_;
v_a_3256_ = v_a_3333_;
goto v___jp_3253_;
}
}
}
else
{
uint8_t v___x_3334_; uint8_t v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3337_; uint64_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec(v_snd_3305_);
v___x_3334_ = 1;
v___x_3335_ = 0;
v___x_3336_ = 2;
v___x_3337_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3337_, 0, v___x_3298_);
lean_ctor_set_uint8(v___x_3337_, 1, v___x_3298_);
lean_ctor_set_uint8(v___x_3337_, 2, v___x_3298_);
lean_ctor_set_uint8(v___x_3337_, 3, v___x_3298_);
lean_ctor_set_uint8(v___x_3337_, 4, v___x_3298_);
lean_ctor_set_uint8(v___x_3337_, 5, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 6, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 7, v___x_3298_);
lean_ctor_set_uint8(v___x_3337_, 8, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 9, v___x_3334_);
lean_ctor_set_uint8(v___x_3337_, 10, v___x_3335_);
lean_ctor_set_uint8(v___x_3337_, 11, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 12, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 13, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 14, v___x_3336_);
lean_ctor_set_uint8(v___x_3337_, 15, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 16, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 17, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 18, v___x_3310_);
lean_ctor_set_uint8(v___x_3337_, 19, v___x_3298_);
v___x_3338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3337_);
v___x_3339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set_uint64(v___x_3339_, sizeof(void*)*1, v___x_3338_);
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3342_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3343_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3344_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3345_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3345_, 0, v___x_3339_);
lean_ctor_set(v___x_3345_, 1, v___x_3116_);
lean_ctor_set(v___x_3345_, 2, v___x_3342_);
lean_ctor_set(v___x_3345_, 3, v___x_3343_);
lean_ctor_set(v___x_3345_, 4, v___x_3344_);
lean_ctor_set(v___x_3345_, 5, v___x_3340_);
lean_ctor_set(v___x_3345_, 6, v___x_3344_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7, v___x_3298_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7 + 1, v___x_3298_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7 + 2, v___x_3298_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7 + 3, v_hasTrace_3124_);
v___x_3346_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3347_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3348_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3346_);
lean_ctor_set(v___x_3349_, 1, v___x_3347_);
lean_ctor_set(v___x_3349_, 2, v___x_3116_);
lean_ctor_set(v___x_3349_, 3, v___x_3341_);
lean_ctor_set(v___x_3349_, 4, v___x_3348_);
v___x_3350_ = lean_st_mk_ref(v___x_3349_);
v___x_3351_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3304_, v___x_3345_, v___x_3350_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3345_, 7);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = lean_st_ref_get(v___x_3350_);
lean_dec(v___x_3350_);
lean_dec(v___x_3353_);
if (lean_obj_tag(v_a_3352_) == 0)
{
v___y_3259_ = v_a_3296_;
v___y_3260_ = v___x_3299_;
v_a_3261_ = v___x_3298_;
goto v___jp_3258_;
}
else
{
lean_dec_ref_known(v_a_3352_, 1);
v___y_3259_ = v_a_3296_;
v___y_3260_ = v___x_3299_;
v_a_3261_ = v___x_3310_;
goto v___jp_3258_;
}
}
else
{
lean_object* v_a_3354_; 
lean_dec(v___x_3350_);
v_a_3354_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3351_, 1);
v___y_3254_ = v_a_3296_;
v___y_3255_ = v___x_3299_;
v_a_3256_ = v_a_3354_;
goto v___jp_3253_;
}
}
}
}
else
{
lean_dec(v___x_3302_);
lean_dec(v_name_3118_);
lean_dec(v___x_3116_);
v___y_3259_ = v_a_3296_;
v___y_3260_ = v___x_3299_;
v_a_3261_ = v___x_3298_;
goto v___jp_3258_;
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_env_3357_; lean_object* v___x_3358_; 
v___x_3355_ = lean_io_get_num_heartbeats();
v___x_3356_ = lean_st_ref_get(v___y_3120_);
v_env_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc_ref(v_env_3357_);
lean_dec(v___x_3356_);
lean_inc(v_name_3118_);
v___x_3358_ = l_Lean_Meta_declFromEqLikeName(v_env_3357_, v_name_3118_);
if (lean_obj_tag(v___x_3358_) == 1)
{
lean_object* v_val_3359_; lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___x_3362_; lean_object* v_env_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_val_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v_fst_3360_ = lean_ctor_get(v_val_3359_, 0);
lean_inc_n(v_fst_3360_, 2);
v_snd_3361_ = lean_ctor_get(v_val_3359_, 1);
lean_inc_n(v_snd_3361_, 2);
lean_dec(v_val_3359_);
v___x_3362_ = lean_st_ref_get(v___y_3120_);
v_env_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc_ref(v_env_3363_);
lean_dec(v___x_3362_);
v___x_3364_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3363_, v_fst_3360_, v_snd_3361_);
v___x_3365_ = lean_name_eq(v_name_3118_, v___x_3364_);
lean_dec(v___x_3364_);
lean_dec(v_name_3118_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec(v_snd_3361_);
lean_dec(v_fst_3360_);
lean_dec(v___x_3116_);
v___x_3366_ = lean_box(0);
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3119_);
v___x_3367_ = lean_apply_4(v___f_3117_, v___x_3366_, v___y_3119_, v___y_3120_, lean_box(0));
v___y_3288_ = v___x_3355_;
v___y_3289_ = v_a_3296_;
v___y_3290_ = v___x_3367_;
goto v___jp_3287_;
}
else
{
uint8_t v___x_3368_; 
lean_inc(v_snd_3361_);
v___x_3368_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3361_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3369_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3370_ = lean_string_dec_eq(v_snd_3361_, v___x_3369_);
lean_dec(v_snd_3361_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec(v_fst_3360_);
lean_dec(v___x_3116_);
v___x_3371_ = lean_box(0);
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3119_);
v___x_3372_ = lean_apply_4(v___f_3117_, v___x_3371_, v___y_3119_, v___y_3120_, lean_box(0));
v___y_3288_ = v___x_3355_;
v___y_3289_ = v_a_3296_;
v___y_3290_ = v___x_3372_;
goto v___jp_3287_;
}
else
{
uint8_t v___x_3373_; uint8_t v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; uint64_t v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_dec_ref(v___f_3117_);
v___x_3373_ = 1;
v___x_3374_ = 0;
v___x_3375_ = 2;
v___x_3376_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3376_, 0, v___x_3368_);
lean_ctor_set_uint8(v___x_3376_, 1, v___x_3368_);
lean_ctor_set_uint8(v___x_3376_, 2, v___x_3368_);
lean_ctor_set_uint8(v___x_3376_, 3, v___x_3368_);
lean_ctor_set_uint8(v___x_3376_, 4, v___x_3368_);
lean_ctor_set_uint8(v___x_3376_, 5, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 6, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 7, v___x_3368_);
lean_ctor_set_uint8(v___x_3376_, 8, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 9, v___x_3373_);
lean_ctor_set_uint8(v___x_3376_, 10, v___x_3374_);
lean_ctor_set_uint8(v___x_3376_, 11, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 12, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 13, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 14, v___x_3375_);
lean_ctor_set_uint8(v___x_3376_, 15, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 16, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 17, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 18, v___x_3370_);
lean_ctor_set_uint8(v___x_3376_, 19, v___x_3368_);
v___x_3377_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3376_);
v___x_3378_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set_uint64(v___x_3378_, sizeof(void*)*1, v___x_3377_);
v___x_3379_ = lean_unsigned_to_nat(0u);
v___x_3380_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3381_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3382_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3383_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3384_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3384_, 0, v___x_3378_);
lean_ctor_set(v___x_3384_, 1, v___x_3116_);
lean_ctor_set(v___x_3384_, 2, v___x_3381_);
lean_ctor_set(v___x_3384_, 3, v___x_3382_);
lean_ctor_set(v___x_3384_, 4, v___x_3383_);
lean_ctor_set(v___x_3384_, 5, v___x_3379_);
lean_ctor_set(v___x_3384_, 6, v___x_3383_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7, v___x_3368_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7 + 1, v___x_3368_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7 + 2, v___x_3368_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7 + 3, v___x_3298_);
v___x_3385_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3386_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3385_);
lean_ctor_set(v___x_3388_, 1, v___x_3386_);
lean_ctor_set(v___x_3388_, 2, v___x_3116_);
lean_ctor_set(v___x_3388_, 3, v___x_3380_);
lean_ctor_set(v___x_3388_, 4, v___x_3387_);
v___x_3389_ = lean_st_mk_ref(v___x_3388_);
v___x_3390_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3360_, v___x_3298_, v___x_3384_, v___x_3389_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3384_, 7);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3392_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___x_3392_ = lean_st_ref_get(v___x_3389_);
lean_dec(v___x_3389_);
lean_dec(v___x_3392_);
if (lean_obj_tag(v_a_3391_) == 0)
{
v___y_3282_ = v___x_3355_;
v___y_3283_ = v_a_3296_;
v_a_3284_ = v___x_3368_;
goto v___jp_3281_;
}
else
{
lean_dec_ref_known(v_a_3391_, 1);
v___y_3282_ = v___x_3355_;
v___y_3283_ = v_a_3296_;
v_a_3284_ = v___x_3370_;
goto v___jp_3281_;
}
}
else
{
lean_object* v_a_3393_; 
lean_dec(v___x_3389_);
v_a_3393_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3390_, 1);
v___y_3277_ = v___x_3355_;
v___y_3278_ = v_a_3296_;
v_a_3279_ = v_a_3393_;
goto v___jp_3276_;
}
}
}
else
{
uint8_t v___x_3394_; uint8_t v___x_3395_; uint8_t v___x_3396_; uint8_t v___x_3397_; lean_object* v___x_3398_; uint64_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec(v_snd_3361_);
lean_dec_ref(v___f_3117_);
v___x_3394_ = 0;
v___x_3395_ = 1;
v___x_3396_ = 0;
v___x_3397_ = 2;
v___x_3398_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3398_, 0, v___x_3394_);
lean_ctor_set_uint8(v___x_3398_, 1, v___x_3394_);
lean_ctor_set_uint8(v___x_3398_, 2, v___x_3394_);
lean_ctor_set_uint8(v___x_3398_, 3, v___x_3394_);
lean_ctor_set_uint8(v___x_3398_, 4, v___x_3394_);
lean_ctor_set_uint8(v___x_3398_, 5, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 6, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 7, v___x_3394_);
lean_ctor_set_uint8(v___x_3398_, 8, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 9, v___x_3395_);
lean_ctor_set_uint8(v___x_3398_, 10, v___x_3396_);
lean_ctor_set_uint8(v___x_3398_, 11, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 12, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 13, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 14, v___x_3397_);
lean_ctor_set_uint8(v___x_3398_, 15, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 16, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 17, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 18, v___x_3368_);
lean_ctor_set_uint8(v___x_3398_, 19, v___x_3394_);
v___x_3399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set_uint64(v___x_3400_, sizeof(void*)*1, v___x_3399_);
v___x_3401_ = lean_unsigned_to_nat(0u);
v___x_3402_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3403_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3405_ = lean_box(0);
lean_inc(v___x_3116_);
v___x_3406_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3406_, 0, v___x_3400_);
lean_ctor_set(v___x_3406_, 1, v___x_3116_);
lean_ctor_set(v___x_3406_, 2, v___x_3403_);
lean_ctor_set(v___x_3406_, 3, v___x_3404_);
lean_ctor_set(v___x_3406_, 4, v___x_3405_);
lean_ctor_set(v___x_3406_, 5, v___x_3401_);
lean_ctor_set(v___x_3406_, 6, v___x_3405_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*7, v___x_3394_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*7 + 1, v___x_3394_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*7 + 2, v___x_3394_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*7 + 3, v___x_3298_);
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3408_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3409_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3407_);
lean_ctor_set(v___x_3410_, 1, v___x_3408_);
lean_ctor_set(v___x_3410_, 2, v___x_3116_);
lean_ctor_set(v___x_3410_, 3, v___x_3402_);
lean_ctor_set(v___x_3410_, 4, v___x_3409_);
v___x_3411_ = lean_st_mk_ref(v___x_3410_);
v___x_3412_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3360_, v___x_3406_, v___x_3411_, v___y_3119_, v___y_3120_);
lean_dec_ref_known(v___x_3406_, 7);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v___x_3414_ = lean_st_ref_get(v___x_3411_);
lean_dec(v___x_3411_);
lean_dec(v___x_3414_);
if (lean_obj_tag(v_a_3413_) == 0)
{
v___y_3282_ = v___x_3355_;
v___y_3283_ = v_a_3296_;
v_a_3284_ = v___x_3394_;
goto v___jp_3281_;
}
else
{
lean_dec_ref_known(v_a_3413_, 1);
v___y_3282_ = v___x_3355_;
v___y_3283_ = v_a_3296_;
v_a_3284_ = v___x_3368_;
goto v___jp_3281_;
}
}
else
{
lean_object* v_a_3415_; 
lean_dec(v___x_3411_);
v_a_3415_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3412_, 1);
v___y_3277_ = v___x_3355_;
v___y_3278_ = v_a_3296_;
v_a_3279_ = v_a_3415_;
goto v___jp_3276_;
}
}
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec(v___x_3358_);
lean_dec(v_name_3118_);
lean_dec(v___x_3116_);
v___x_3416_ = lean_box(0);
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3119_);
v___x_3417_ = lean_apply_4(v___f_3117_, v___x_3416_, v___y_3119_, v___y_3120_, lean_box(0));
v___y_3288_ = v___x_3355_;
v___y_3289_ = v_a_3296_;
v___y_3290_ = v___x_3417_;
goto v___jp_3287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3527_, lean_object* v___f_3528_, lean_object* v_name_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3527_, v___f_3528_, v_name_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
return v_res_3533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = lean_unsigned_to_nat(3137104340u);
v___x_3579_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3580_ = l_Lean_Name_num___override(v___x_3579_, v___x_3578_);
return v___x_3580_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3583_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3584_ = l_Lean_Name_str___override(v___x_3583_, v___x_3582_);
return v___x_3584_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3586_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3587_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3588_ = l_Lean_Name_str___override(v___x_3587_, v___x_3586_);
return v___x_3588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = lean_unsigned_to_nat(2u);
v___x_3590_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3591_ = l_Lean_Name_num___override(v___x_3590_, v___x_3589_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3593_; lean_object* v___x_3594_; 
v___f_3593_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3594_ = l_Lean_registerReservedNameAction(v___f_3593_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3595_; uint8_t v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec_ref_known(v___x_3594_, 1);
v___x_3595_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__8));
v___x_3596_ = 0;
v___x_3597_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3598_ = l_Lean_registerTraceClass(v___x_3595_, v___x_3596_, v___x_3597_);
return v___x_3598_;
}
else
{
return v___x_3594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3601_, lean_object* v_x_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3602_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3607_, lean_object* v_x_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3607_, v_x_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
return v_res_3612_;
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
