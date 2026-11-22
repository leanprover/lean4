// Lean compiler output
// Module: Lean.Meta.Eqns
// Imports: public import Lean.Meta.Match.MatcherInfo public import Lean.DefEqAttrib public import Lean.Meta.RecExt public import Lean.Meta.LetToHave import Lean.Meta.AppBuilder public import Lean.Meta.ExprDefEq public import Lean.Meta.WHNF
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
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
extern lean_object* l_Lean_Meta_smartUnfolding;
extern lean_object* l_Lean_Meta_backward_whnf_reducibleClassField;
extern lean_object* l_Lean_Meta_backward_isDefEq_respectTransparency_types;
extern lean_object* l_Lean_Meta_backward_isDefEq_respectTransparency;
extern lean_object* l_Lean_backward_defeqAttrib_useBackward;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_isEqnLikeSuffix___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_92_ = l_Lean_Meta_smartUnfolding;
v___x_93_ = l_Lean_Meta_backward_whnf_reducibleClassField;
v___x_94_ = l_Lean_Meta_backward_isDefEq_respectTransparency_types;
v___x_95_ = l_Lean_Meta_backward_isDefEq_respectTransparency;
v___x_96_ = l_Lean_backward_defeqAttrib_useBackward;
v___x_97_ = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
v___x_98_ = l_Lean_Meta_backward_eqns_nonrecursive;
v___x_99_ = lean_unsigned_to_nat(7u);
v___x_100_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_101_ = lean_array_push(v___x_100_, v___x_98_);
v___x_102_ = lean_array_push(v___x_101_, v___x_97_);
v___x_103_ = lean_array_push(v___x_102_, v___x_96_);
v___x_104_ = lean_array_push(v___x_103_, v___x_95_);
v___x_105_ = lean_array_push(v___x_104_, v___x_94_);
v___x_106_ = lean_array_push(v___x_105_, v___x_93_);
v___x_107_ = lean_array_push(v___x_106_, v___x_92_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Meta_eqnAffectingOptions___closed__0, &l_Lean_Meta_eqnAffectingOptions___closed__0_once, _init_l_Lean_Meta_eqnAffectingOptions___closed__0);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(lean_object* v_env_109_, lean_object* v_as_110_, size_t v_i_111_, size_t v_stop_112_, lean_object* v_b_113_){
_start:
{
lean_object* v___y_115_; uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_eq(v_i_111_, v_stop_112_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_fst_121_; uint8_t v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_120_ = lean_array_uget_borrowed(v_as_110_, v_i_111_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
v___x_122_ = 1;
lean_inc_ref(v_env_109_);
v___x_123_ = l_Lean_Environment_setExporting(v_env_109_, v___x_122_);
lean_inc(v_fst_121_);
v___x_124_ = l_Lean_Environment_contains(v___x_123_, v_fst_121_, v___x_122_);
if (v___x_124_ == 0)
{
v___y_115_ = v_b_113_;
goto v___jp_114_;
}
else
{
lean_object* v___x_125_; 
lean_inc(v___x_120_);
v___x_125_ = lean_array_push(v_b_113_, v___x_120_);
v___y_115_ = v___x_125_;
goto v___jp_114_;
}
}
else
{
lean_dec_ref(v_env_109_);
return v_b_113_;
}
v___jp_114_:
{
size_t v___x_116_; size_t v___x_117_; 
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_add(v_i_111_, v___x_116_);
v_i_111_ = v___x_117_;
v_b_113_ = v___y_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_126_, lean_object* v_as_127_, lean_object* v_i_128_, lean_object* v_stop_129_, lean_object* v_b_130_){
_start:
{
size_t v_i_boxed_131_; size_t v_stop_boxed_132_; lean_object* v_res_133_; 
v_i_boxed_131_ = lean_unbox_usize(v_i_128_);
lean_dec(v_i_128_);
v_stop_boxed_132_ = lean_unbox_usize(v_stop_129_);
lean_dec(v_stop_129_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_126_, v_as_127_, v_i_boxed_131_, v_stop_boxed_132_, v_b_130_);
lean_dec_ref(v_as_127_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v_k_136_; lean_object* v_v_137_; lean_object* v_l_138_; lean_object* v_r_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_k_136_ = lean_ctor_get(v_x_135_, 1);
v_v_137_ = lean_ctor_get(v_x_135_, 2);
v_l_138_ = lean_ctor_get(v_x_135_, 3);
v_r_139_ = lean_ctor_get(v_x_135_, 4);
v___x_140_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_134_, v_l_138_);
lean_inc(v_v_137_);
lean_inc(v_k_136_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_k_136_);
lean_ctor_set(v___x_141_, 1, v_v_137_);
v___x_142_ = lean_array_push(v___x_140_, v___x_141_);
v_init_134_ = v___x_142_;
v_x_135_ = v_r_139_;
goto _start;
}
else
{
return v_init_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_144_, v_x_145_);
lean_dec(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(lean_object* v_env_147_, lean_object* v_as_148_, size_t v_i_149_, size_t v_stop_150_, lean_object* v_b_151_){
_start:
{
lean_object* v___y_153_; uint8_t v___x_157_; 
v___x_157_ = lean_usize_dec_eq(v_i_149_, v_stop_150_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v_fst_159_; uint8_t v___x_160_; 
v___x_158_ = lean_array_uget_borrowed(v_as_148_, v_i_149_);
v_fst_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_fst_159_);
lean_inc_ref(v_env_147_);
v___x_160_ = l_Lean_Environment_contains(v_env_147_, v_fst_159_, v___x_157_);
if (v___x_160_ == 0)
{
v___y_153_ = v_b_151_;
goto v___jp_152_;
}
else
{
lean_object* v___x_161_; 
lean_inc(v___x_158_);
v___x_161_ = lean_array_push(v_b_151_, v___x_158_);
v___y_153_ = v___x_161_;
goto v___jp_152_;
}
}
else
{
lean_dec_ref(v_env_147_);
return v_b_151_;
}
v___jp_152_:
{
size_t v___x_154_; size_t v___x_155_; 
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_add(v_i_149_, v___x_154_);
v_i_149_ = v___x_155_;
v_b_151_ = v___y_153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_162_, lean_object* v_as_163_, lean_object* v_i_164_, lean_object* v_stop_165_, lean_object* v_b_166_){
_start:
{
size_t v_i_boxed_167_; size_t v_stop_boxed_168_; lean_object* v_res_169_; 
v_i_boxed_167_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_stop_boxed_168_ = lean_unbox_usize(v_stop_165_);
lean_dec(v_stop_165_);
v_res_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_162_, v_as_163_, v_i_boxed_167_, v_stop_boxed_168_, v_b_166_);
lean_dec_ref(v_as_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(lean_object* v_env_174_, lean_object* v_s_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___y_178_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_187_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_188_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v___x_187_, v_s_175_);
v___x_189_ = lean_array_get_size(v___x_188_);
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_191_ = lean_nat_dec_lt(v___x_176_, v___x_189_);
if (v___x_191_ == 0)
{
lean_dec_ref(v___x_188_);
v___y_178_ = v___x_190_;
goto v___jp_177_;
}
else
{
size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((size_t)0ULL);
v___x_193_ = lean_usize_of_nat(v___x_189_);
lean_inc_ref(v_env_174_);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_174_, v___x_188_, v___x_192_, v___x_193_, v___x_190_);
lean_dec_ref(v___x_188_);
v___y_178_ = v___x_194_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_array_get_size(v___y_178_);
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_181_ = lean_nat_dec_lt(v___x_176_, v___x_179_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref(v_env_174_);
v___x_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___y_178_);
return v___x_182_;
}
else
{
size_t v___x_183_; size_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = ((size_t)0ULL);
v___x_184_ = lean_usize_of_nat(v___x_179_);
v___x_185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_174_, v___y_178_, v___x_183_, v___x_184_, v___x_180_);
lean_inc_ref(v___x_185_);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
lean_ctor_set(v___x_186_, 2, v___y_178_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_env_195_, lean_object* v_s_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(v_env_195_, v_s_196_);
lean_dec(v_s_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; 
v___f_205_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_207_ = lean_box(1);
v___x_208_ = 0;
v___x_209_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_206_, v___x_207_, v___x_208_, v___f_205_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object* v_init_212_, lean_object* v_t_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_212_, v_t_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_215_, lean_object* v_t_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_215_, v_t_216_);
lean_dec(v_t_216_);
return v_res_217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_string_utf8_byte_size(v_s_224_);
v___x_226_ = lean_unsigned_to_nat(3u);
v___x_227_ = lean_nat_dec_le(v___x_226_, v___x_225_);
if (v___x_227_ == 0)
{
lean_dec_ref(v_s_224_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_228_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_string_memcmp(v_s_224_, v___x_228_, v___x_229_, v___x_229_, v___x_226_);
if (v___x_230_ == 0)
{
lean_dec_ref(v_s_224_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
lean_inc_ref(v_s_224_);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v_s_224_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_225_);
v___x_232_ = l_String_Slice_Pos_nextn(v___x_231_, v___x_229_, v___x_226_);
lean_dec_ref_known(v___x_231_, 3);
v___x_233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_233_, 0, v_s_224_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_ctor_set(v___x_233_, 2, v___x_225_);
v___x_234_ = l_String_Slice_isNat(v___x_233_);
lean_dec_ref_known(v___x_233_, 3);
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_235_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_242_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_244_ = lean_string_dec_eq(v_s_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_246_ = lean_string_dec_eq(v_s_242_, v___x_245_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_242_);
return v___x_247_;
}
else
{
lean_dec_ref(v_s_242_);
return v___x_246_;
}
}
else
{
lean_dec_ref(v_s_242_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lean_Meta_isEqnLikeSuffix(v_s_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_env_254_, lean_object* v_str_255_, lean_object* v_as_x27_256_, lean_object* v_b_257_){
_start:
{
if (lean_obj_tag(v_as_x27_256_) == 0)
{
lean_dec_ref(v_str_255_);
lean_dec_ref(v_env_254_);
lean_inc_ref(v_b_257_);
return v_b_257_;
}
else
{
lean_object* v_head_258_; lean_object* v_tail_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_head_258_ = lean_ctor_get(v_as_x27_256_, 0);
v_tail_259_ = lean_ctor_get(v_as_x27_256_, 1);
v___x_260_ = lean_box(0);
v___x_261_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_262_ = 0;
lean_inc_ref(v_env_254_);
v___x_263_ = l_Lean_Environment_setExporting(v_env_254_, v___x_262_);
lean_inc(v_head_258_);
v___x_264_ = l_Lean_Environment_isSafeDefinition(v___x_263_, v_head_258_);
if (v___x_264_ == 0)
{
v_as_x27_256_ = v_tail_259_;
v_b_257_ = v___x_261_;
goto _start;
}
else
{
uint8_t v___x_266_; 
lean_inc(v_head_258_);
lean_inc_ref(v_env_254_);
v___x_266_ = l_Lean_Meta_isMatcherCore(v_env_254_, v_head_258_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref(v_env_254_);
lean_inc(v_head_258_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_head_258_);
lean_ctor_set(v___x_267_, 1, v_str_255_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_260_);
return v___x_270_;
}
else
{
v_as_x27_256_ = v_tail_259_;
v_b_257_ = v___x_261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_env_272_, lean_object* v_str_273_, lean_object* v_as_x27_274_, lean_object* v_b_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_env_272_, v_str_273_, v_as_x27_274_, v_b_275_);
lean_dec_ref(v_b_275_);
lean_dec(v_as_x27_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_277_, lean_object* v_name_278_){
_start:
{
if (lean_obj_tag(v_name_278_) == 1)
{
lean_object* v_pre_279_; lean_object* v_str_280_; uint8_t v___x_281_; 
v_pre_279_ = lean_ctor_get(v_name_278_, 0);
lean_inc(v_pre_279_);
v_str_280_ = lean_ctor_get(v_name_278_, 1);
lean_inc_ref_n(v_str_280_, 2);
lean_dec_ref_known(v_name_278_, 2);
v___x_281_ = l_Lean_Meta_isEqnLikeSuffix(v_str_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_dec_ref(v_str_280_);
lean_dec(v_pre_279_);
lean_dec_ref(v_env_277_);
v___x_282_ = lean_box(0);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_fst_290_; 
lean_inc(v_pre_279_);
v___x_283_ = l_Lean_privateToUserName(v_pre_279_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v_pre_279_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_box(0);
v___x_288_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_289_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_env_277_, v_str_280_, v___x_286_, v___x_288_);
lean_dec_ref_known(v___x_286_, 2);
v_fst_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_fst_290_);
lean_dec_ref(v___x_289_);
if (lean_obj_tag(v_fst_290_) == 0)
{
return v___x_287_;
}
else
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v_fst_290_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v_fst_290_, 1);
return v_val_291_;
}
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v_name_278_);
lean_dec_ref(v_env_277_);
v___x_292_ = lean_box(0);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_env_293_, lean_object* v_str_294_, lean_object* v_as_295_, lean_object* v_as_x27_296_, lean_object* v_b_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_env_293_, v_str_294_, v_as_x27_296_, v_b_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_env_300_, lean_object* v_str_301_, lean_object* v_as_302_, lean_object* v_as_x27_303_, lean_object* v_b_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_env_300_, v_str_301_, v_as_302_, v_as_x27_303_, v_b_304_, v_a_305_);
lean_dec_ref(v_b_304_);
lean_dec(v_as_x27_303_);
lean_dec(v_as_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_307_, lean_object* v_declName_308_, lean_object* v_suffix_309_){
_start:
{
uint8_t v_isExposed_310_; lean_object* v_name_311_; 
lean_inc(v_declName_308_);
lean_inc_ref(v_env_307_);
v_isExposed_310_ = l_Lean_Environment_hasExposedBody(v_env_307_, v_declName_308_);
v_name_311_ = l_Lean_Name_str___override(v_declName_308_, v_suffix_309_);
if (v_isExposed_310_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_mkPrivateName(v_env_307_, v_name_311_);
lean_dec_ref(v_env_307_);
return v___x_312_;
}
else
{
lean_dec_ref(v_env_307_);
return v_name_311_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_313_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_ctor_set(v___x_318_, 3, v___x_317_);
lean_ctor_set(v___x_318_, 4, v___x_316_);
lean_ctor_set(v___x_318_, 5, v___x_316_);
lean_ctor_set(v___x_318_, 6, v___x_316_);
lean_ctor_set(v___x_318_, 7, v___x_316_);
lean_ctor_set(v___x_318_, 8, v___x_316_);
lean_ctor_set(v___x_318_, 9, v___x_316_);
lean_ctor_set(v___x_318_, 10, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_unsigned_to_nat(32u);
v___x_320_ = lean_mk_empty_array_with_capacity(v___x_319_);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_322_ = ((size_t)5ULL);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_unsigned_to_nat(32u);
v___x_325_ = lean_mk_empty_array_with_capacity(v___x_324_);
v___x_326_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_327_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
lean_ctor_set(v___x_327_, 2, v___x_323_);
lean_ctor_set(v___x_327_, 3, v___x_323_);
lean_ctor_set_usize(v___x_327_, 4, v___x_322_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_box(1);
v___x_329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v___x_328_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; lean_object* v_toCold_337_; lean_object* v_env_338_; lean_object* v_options_339_; uint8_t v___x_340_; lean_object* v_env_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_336_ = lean_st_ref_get(v___y_334_);
v_toCold_337_ = lean_ctor_get(v___y_333_, 0);
v_env_338_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_env_338_);
lean_dec(v___x_336_);
v_options_339_ = lean_ctor_get(v_toCold_337_, 2);
v___x_340_ = 0;
v_env_341_ = l_Lean_Environment_setRecordingDeps(v_env_338_, v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_339_);
v___x_344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_344_, 0, v_env_341_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
lean_ctor_set(v___x_344_, 2, v___x_343_);
lean_ctor_set(v___x_344_, 3, v_options_339_);
v___x_345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_msgData_332_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_ref_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_ref_356_ = lean_ctor_get(v___y_353_, 2);
v___x_357_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_352_, v___y_353_, v___y_354_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_inc(v_ref_356_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_ref_356_);
lean_ctor_set(v___x_362_, 1, v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_381_, lean_object* v_reservedName_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_386_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_387_ = 0;
v___x_388_ = l_Lean_MessageData_ofConstName(v_declName_381_, v___x_387_);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_386_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = 1;
v___x_393_ = l_Lean_MessageData_ofConstName(v_reservedName_382_, v___x_392_);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_391_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_396_, v___y_383_, v___y_384_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_398_, lean_object* v_reservedName_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_398_, v_reservedName_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_404_, lean_object* v_suffix_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_reservedName_409_; lean_object* v___x_410_; lean_object* v_env_411_; uint8_t v___x_412_; uint8_t v___x_413_; 
lean_inc(v_declName_404_);
v_reservedName_409_ = l_Lean_Name_str___override(v_declName_404_, v_suffix_405_);
v___x_410_ = lean_st_ref_get(v___y_407_);
v_env_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_env_411_);
lean_dec(v___x_410_);
v___x_412_ = 1;
lean_inc(v_reservedName_409_);
v___x_413_ = l_Lean_Environment_contains(v_env_411_, v_reservedName_409_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_reservedName_409_);
lean_dec(v_declName_404_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_404_, v_reservedName_409_, v___y_406_, v___y_407_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_417_, lean_object* v_suffix_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_417_, v_suffix_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_423_);
v___x_428_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_423_, v___x_427_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref_known(v___x_428_, 1);
v___x_429_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_423_);
v___x_430_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_423_, v___x_429_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref_known(v___x_430_, 1);
v___x_431_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_432_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_423_, v___x_431_, v_a_424_, v_a_425_);
return v___x_432_;
}
else
{
lean_dec(v_declName_423_);
return v___x_430_;
}
}
else
{
lean_dec(v_declName_423_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_438_, lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_439_, v___y_440_, v___y_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_444_, lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_444_, v_msg_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_449_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_(lean_object* v_env_450_, lean_object* v_n_451_){
_start:
{
lean_object* v___x_452_; 
lean_inc(v_n_451_);
lean_inc_ref(v_env_450_);
v___x_452_ = l_Lean_Meta_declFromEqLikeName(v_env_450_, v_n_451_);
if (lean_obj_tag(v___x_452_) == 1)
{
lean_object* v_val_453_; lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_val_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v___x_452_, 1);
v_fst_454_ = lean_ctor_get(v_val_453_, 0);
lean_inc(v_fst_454_);
v_snd_455_ = lean_ctor_get(v_val_453_, 1);
lean_inc(v_snd_455_);
lean_dec(v_val_453_);
v___x_456_ = l_Lean_Meta_mkEqLikeNameFor(v_env_450_, v_fst_454_, v_snd_455_);
v___x_457_ = lean_name_eq(v_n_451_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v_n_451_);
return v___x_457_;
}
else
{
uint8_t v___x_458_; 
lean_dec(v___x_452_);
lean_dec(v_n_451_);
lean_dec_ref(v_env_450_);
v___x_458_ = 0;
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2____boxed(lean_object* v_env_459_, lean_object* v_n_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_(v_env_459_, v_n_460_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___f_466_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_));
v___x_467_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_));
v___x_468_ = l_Lean_registerReservedNamePredicate(v___x_467_, v___f_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2____boxed(lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_();
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_box(0);
v___x_473_ = lean_st_mk_ref(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_476_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_479_ = lean_mk_io_user_error(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_480_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = l_Lean_initializing();
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec_ref(v_f_480_);
v___x_483_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_485_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_486_ = lean_st_ref_take(v___x_485_);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v_f_480_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_st_ref_put(v___x_485_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Meta_registerGetEqnsFn(v_f_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_503_; lean_object* v_env_504_; uint8_t v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_st_ref_get(v_a_497_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_env_504_);
lean_dec(v___x_503_);
v___x_505_ = 0;
lean_inc(v_declName_493_);
v___x_506_ = l_Lean_Environment_findAsync_x3f(v_env_504_, v_declName_493_, v___x_505_);
if (lean_obj_tag(v___x_506_) == 1)
{
lean_object* v_val_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_538_; 
v_val_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_538_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_538_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_val_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_538_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v_kind_511_; 
v_kind_511_ = lean_ctor_get_uint8(v_val_507_, sizeof(void*)*3);
if (v_kind_511_ == 0)
{
lean_object* v_sig_512_; lean_object* v___x_513_; lean_object* v_env_514_; uint8_t v___x_515_; 
v_sig_512_ = lean_ctor_get(v_val_507_, 1);
lean_inc_ref(v_sig_512_);
lean_dec(v_val_507_);
v___x_513_ = lean_st_ref_get(v_a_497_);
v_env_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_env_514_);
lean_dec(v___x_513_);
v___x_515_ = l_Lean_Meta_isMatcherCore(v_env_514_, v_declName_493_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v_type_517_; lean_object* v___x_518_; 
lean_del_object(v___x_509_);
v___x_516_ = lean_task_get_own(v_sig_512_);
v_type_517_ = lean_ctor_get(v___x_516_, 2);
lean_inc_ref(v_type_517_);
lean_dec(v___x_516_);
v___x_518_ = l_Lean_Meta_isProp(v_type_517_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_533_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_533_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_533_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_533_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v___x_523_; 
v___x_523_ = lean_unbox(v_a_519_);
lean_dec(v_a_519_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = 1;
v___x_525_ = lean_box(v___x_524_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_box(v___x_515_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_529_);
v___x_531_ = v___x_521_;
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
}
else
{
return v___x_518_;
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec_ref(v_sig_512_);
v___x_534_ = lean_box(v___x_505_);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 0);
lean_ctor_set(v___x_509_, 0, v___x_534_);
v___x_536_ = v___x_509_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_del_object(v___x_509_);
lean_dec(v_val_507_);
lean_dec(v_declName_493_);
goto v___jp_499_;
}
}
}
else
{
lean_dec(v___x_506_);
lean_dec(v_declName_493_);
goto v___jp_499_;
}
v___jp_499_:
{
uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = 0;
v___x_501_ = lean_box(v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_545_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object* v___x_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v___x_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_553_);
return v_res_555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_556_; lean_object* v___f_557_; 
v___x_556_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_557_, 0, v___x_556_);
return v___f_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; 
v___f_564_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_box(1);
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_));
v___x_568_ = 0;
v___x_569_ = 1;
v___x_570_ = l_Lean_registerEnvExtension___redArg(v___f_564_, v___x_565_, v___x_566_, v___x_567_, v___x_568_, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_573_, lean_object* v_opt_574_){
_start:
{
lean_object* v_name_575_; lean_object* v_defValue_576_; lean_object* v_map_577_; lean_object* v___x_578_; 
v_name_575_ = lean_ctor_get(v_opt_574_, 0);
v_defValue_576_ = lean_ctor_get(v_opt_574_, 1);
v_map_577_ = lean_ctor_get(v_opts_573_, 0);
v___x_578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_577_, v_name_575_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_inc(v_defValue_576_);
return v_defValue_576_;
}
else
{
lean_object* v_val_579_; 
v_val_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_578_, 1);
if (lean_obj_tag(v_val_579_) == 3)
{
lean_object* v_v_580_; 
v_v_580_ = lean_ctor_get(v_val_579_, 0);
lean_inc(v_v_580_);
lean_dec_ref_known(v_val_579_, 1);
return v_v_580_;
}
else
{
lean_dec(v_val_579_);
lean_inc(v_defValue_576_);
return v_defValue_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_581_, lean_object* v_opt_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_581_, v_opt_582_);
lean_dec_ref(v_opt_582_);
lean_dec_ref(v_opts_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_587_, size_t v_sz_588_, size_t v_i_589_, lean_object* v_b_590_){
_start:
{
lean_object* v_a_592_; uint8_t v___x_596_; 
v___x_596_ = lean_usize_dec_lt(v_i_589_, v_sz_588_);
if (v___x_596_ == 0)
{
return v_b_590_;
}
else
{
lean_object* v_a_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v_map_600_; uint8_t v_hasTrace_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_614_; 
v_a_597_ = lean_array_uget_borrowed(v_as_587_, v_i_589_);
v_fst_598_ = lean_ctor_get(v_a_597_, 0);
v_snd_599_ = lean_ctor_get(v_a_597_, 1);
v_map_600_ = lean_ctor_get(v_b_590_, 0);
v_hasTrace_601_ = lean_ctor_get_uint8(v_b_590_, sizeof(void*)*1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_b_590_);
if (v_isSharedCheck_614_ == 0)
{
v___x_603_ = v_b_590_;
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_map_600_);
lean_dec(v_b_590_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; 
lean_inc(v_snd_599_);
lean_inc(v_fst_598_);
v___x_605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_598_, v_snd_599_, v_map_600_);
if (v_hasTrace_601_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_609_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_607_ = l_Lean_Name_isPrefixOf(v___x_606_, v_fst_598_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*1, v___x_607_);
v_a_592_ = v___x_609_;
goto v___jp_591_;
}
}
else
{
lean_object* v___x_612_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_612_ = v___x_603_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
lean_ctor_set_uint8(v_reuseFailAlloc_613_, sizeof(void*)*1, v_hasTrace_601_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v_a_592_ = v___x_612_;
goto v___jp_591_;
}
}
}
}
v___jp_591_:
{
size_t v___x_593_; size_t v___x_594_; 
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_i_589_, v___x_593_);
v_i_589_ = v___x_594_;
v_b_590_ = v_a_592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_615_, lean_object* v_sz_616_, lean_object* v_i_617_, lean_object* v_b_618_){
_start:
{
size_t v_sz_boxed_619_; size_t v_i_boxed_620_; lean_object* v_res_621_; 
v_sz_boxed_619_ = lean_unbox_usize(v_sz_616_);
lean_dec(v_sz_616_);
v_i_boxed_620_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_615_, v_sz_boxed_619_, v_i_boxed_620_, v_b_618_);
lean_dec_ref(v_as_615_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_622_, lean_object* v_k_623_, uint8_t v_v_624_){
_start:
{
lean_object* v_map_625_; uint8_t v_hasTrace_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_640_; 
v_map_625_ = lean_ctor_get(v_o_622_, 0);
v_hasTrace_626_ = lean_ctor_get_uint8(v_o_622_, sizeof(void*)*1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_o_622_);
if (v_isSharedCheck_640_ == 0)
{
v___x_628_ = v_o_622_;
v_isShared_629_ = v_isSharedCheck_640_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_map_625_);
lean_dec(v_o_622_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_640_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_630_, 0, v_v_624_);
lean_inc(v_k_623_);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_623_, v___x_630_, v_map_625_);
if (v_hasTrace_626_ == 0)
{
lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_635_; 
v___x_632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_633_ = l_Lean_Name_isPrefixOf(v___x_632_, v_k_623_);
lean_dec(v_k_623_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_631_);
v___x_635_ = v___x_628_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_631_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_633_);
return v___x_635_;
}
}
else
{
lean_object* v___x_638_; 
lean_dec(v_k_623_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_631_);
v___x_638_ = v___x_628_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*1, v_hasTrace_626_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_641_, lean_object* v_k_642_, lean_object* v_v_643_){
_start:
{
uint8_t v_v_boxed_644_; lean_object* v_res_645_; 
v_v_boxed_644_ = lean_unbox(v_v_643_);
v_res_645_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_641_, v_k_642_, v_v_boxed_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_646_, lean_object* v_opt_647_, uint8_t v_val_648_){
_start:
{
lean_object* v_name_649_; lean_object* v___x_650_; 
v_name_649_ = lean_ctor_get(v_opt_647_, 0);
lean_inc(v_name_649_);
lean_dec_ref(v_opt_647_);
v___x_650_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_646_, v_name_649_, v_val_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_651_, lean_object* v_opt_652_, lean_object* v_val_653_){
_start:
{
uint8_t v_val_boxed_654_; lean_object* v_res_655_; 
v_val_boxed_654_ = lean_unbox(v_val_653_);
v_res_655_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_651_, v_opt_652_, v_val_boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_656_, size_t v_i_657_, size_t v_stop_658_, lean_object* v_b_659_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = lean_usize_dec_eq(v_i_657_, v_stop_658_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v_defValue_662_; uint8_t v___x_663_; lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; 
v___x_661_ = lean_array_uget_borrowed(v_as_656_, v_i_657_);
v_defValue_662_ = lean_ctor_get(v___x_661_, 1);
v___x_663_ = lean_unbox(v_defValue_662_);
lean_inc(v___x_661_);
v___x_664_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_659_, v___x_661_, v___x_663_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_657_, v___x_665_);
v_i_657_ = v___x_666_;
v_b_659_ = v___x_664_;
goto _start;
}
else
{
return v_b_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_668_, lean_object* v_i_669_, lean_object* v_stop_670_, lean_object* v_b_671_){
_start:
{
size_t v_i_boxed_672_; size_t v_stop_boxed_673_; lean_object* v_res_674_; 
v_i_boxed_672_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_stop_boxed_673_ = lean_unbox_usize(v_stop_670_);
lean_dec(v_stop_670_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_668_, v_i_boxed_672_, v_stop_boxed_673_, v_b_671_);
lean_dec_ref(v_as_668_);
return v_res_674_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = l_Lean_Meta_eqnAffectingOptions;
v___x_680_ = lean_array_get_size(v___x_679_);
return v___x_680_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_681_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_nat_dec_lt(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_684_; size_t v___x_685_; 
v___x_684_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_685_ = lean_usize_of_nat(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_686_, lean_object* v_act_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___y_694_; uint16_t v___y_695_; lean_object* v_fileName_696_; lean_object* v_fileMap_697_; lean_object* v_currNamespace_698_; lean_object* v_openDecls_699_; lean_object* v_initHeartbeats_700_; lean_object* v_maxHeartbeats_701_; lean_object* v_quotContext_702_; lean_object* v_currMacroScope_703_; lean_object* v_cancelTk_x3f_704_; lean_object* v_inheritedTraceOptions_705_; lean_object* v_currRecDepth_706_; lean_object* v_ref_707_; uint8_t v_suppressElabErrors_708_; uint8_t v_checkDeprecated_709_; uint8_t v_isRecordingDeps_710_; lean_object* v___y_711_; lean_object* v___y_718_; uint8_t v___y_719_; uint16_t v___y_720_; lean_object* v___x_758_; lean_object* v_toCold_759_; lean_object* v_currRecDepth_760_; lean_object* v_ref_761_; uint8_t v_suppressElabErrors_762_; uint8_t v_checkDeprecated_763_; uint8_t v_isRecordingDeps_764_; lean_object* v_fileName_765_; lean_object* v_fileMap_766_; lean_object* v_options_767_; lean_object* v_currNamespace_768_; lean_object* v_openDecls_769_; lean_object* v_initHeartbeats_770_; lean_object* v_maxHeartbeats_771_; lean_object* v_quotContext_772_; lean_object* v_currMacroScope_773_; lean_object* v_cancelTk_x3f_774_; lean_object* v_inheritedTraceOptions_775_; lean_object* v___y_777_; 
v___x_758_ = lean_st_ref_get(v_a_691_);
v_toCold_759_ = lean_ctor_get(v_a_690_, 0);
v_currRecDepth_760_ = lean_ctor_get(v_a_690_, 1);
v_ref_761_ = lean_ctor_get(v_a_690_, 2);
v_suppressElabErrors_762_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*3 + 2);
v_checkDeprecated_763_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*3 + 3);
v_isRecordingDeps_764_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*3 + 4);
v_fileName_765_ = lean_ctor_get(v_toCold_759_, 0);
v_fileMap_766_ = lean_ctor_get(v_toCold_759_, 1);
v_options_767_ = lean_ctor_get(v_toCold_759_, 2);
v_currNamespace_768_ = lean_ctor_get(v_toCold_759_, 4);
v_openDecls_769_ = lean_ctor_get(v_toCold_759_, 5);
v_initHeartbeats_770_ = lean_ctor_get(v_toCold_759_, 6);
v_maxHeartbeats_771_ = lean_ctor_get(v_toCold_759_, 7);
v_quotContext_772_ = lean_ctor_get(v_toCold_759_, 8);
v_currMacroScope_773_ = lean_ctor_get(v_toCold_759_, 9);
v_cancelTk_x3f_774_ = lean_ctor_get(v_toCold_759_, 10);
v_inheritedTraceOptions_775_ = lean_ctor_get(v_toCold_759_, 11);
if (v_isRecordingDeps_764_ == 0)
{
lean_object* v_env_788_; lean_object* v___x_789_; lean_object* v_toEnvExtension_790_; lean_object* v_asyncMode_791_; uint8_t v___x_792_; lean_object* v___x_793_; 
v_env_788_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_env_788_);
lean_dec(v___x_758_);
v___x_789_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_790_ = lean_ctor_get(v___x_789_, 0);
v_asyncMode_791_ = lean_ctor_get(v_toEnvExtension_790_, 2);
v___x_792_ = 0;
v___x_793_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_789_, v_env_788_, v_declName_686_, v_asyncMode_791_, v___x_792_);
if (lean_obj_tag(v___x_793_) == 1)
{
lean_object* v_val_794_; lean_object* v___y_796_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_val_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v___x_793_, 1);
v___x_800_ = l_Lean_Meta_eqnAffectingOptions;
v___x_801_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
if (v___x_801_ == 0)
{
lean_inc_ref(v_options_767_);
v___y_796_ = v_options_767_;
goto v___jp_795_;
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
lean_inc_ref(v_options_767_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_800_, v___x_802_, v___x_803_, v_options_767_);
v___y_796_ = v___x_804_;
goto v___jp_795_;
}
v___jp_795_:
{
size_t v_sz_797_; size_t v___x_798_; lean_object* v___x_799_; 
v_sz_797_ = lean_array_size(v_val_794_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_794_, v_sz_797_, v___x_798_, v___y_796_);
lean_dec(v_val_794_);
v___y_777_ = v___x_799_;
goto v___jp_776_;
}
}
else
{
lean_object* v___x_805_; uint8_t v___x_806_; 
lean_dec(v___x_793_);
v___x_805_ = l_Lean_Meta_eqnAffectingOptions;
v___x_806_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
if (v___x_806_ == 0)
{
lean_inc_ref(v_options_767_);
v___y_777_ = v_options_767_;
goto v___jp_776_;
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
lean_inc_ref(v_options_767_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_805_, v___x_807_, v___x_808_, v_options_767_);
v___y_777_ = v___x_809_;
goto v___jp_776_;
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec(v___x_758_);
lean_dec(v_declName_686_);
lean_inc_ref(v_options_767_);
v___x_810_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_767_);
v___y_777_ = v___x_810_;
goto v___jp_776_;
}
v___jp_693_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_712_ = l_Lean_maxRecDepth;
v___x_713_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_694_, v___x_712_);
v___x_714_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_714_, 0, v_fileName_696_);
lean_ctor_set(v___x_714_, 1, v_fileMap_697_);
lean_ctor_set(v___x_714_, 2, v___y_694_);
lean_ctor_set(v___x_714_, 3, v___x_713_);
lean_ctor_set(v___x_714_, 4, v_currNamespace_698_);
lean_ctor_set(v___x_714_, 5, v_openDecls_699_);
lean_ctor_set(v___x_714_, 6, v_initHeartbeats_700_);
lean_ctor_set(v___x_714_, 7, v_maxHeartbeats_701_);
lean_ctor_set(v___x_714_, 8, v_quotContext_702_);
lean_ctor_set(v___x_714_, 9, v_currMacroScope_703_);
lean_ctor_set(v___x_714_, 10, v_cancelTk_x3f_704_);
lean_ctor_set(v___x_714_, 11, v_inheritedTraceOptions_705_);
lean_inc(v_ref_707_);
lean_inc(v_currRecDepth_706_);
v___x_715_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v_currRecDepth_706_);
lean_ctor_set(v___x_715_, 2, v_ref_707_);
lean_ctor_set_uint16(v___x_715_, sizeof(void*)*3, v___y_695_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3 + 2, v_suppressElabErrors_708_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3 + 3, v_checkDeprecated_709_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3 + 4, v_isRecordingDeps_710_);
lean_inc(v___y_711_);
lean_inc(v_a_689_);
lean_inc_ref(v_a_688_);
v___x_716_ = lean_apply_5(v_act_687_, v_a_688_, v_a_689_, v___x_715_, v___y_711_, lean_box(0));
return v___x_716_;
}
v___jp_717_:
{
lean_object* v___x_721_; lean_object* v_env_722_; lean_object* v_nextMacroScope_723_; lean_object* v_ngen_724_; lean_object* v_auxDeclNGen_725_; lean_object* v_traceState_726_; lean_object* v_recordedDeps_727_; lean_object* v_messages_728_; lean_object* v_infoState_729_; lean_object* v_snapshotTasks_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_756_; 
v___x_721_ = lean_st_ref_take(v_a_691_);
v_env_722_ = lean_ctor_get(v___x_721_, 0);
v_nextMacroScope_723_ = lean_ctor_get(v___x_721_, 1);
v_ngen_724_ = lean_ctor_get(v___x_721_, 2);
v_auxDeclNGen_725_ = lean_ctor_get(v___x_721_, 3);
v_traceState_726_ = lean_ctor_get(v___x_721_, 4);
v_recordedDeps_727_ = lean_ctor_get(v___x_721_, 6);
v_messages_728_ = lean_ctor_get(v___x_721_, 7);
v_infoState_729_ = lean_ctor_get(v___x_721_, 8);
v_snapshotTasks_730_ = lean_ctor_get(v___x_721_, 9);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v___x_721_, 5);
lean_dec(v_unused_757_);
v___x_732_ = v___x_721_;
v_isShared_733_ = v_isSharedCheck_756_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snapshotTasks_730_);
lean_inc(v_infoState_729_);
lean_inc(v_messages_728_);
lean_inc(v_recordedDeps_727_);
lean_inc(v_traceState_726_);
lean_inc(v_auxDeclNGen_725_);
lean_inc(v_ngen_724_);
lean_inc(v_nextMacroScope_723_);
lean_inc(v_env_722_);
lean_dec(v___x_721_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_756_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = l_Lean_Kernel_enableDiag(v_env_722_, v___y_719_);
v___x_735_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 5, v___x_735_);
lean_ctor_set(v___x_732_, 0, v___x_734_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_nextMacroScope_723_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_ngen_724_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_auxDeclNGen_725_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_traceState_726_);
lean_ctor_set(v_reuseFailAlloc_755_, 5, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_755_, 6, v_recordedDeps_727_);
lean_ctor_set(v_reuseFailAlloc_755_, 7, v_messages_728_);
lean_ctor_set(v_reuseFailAlloc_755_, 8, v_infoState_729_);
lean_ctor_set(v_reuseFailAlloc_755_, 9, v_snapshotTasks_730_);
v___x_737_ = v_reuseFailAlloc_755_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v_toCold_739_; lean_object* v_currRecDepth_740_; lean_object* v_ref_741_; uint8_t v_suppressElabErrors_742_; uint8_t v_checkDeprecated_743_; uint8_t v_isRecordingDeps_744_; lean_object* v_fileName_745_; lean_object* v_fileMap_746_; lean_object* v_currNamespace_747_; lean_object* v_openDecls_748_; lean_object* v_initHeartbeats_749_; lean_object* v_maxHeartbeats_750_; lean_object* v_quotContext_751_; lean_object* v_currMacroScope_752_; lean_object* v_cancelTk_x3f_753_; lean_object* v_inheritedTraceOptions_754_; 
v___x_738_ = lean_st_ref_put(v_a_691_, v___x_737_);
v_toCold_739_ = lean_ctor_get(v_a_690_, 0);
v_currRecDepth_740_ = lean_ctor_get(v_a_690_, 1);
v_ref_741_ = lean_ctor_get(v_a_690_, 2);
v_suppressElabErrors_742_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*3 + 2);
v_checkDeprecated_743_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*3 + 3);
v_isRecordingDeps_744_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*3 + 4);
v_fileName_745_ = lean_ctor_get(v_toCold_739_, 0);
v_fileMap_746_ = lean_ctor_get(v_toCold_739_, 1);
v_currNamespace_747_ = lean_ctor_get(v_toCold_739_, 4);
v_openDecls_748_ = lean_ctor_get(v_toCold_739_, 5);
v_initHeartbeats_749_ = lean_ctor_get(v_toCold_739_, 6);
v_maxHeartbeats_750_ = lean_ctor_get(v_toCold_739_, 7);
v_quotContext_751_ = lean_ctor_get(v_toCold_739_, 8);
v_currMacroScope_752_ = lean_ctor_get(v_toCold_739_, 9);
v_cancelTk_x3f_753_ = lean_ctor_get(v_toCold_739_, 10);
v_inheritedTraceOptions_754_ = lean_ctor_get(v_toCold_739_, 11);
lean_inc_ref(v_inheritedTraceOptions_754_);
lean_inc(v_cancelTk_x3f_753_);
lean_inc(v_currMacroScope_752_);
lean_inc(v_quotContext_751_);
lean_inc(v_maxHeartbeats_750_);
lean_inc(v_initHeartbeats_749_);
lean_inc(v_openDecls_748_);
lean_inc(v_currNamespace_747_);
lean_inc_ref(v_fileMap_746_);
lean_inc_ref(v_fileName_745_);
v___y_694_ = v___y_718_;
v___y_695_ = v___y_720_;
v_fileName_696_ = v_fileName_745_;
v_fileMap_697_ = v_fileMap_746_;
v_currNamespace_698_ = v_currNamespace_747_;
v_openDecls_699_ = v_openDecls_748_;
v_initHeartbeats_700_ = v_initHeartbeats_749_;
v_maxHeartbeats_701_ = v_maxHeartbeats_750_;
v_quotContext_702_ = v_quotContext_751_;
v_currMacroScope_703_ = v_currMacroScope_752_;
v_cancelTk_x3f_704_ = v_cancelTk_x3f_753_;
v_inheritedTraceOptions_705_ = v_inheritedTraceOptions_754_;
v_currRecDepth_706_ = v_currRecDepth_740_;
v_ref_707_ = v_ref_741_;
v_suppressElabErrors_708_ = v_suppressElabErrors_742_;
v_checkDeprecated_709_ = v_checkDeprecated_743_;
v_isRecordingDeps_710_ = v_isRecordingDeps_744_;
v___y_711_ = v_a_691_;
goto v___jp_693_;
}
}
}
v___jp_776_:
{
uint16_t v___x_778_; lean_object* v___x_779_; lean_object* v_env_780_; uint8_t v___x_781_; uint16_t v___x_782_; uint16_t v___x_783_; uint16_t v___x_784_; uint8_t v___x_785_; 
v___x_778_ = l_Lean_OptionFlags_ofOptions(v___y_777_);
v___x_779_ = lean_st_ref_get(v_a_691_);
v_env_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc_ref(v_env_780_);
lean_dec(v___x_779_);
v___x_781_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_780_);
lean_dec_ref(v_env_780_);
v___x_782_ = 512;
v___x_783_ = lean_uint16_land(v___x_778_, v___x_782_);
v___x_784_ = 0;
v___x_785_ = lean_uint16_dec_eq(v___x_783_, v___x_784_);
if (v___x_785_ == 0)
{
if (v___x_781_ == 0)
{
uint8_t v___x_786_; 
v___x_786_ = 1;
v___y_718_ = v___y_777_;
v___y_719_ = v___x_786_;
v___y_720_ = v___x_778_;
goto v___jp_717_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_775_);
lean_inc(v_cancelTk_x3f_774_);
lean_inc(v_currMacroScope_773_);
lean_inc(v_quotContext_772_);
lean_inc(v_maxHeartbeats_771_);
lean_inc(v_initHeartbeats_770_);
lean_inc(v_openDecls_769_);
lean_inc(v_currNamespace_768_);
lean_inc_ref(v_fileMap_766_);
lean_inc_ref(v_fileName_765_);
v___y_694_ = v___y_777_;
v___y_695_ = v___x_778_;
v_fileName_696_ = v_fileName_765_;
v_fileMap_697_ = v_fileMap_766_;
v_currNamespace_698_ = v_currNamespace_768_;
v_openDecls_699_ = v_openDecls_769_;
v_initHeartbeats_700_ = v_initHeartbeats_770_;
v_maxHeartbeats_701_ = v_maxHeartbeats_771_;
v_quotContext_702_ = v_quotContext_772_;
v_currMacroScope_703_ = v_currMacroScope_773_;
v_cancelTk_x3f_704_ = v_cancelTk_x3f_774_;
v_inheritedTraceOptions_705_ = v_inheritedTraceOptions_775_;
v_currRecDepth_706_ = v_currRecDepth_760_;
v_ref_707_ = v_ref_761_;
v_suppressElabErrors_708_ = v_suppressElabErrors_762_;
v_checkDeprecated_709_ = v_checkDeprecated_763_;
v_isRecordingDeps_710_ = v_isRecordingDeps_764_;
v___y_711_ = v_a_691_;
goto v___jp_693_;
}
}
else
{
if (v___x_781_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_775_);
lean_inc(v_cancelTk_x3f_774_);
lean_inc(v_currMacroScope_773_);
lean_inc(v_quotContext_772_);
lean_inc(v_maxHeartbeats_771_);
lean_inc(v_initHeartbeats_770_);
lean_inc(v_openDecls_769_);
lean_inc(v_currNamespace_768_);
lean_inc_ref(v_fileMap_766_);
lean_inc_ref(v_fileName_765_);
v___y_694_ = v___y_777_;
v___y_695_ = v___x_778_;
v_fileName_696_ = v_fileName_765_;
v_fileMap_697_ = v_fileMap_766_;
v_currNamespace_698_ = v_currNamespace_768_;
v_openDecls_699_ = v_openDecls_769_;
v_initHeartbeats_700_ = v_initHeartbeats_770_;
v_maxHeartbeats_701_ = v_maxHeartbeats_771_;
v_quotContext_702_ = v_quotContext_772_;
v_currMacroScope_703_ = v_currMacroScope_773_;
v_cancelTk_x3f_704_ = v_cancelTk_x3f_774_;
v_inheritedTraceOptions_705_ = v_inheritedTraceOptions_775_;
v_currRecDepth_706_ = v_currRecDepth_760_;
v_ref_707_ = v_ref_761_;
v_suppressElabErrors_708_ = v_suppressElabErrors_762_;
v_checkDeprecated_709_ = v_checkDeprecated_763_;
v_isRecordingDeps_710_ = v_isRecordingDeps_764_;
v___y_711_ = v_a_691_;
goto v___jp_693_;
}
else
{
uint8_t v___x_787_; 
v___x_787_ = 0;
v___y_718_ = v___y_777_;
v___y_719_ = v___x_787_;
v___y_720_ = v___x_778_;
goto v___jp_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_811_, lean_object* v_act_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_811_, v_act_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_819_, lean_object* v_declName_820_, lean_object* v_act_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_820_, v_act_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_828_, lean_object* v_declName_829_, lean_object* v_act_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_828_, v_declName_829_, v_act_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; lean_object* v_env_841_; lean_object* v_toConstantVal_842_; lean_object* v_value_843_; lean_object* v_all_844_; lean_object* v_type_851_; uint8_t v___x_852_; 
v___x_840_ = lean_st_ref_get(v___y_838_);
v_env_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref_n(v_env_841_, 2);
lean_dec(v___x_840_);
v_toConstantVal_842_ = lean_ctor_get(v_thm_837_, 0);
v_value_843_ = lean_ctor_get(v_thm_837_, 1);
v_all_844_ = lean_ctor_get(v_thm_837_, 2);
v_type_851_ = lean_ctor_get(v_toConstantVal_842_, 2);
v___x_852_ = l_Lean_Environment_hasUnsafe(v_env_841_, v_type_851_);
if (v___x_852_ == 0)
{
uint8_t v___x_853_; 
v___x_853_ = l_Lean_Environment_hasUnsafe(v_env_841_, v_value_843_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_854_, 0, v_thm_837_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
else
{
lean_inc(v_all_844_);
lean_inc_ref(v_value_843_);
lean_inc_ref(v_toConstantVal_842_);
lean_dec_ref(v_thm_837_);
goto v___jp_845_;
}
}
else
{
lean_inc(v_all_844_);
lean_inc_ref(v_value_843_);
lean_inc_ref(v_toConstantVal_842_);
lean_dec_ref(v_env_841_);
lean_dec_ref(v_thm_837_);
goto v___jp_845_;
}
v___jp_845_:
{
lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_846_ = lean_box(0);
v___x_847_ = 0;
v___x_848_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_848_, 0, v_toConstantVal_842_);
lean_ctor_set(v___x_848_, 1, v_value_843_);
lean_ctor_set(v___x_848_, 2, v___x_846_);
lean_ctor_set(v___x_848_, 3, v_all_844_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*4, v___x_847_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_856_, v___y_857_);
lean_dec(v___y_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_860_, v___y_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_874_, lean_object* v_b_875_, lean_object* v_c_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
v___x_882_ = lean_apply_7(v_k_874_, v_b_875_, v_c_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_883_, lean_object* v_b_884_, lean_object* v_c_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_883_, v_b_884_, v_c_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_892_, lean_object* v_k_893_, uint8_t v_cleanupAnnotations_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___f_900_; uint8_t v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_900_, 0, v_k_893_);
v___x_901_ = 1;
v___x_902_ = 0;
v___x_903_ = lean_box(0);
v___x_904_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_892_, v___x_901_, v___x_902_, v___x_901_, v___x_902_, v___x_903_, v___f_900_, v_cleanupAnnotations_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_a_913_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_904_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_904_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_921_, lean_object* v_k_922_, lean_object* v_cleanupAnnotations_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_929_; lean_object* v_res_930_; 
v_cleanupAnnotations_boxed_929_ = lean_unbox(v_cleanupAnnotations_923_);
v_res_930_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_921_, v_k_922_, v_cleanupAnnotations_boxed_929_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_931_, lean_object* v_e_932_, lean_object* v_k_933_, uint8_t v_cleanupAnnotations_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_932_, v_k_933_, v_cleanupAnnotations_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_941_, lean_object* v_e_942_, lean_object* v_k_943_, lean_object* v_cleanupAnnotations_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_950_; lean_object* v_res_951_; 
v_cleanupAnnotations_boxed_950_ = lean_unbox(v_cleanupAnnotations_944_);
v_res_951_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_941_, v_e_942_, v_k_943_, v_cleanupAnnotations_boxed_950_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
if (lean_obj_tag(v_a_952_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = l_List_reverse___redArg(v_a_953_);
return v___x_954_;
}
else
{
lean_object* v_head_955_; lean_object* v_tail_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v_head_955_ = lean_ctor_get(v_a_952_, 0);
v_tail_956_ = lean_ctor_get(v_a_952_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v_a_952_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_tail_956_);
lean_inc(v_head_955_);
lean_dec(v_a_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = l_Lean_mkLevelParam(v_head_955_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v_a_953_);
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_a_953_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v_a_952_ = v_tail_956_;
v_a_953_ = v___x_962_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_966_, lean_object* v_name_967_, lean_object* v_xs_968_, lean_object* v_body_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_name_975_; lean_object* v_levelParams_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1046_; 
v_name_975_ = lean_ctor_get(v_toConstantVal_966_, 0);
v_levelParams_976_ = lean_ctor_get(v_toConstantVal_966_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_toConstantVal_966_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_toConstantVal_966_, 2);
lean_dec(v_unused_1047_);
v___x_978_ = v_toConstantVal_966_;
v_isShared_979_ = v_isSharedCheck_1046_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_levelParams_976_);
lean_inc(v_name_975_);
lean_dec(v_toConstantVal_966_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1046_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_lhs_983_; lean_object* v___x_984_; 
v___x_980_ = lean_box(0);
lean_inc(v_levelParams_976_);
v___x_981_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_976_, v___x_980_);
v___x_982_ = l_Lean_mkConst(v_name_975_, v___x_981_);
v_lhs_983_ = l_Lean_mkAppN(v___x_982_, v_xs_968_);
lean_inc_ref(v_lhs_983_);
v___x_984_ = l_Lean_Meta_mkEq(v_lhs_983_, v_body_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; uint8_t v___x_986_; uint8_t v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = 0;
v___x_987_ = 1;
v___x_988_ = 1;
v___x_989_ = l_Lean_Meta_mkForallFVars(v_xs_968_, v_a_985_, v___x_986_, v___x_987_, v___x_987_, v___x_988_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_Meta_letToHave(v_a_990_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = l_Lean_Meta_mkEqRefl(v_lhs_983_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = l_Lean_Meta_mkLambdaFVars(v_xs_968_, v_a_994_, v___x_986_, v___x_987_, v___x_986_, v___x_987_, v___x_988_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
lean_inc(v_name_967_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 2, v_a_992_);
lean_ctor_set(v___x_978_, 0, v_name_967_);
v___x_998_ = v___x_978_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_name_967_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_levelParams_976_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_a_992_);
v___x_998_ = v_reuseFailAlloc_1005_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_a_1002_; lean_object* v___x_1003_; 
lean_inc(v_name_967_);
v___x_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_999_, 0, v_name_967_);
lean_ctor_set(v___x_999_, 1, v___x_980_);
v___x_1000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v_a_996_);
lean_ctor_set(v___x_1000_, 2, v___x_999_);
v___x_1001_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_1000_, v___y_973_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = l_Lean_addDecl(v_a_1002_, v___x_986_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v___x_1004_; 
lean_dec_ref_known(v___x_1003_, 1);
v___x_1004_ = l_Lean_inferDefEqAttr(v_name_967_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_1004_;
}
else
{
lean_dec(v_name_967_);
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_a_992_);
lean_del_object(v___x_978_);
lean_dec(v_levelParams_976_);
lean_dec(v_name_967_);
v_a_1006_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_995_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_995_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_a_992_);
lean_del_object(v___x_978_);
lean_dec(v_levelParams_976_);
lean_dec(v_name_967_);
v_a_1014_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_993_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_993_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_lhs_983_);
lean_del_object(v___x_978_);
lean_dec(v_levelParams_976_);
lean_dec(v_name_967_);
v_a_1022_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_991_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_991_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref(v_lhs_983_);
lean_del_object(v___x_978_);
lean_dec(v_levelParams_976_);
lean_dec(v_name_967_);
v_a_1030_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_989_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_989_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_lhs_983_);
lean_del_object(v___x_978_);
lean_dec(v_levelParams_976_);
lean_dec(v_name_967_);
v_a_1038_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_984_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_984_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1048_, lean_object* v_name_1049_, lean_object* v_xs_1050_, lean_object* v_body_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1048_, v_name_1049_, v_xs_1050_, v_body_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v_xs_1050_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1058_, lean_object* v_info_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_toConstantVal_1065_; lean_object* v_value_1066_; lean_object* v___f_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; 
v_toConstantVal_1065_ = lean_ctor_get(v_info_1059_, 0);
lean_inc_ref(v_toConstantVal_1065_);
v_value_1066_ = lean_ctor_get(v_info_1059_, 1);
lean_inc_ref(v_value_1066_);
lean_dec_ref(v_info_1059_);
v___f_1067_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1067_, 0, v_toConstantVal_1065_);
lean_closure_set(v___f_1067_, 1, v_name_1058_);
v___x_1068_ = 1;
v___x_1069_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1066_, v___f_1067_, v___x_1068_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1070_, lean_object* v_info_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1070_, v_info_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1078_, lean_object* v_name_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1088_; lean_object* v_env_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1088_ = lean_st_ref_get(v_a_1083_);
v_env_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_env_1089_);
lean_dec(v___x_1088_);
v___x_1090_ = 0;
lean_inc(v_declName_1078_);
v___x_1091_ = l_Lean_Environment_find_x3f(v_env_1089_, v_declName_1078_, v___x_1090_);
if (lean_obj_tag(v___x_1091_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1119_; 
v_val_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1119_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1119_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
if (lean_obj_tag(v_val_1092_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_val_1096_ = lean_ctor_get(v_val_1092_, 0);
lean_inc_ref(v_val_1096_);
lean_dec_ref_known(v_val_1092_, 1);
lean_inc_n(v_name_1079_, 2);
v___x_1097_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1097_, 0, v_name_1079_);
lean_closure_set(v___x_1097_, 1, v_val_1096_);
lean_inc(v_declName_1078_);
v___x_1098_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1098_, 0, lean_box(0));
lean_closure_set(v___x_1098_, 1, v_declName_1078_);
lean_closure_set(v___x_1098_, 2, v___x_1097_);
v___x_1099_ = l_Lean_Meta_realizeConst(v_declName_1078_, v_name_1079_, v___x_1098_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1109_; 
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v___x_1099_, 0);
lean_dec(v_unused_1110_);
v___x_1101_ = v___x_1099_;
v_isShared_1102_ = v_isSharedCheck_1109_;
goto v_resetjp_1100_;
}
else
{
lean_dec(v___x_1099_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1109_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_name_1079_);
v___x_1104_ = v___x_1094_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_name_1079_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
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
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_del_object(v___x_1094_);
lean_dec(v_name_1079_);
v_a_1111_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1099_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1099_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_del_object(v___x_1094_);
lean_dec(v_val_1092_);
lean_dec(v_name_1079_);
lean_dec(v_declName_1078_);
goto v___jp_1085_;
}
}
}
else
{
lean_dec(v___x_1091_);
lean_dec(v_name_1079_);
lean_dec(v_declName_1078_);
goto v___jp_1085_;
}
v___jp_1085_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1120_, lean_object* v_name_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1120_, v_name_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1128_, lean_object* v_vals_1129_, lean_object* v_i_1130_, lean_object* v_k_1131_){
_start:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_array_get_size(v_keys_1128_);
v___x_1133_ = lean_nat_dec_lt(v_i_1130_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v_i_1130_);
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
lean_object* v_k_x27_1135_; uint8_t v___x_1136_; 
v_k_x27_1135_ = lean_array_fget_borrowed(v_keys_1128_, v_i_1130_);
v___x_1136_ = lean_name_eq(v_k_1131_, v_k_x27_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_i_1130_, v___x_1137_);
lean_dec(v_i_1130_);
v_i_1130_ = v___x_1138_;
goto _start;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_array_fget_borrowed(v_vals_1129_, v_i_1130_);
lean_dec(v_i_1130_);
lean_inc(v___x_1140_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1142_, lean_object* v_vals_1143_, lean_object* v_i_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1142_, v_vals_1143_, v_i_1144_, v_k_1145_);
lean_dec(v_k_1145_);
lean_dec_ref(v_vals_1143_);
lean_dec_ref(v_keys_1142_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1147_, size_t v_x_1148_, lean_object* v_x_1149_){
_start:
{
if (lean_obj_tag(v_x_1147_) == 0)
{
lean_object* v_es_1150_; lean_object* v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v_j_1154_; lean_object* v___x_1155_; 
v_es_1150_ = lean_ctor_get(v_x_1147_, 0);
v___x_1151_ = lean_box(2);
v___x_1152_ = ((size_t)31ULL);
v___x_1153_ = lean_usize_land(v_x_1148_, v___x_1152_);
v_j_1154_ = lean_usize_to_nat(v___x_1153_);
v___x_1155_ = lean_array_get_borrowed(v___x_1151_, v_es_1150_, v_j_1154_);
lean_dec(v_j_1154_);
switch(lean_obj_tag(v___x_1155_))
{
case 0:
{
lean_object* v_key_1156_; lean_object* v_val_1157_; uint8_t v___x_1158_; 
v_key_1156_ = lean_ctor_get(v___x_1155_, 0);
v_val_1157_ = lean_ctor_get(v___x_1155_, 1);
v___x_1158_ = lean_name_eq(v_x_1149_, v_key_1156_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; 
lean_inc(v_val_1157_);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_val_1157_);
return v___x_1160_;
}
}
case 1:
{
lean_object* v_node_1161_; size_t v___x_1162_; size_t v___x_1163_; 
v_node_1161_ = lean_ctor_get(v___x_1155_, 0);
v___x_1162_ = ((size_t)5ULL);
v___x_1163_ = lean_usize_shift_right(v_x_1148_, v___x_1162_);
v_x_1147_ = v_node_1161_;
v_x_1148_ = v___x_1163_;
goto _start;
}
default: 
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_box(0);
return v___x_1165_;
}
}
}
else
{
lean_object* v_ks_1166_; lean_object* v_vs_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_ks_1166_ = lean_ctor_get(v_x_1147_, 0);
v_vs_1167_ = lean_ctor_get(v_x_1147_, 1);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1166_, v_vs_1167_, v___x_1168_, v_x_1149_);
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
size_t v_x_344__boxed_1173_; lean_object* v_res_1174_; 
v_x_344__boxed_1173_ = lean_unbox_usize(v_x_1171_);
lean_dec(v_x_1171_);
v_res_1174_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1170_, v_x_344__boxed_1173_, v_x_1172_);
lean_dec(v_x_1172_);
lean_dec_ref(v_x_1170_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
uint64_t v___y_1178_; 
if (lean_obj_tag(v_x_1176_) == 0)
{
uint64_t v___x_1181_; 
v___x_1181_ = 1723ULL;
v___y_1178_ = v___x_1181_;
goto v___jp_1177_;
}
else
{
uint64_t v_hash_1182_; 
v_hash_1182_ = lean_ctor_get_uint64(v_x_1176_, sizeof(void*)*2);
v___y_1178_ = v_hash_1182_;
goto v___jp_1177_;
}
v___jp_1177_:
{
size_t v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_uint64_to_usize(v___y_1178_);
v___x_1180_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1175_, v___x_1179_, v_x_1176_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1183_, v_x_1184_);
lean_dec(v_x_1184_);
lean_dec_ref(v_x_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v___x_1192_; lean_object* v_asyncMode_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1189_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1190_ = lean_st_ref_get(v_a_1187_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1193_ = lean_ctor_get(v___x_1192_, 2);
v___x_1194_ = lean_box(0);
v___x_1195_ = 0;
v___x_1196_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1189_, v___x_1192_, v_env_1191_, v_asyncMode_1193_, v___x_1194_, v___x_1195_);
v___x_1197_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1196_, v_thmName_1186_);
lean_dec(v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec(v_thmName_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1203_, v_a_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1208_, v_a_1209_, v_a_1210_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_thmName_1208_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1214_, v_x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1217_, lean_object* v_x_1218_, lean_object* v_x_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1217_, v_x_1218_, v_x_1219_);
lean_dec(v_x_1219_);
lean_dec_ref(v_x_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1221_, lean_object* v_x_1222_, size_t v_x_1223_, lean_object* v_x_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1222_, v_x_1223_, v_x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_, lean_object* v_x_1229_){
_start:
{
size_t v_x_439__boxed_1230_; lean_object* v_res_1231_; 
v_x_439__boxed_1230_ = lean_unbox_usize(v_x_1228_);
lean_dec(v_x_1228_);
v_res_1231_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1226_, v_x_1227_, v_x_439__boxed_1230_, v_x_1229_);
lean_dec(v_x_1229_);
lean_dec_ref(v_x_1227_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1232_, lean_object* v_keys_1233_, lean_object* v_vals_1234_, lean_object* v_heq_1235_, lean_object* v_i_1236_, lean_object* v_k_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1233_, v_vals_1234_, v_i_1236_, v_k_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1239_, lean_object* v_keys_1240_, lean_object* v_vals_1241_, lean_object* v_heq_1242_, lean_object* v_i_1243_, lean_object* v_k_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1239_, v_keys_1240_, v_vals_1241_, v_heq_1242_, v_i_1243_, v_k_1244_);
lean_dec(v_k_1244_);
lean_dec_ref(v_vals_1241_);
lean_dec_ref(v_keys_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1246_, lean_object* v_i_1247_, lean_object* v_k_1248_){
_start:
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = lean_array_get_size(v_keys_1246_);
v___x_1250_ = lean_nat_dec_lt(v_i_1247_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v_i_1247_);
return v___x_1250_;
}
else
{
lean_object* v_k_x27_1251_; uint8_t v___x_1252_; 
v_k_x27_1251_ = lean_array_fget_borrowed(v_keys_1246_, v_i_1247_);
v___x_1252_ = lean_name_eq(v_k_1248_, v_k_x27_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_nat_add(v_i_1247_, v___x_1253_);
lean_dec(v_i_1247_);
v_i_1247_ = v___x_1254_;
goto _start;
}
else
{
lean_dec(v_i_1247_);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1256_, lean_object* v_i_1257_, lean_object* v_k_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1256_, v_i_1257_, v_k_1258_);
lean_dec(v_k_1258_);
lean_dec_ref(v_keys_1256_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1261_, size_t v_x_1262_, lean_object* v_x_1263_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
lean_object* v_es_1264_; lean_object* v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; lean_object* v_j_1268_; lean_object* v___x_1269_; 
v_es_1264_ = lean_ctor_get(v_x_1261_, 0);
v___x_1265_ = lean_box(2);
v___x_1266_ = ((size_t)31ULL);
v___x_1267_ = lean_usize_land(v_x_1262_, v___x_1266_);
v_j_1268_ = lean_usize_to_nat(v___x_1267_);
v___x_1269_ = lean_array_get_borrowed(v___x_1265_, v_es_1264_, v_j_1268_);
lean_dec(v_j_1268_);
switch(lean_obj_tag(v___x_1269_))
{
case 0:
{
lean_object* v_key_1270_; uint8_t v___x_1271_; 
v_key_1270_ = lean_ctor_get(v___x_1269_, 0);
v___x_1271_ = lean_name_eq(v_x_1263_, v_key_1270_);
return v___x_1271_;
}
case 1:
{
lean_object* v_node_1272_; size_t v___x_1273_; size_t v___x_1274_; 
v_node_1272_ = lean_ctor_get(v___x_1269_, 0);
v___x_1273_ = ((size_t)5ULL);
v___x_1274_ = lean_usize_shift_right(v_x_1262_, v___x_1273_);
v_x_1261_ = v_node_1272_;
v_x_1262_ = v___x_1274_;
goto _start;
}
default: 
{
uint8_t v___x_1276_; 
v___x_1276_ = 0;
return v___x_1276_;
}
}
}
else
{
lean_object* v_ks_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_ks_1277_ = lean_ctor_get(v_x_1261_, 0);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1277_, v___x_1278_, v_x_1263_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
size_t v_x_328__boxed_1283_; uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_x_328__boxed_1283_ = lean_unbox_usize(v_x_1281_);
lean_dec(v_x_1281_);
v_res_1284_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1280_, v_x_328__boxed_1283_, v_x_1282_);
lean_dec(v_x_1282_);
lean_dec_ref(v_x_1280_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1286_, lean_object* v_x_1287_){
_start:
{
uint64_t v___y_1289_; 
if (lean_obj_tag(v_x_1287_) == 0)
{
uint64_t v___x_1292_; 
v___x_1292_ = 1723ULL;
v___y_1289_ = v___x_1292_;
goto v___jp_1288_;
}
else
{
uint64_t v_hash_1293_; 
v_hash_1293_ = lean_ctor_get_uint64(v_x_1287_, sizeof(void*)*2);
v___y_1289_ = v_hash_1293_;
goto v___jp_1288_;
}
v___jp_1288_:
{
size_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_uint64_to_usize(v___y_1289_);
v___x_1291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1286_, v___x_1290_, v_x_1287_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1294_, v_x_1295_);
lean_dec(v_x_1295_);
lean_dec_ref(v_x_1294_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_env_1303_; lean_object* v___x_1304_; lean_object* v_asyncMode_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1301_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1302_ = lean_st_ref_get(v_a_1299_);
v_env_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_ref(v_env_1303_);
lean_dec(v___x_1302_);
v___x_1304_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1305_ = lean_ctor_get(v___x_1304_, 2);
v___x_1306_ = lean_box(0);
v___x_1307_ = 0;
v___x_1308_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1301_, v___x_1304_, v_env_1303_, v_asyncMode_1305_, v___x_1306_, v___x_1307_);
v___x_1309_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1308_, v_thmName_1298_);
lean_dec(v___x_1308_);
v___x_1310_ = lean_box(v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec(v_thmName_1312_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1316_, v_a_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Meta_isEqnThm(v_thmName_1321_, v_a_1322_, v_a_1323_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_thmName_1321_);
return v_res_1325_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1327_, v_x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_){
_start:
{
uint8_t v_res_1333_; lean_object* v_r_1334_; 
v_res_1333_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1330_, v_x_1331_, v_x_1332_);
lean_dec(v_x_1332_);
lean_dec_ref(v_x_1331_);
v_r_1334_ = lean_box(v_res_1333_);
return v_r_1334_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1335_, lean_object* v_x_1336_, size_t v_x_1337_, lean_object* v_x_1338_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1336_, v_x_1337_, v_x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
size_t v_x_419__boxed_1344_; uint8_t v_res_1345_; lean_object* v_r_1346_; 
v_x_419__boxed_1344_ = lean_unbox_usize(v_x_1342_);
lean_dec(v_x_1342_);
v_res_1345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1340_, v_x_1341_, v_x_419__boxed_1344_, v_x_1343_);
lean_dec(v_x_1343_);
lean_dec_ref(v_x_1341_);
v_r_1346_ = lean_box(v_res_1345_);
return v_r_1346_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1347_, lean_object* v_keys_1348_, lean_object* v_vals_1349_, lean_object* v_heq_1350_, lean_object* v_i_1351_, lean_object* v_k_1352_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1348_, v_i_1351_, v_k_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1354_, lean_object* v_keys_1355_, lean_object* v_vals_1356_, lean_object* v_heq_1357_, lean_object* v_i_1358_, lean_object* v_k_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1354_, v_keys_1355_, v_vals_1356_, v_heq_1357_, v_i_1358_, v_k_1359_);
lean_dec(v_k_1359_);
lean_dec_ref(v_vals_1356_);
lean_dec_ref(v_keys_1355_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1362_, lean_object* v_msg_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_panic_fn_borrowed(v_x1_1362_, v_msg_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1365_, lean_object* v_msg_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1365_, v_msg_1366_);
lean_dec_ref(v_x1_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v_ks_1372_; lean_object* v_vs_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1397_; 
v_ks_1372_ = lean_ctor_get(v_x_1368_, 0);
v_vs_1373_ = lean_ctor_get(v_x_1368_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_x_1368_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1375_ = v_x_1368_;
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_vs_1373_);
lean_inc(v_ks_1372_);
lean_dec(v_x_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_ks_1372_);
v___x_1378_ = lean_nat_dec_lt(v_x_1369_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec(v_x_1369_);
v___x_1379_ = lean_array_push(v_ks_1372_, v_x_1370_);
v___x_1380_ = lean_array_push(v_vs_1373_, v_x_1371_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1380_);
lean_ctor_set(v___x_1375_, 0, v___x_1379_);
v___x_1382_ = v___x_1375_;
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
else
{
lean_object* v_k_x27_1384_; uint8_t v___x_1385_; 
v_k_x27_1384_ = lean_array_fget_borrowed(v_ks_1372_, v_x_1369_);
v___x_1385_ = lean_name_eq(v_x_1370_, v_k_x27_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1387_; 
if (v_isShared_1376_ == 0)
{
v___x_1387_ = v___x_1375_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_ks_1372_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_vs_1373_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_nat_add(v_x_1369_, v___x_1388_);
lean_dec(v_x_1369_);
v_x_1368_ = v___x_1387_;
v_x_1369_ = v___x_1389_;
goto _start;
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = lean_array_fset(v_ks_1372_, v_x_1369_, v_x_1370_);
v___x_1393_ = lean_array_fset(v_vs_1373_, v_x_1369_, v_x_1371_);
lean_dec(v_x_1369_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1393_);
lean_ctor_set(v___x_1375_, 0, v___x_1392_);
v___x_1395_ = v___x_1375_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1398_, lean_object* v_k_1399_, lean_object* v_v_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1398_, v___x_1401_, v_k_1399_, v_v_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1404_, size_t v_x_1405_, size_t v_x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1404_) == 0)
{
lean_object* v_es_1409_; size_t v___x_1410_; size_t v___x_1411_; lean_object* v_j_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_es_1409_ = lean_ctor_get(v_x_1404_, 0);
v___x_1410_ = ((size_t)31ULL);
v___x_1411_ = lean_usize_land(v_x_1405_, v___x_1410_);
v_j_1412_ = lean_usize_to_nat(v___x_1411_);
v___x_1413_ = lean_array_get_size(v_es_1409_);
v___x_1414_ = lean_nat_dec_lt(v_j_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_dec(v_j_1412_);
lean_dec(v_x_1408_);
lean_dec(v_x_1407_);
return v_x_1404_;
}
else
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1453_; 
lean_inc_ref(v_es_1409_);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_x_1404_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_x_1404_, 0);
lean_dec(v_unused_1454_);
v___x_1416_ = v_x_1404_;
v_isShared_1417_ = v_isSharedCheck_1453_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v_x_1404_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1453_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_v_1418_; lean_object* v___x_1419_; lean_object* v_xs_x27_1420_; lean_object* v___y_1422_; 
v_v_1418_ = lean_array_fget(v_es_1409_, v_j_1412_);
v___x_1419_ = lean_box(0);
v_xs_x27_1420_ = lean_array_fset(v_es_1409_, v_j_1412_, v___x_1419_);
switch(lean_obj_tag(v_v_1418_))
{
case 0:
{
lean_object* v_key_1427_; lean_object* v_val_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1438_; 
v_key_1427_ = lean_ctor_get(v_v_1418_, 0);
v_val_1428_ = lean_ctor_get(v_v_1418_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_v_1418_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1430_ = v_v_1418_;
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_val_1428_);
lean_inc(v_key_1427_);
lean_dec(v_v_1418_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_name_eq(v_x_1407_, v_key_1427_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_del_object(v___x_1430_);
v___x_1433_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1427_, v_val_1428_, v_x_1407_, v_x_1408_);
v___x_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
v___y_1422_ = v___x_1434_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1436_; 
lean_dec(v_val_1428_);
lean_dec(v_key_1427_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v_x_1408_);
lean_ctor_set(v___x_1430_, 0, v_x_1407_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_x_1407_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_x_1408_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v___y_1422_ = v___x_1436_;
goto v___jp_1421_;
}
}
}
}
case 1:
{
lean_object* v_node_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1451_; 
v_node_1439_ = lean_ctor_get(v_v_1418_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_v_1418_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1441_ = v_v_1418_;
v_isShared_1442_ = v_isSharedCheck_1451_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_node_1439_);
lean_dec(v_v_1418_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1451_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
size_t v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1443_ = ((size_t)5ULL);
v___x_1444_ = lean_usize_shift_right(v_x_1405_, v___x_1443_);
v___x_1445_ = ((size_t)1ULL);
v___x_1446_ = lean_usize_add(v_x_1406_, v___x_1445_);
v___x_1447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1439_, v___x_1444_, v___x_1446_, v_x_1407_, v_x_1408_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1447_);
v___x_1449_ = v___x_1441_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
v___y_1422_ = v___x_1449_;
goto v___jp_1421_;
}
}
}
default: 
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_x_1407_);
lean_ctor_set(v___x_1452_, 1, v_x_1408_);
v___y_1422_ = v___x_1452_;
goto v___jp_1421_;
}
}
v___jp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_array_fset(v_xs_x27_1420_, v_j_1412_, v___y_1422_);
lean_dec(v_j_1412_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1423_);
v___x_1425_ = v___x_1416_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
else
{
lean_object* v_ks_1455_; lean_object* v_vs_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1474_; 
v_ks_1455_ = lean_ctor_get(v_x_1404_, 0);
v_vs_1456_ = lean_ctor_get(v_x_1404_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_x_1404_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1458_ = v_x_1404_;
v_isShared_1459_ = v_isSharedCheck_1474_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_vs_1456_);
lean_inc(v_ks_1455_);
lean_dec(v_x_1404_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1474_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_ks_1455_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_vs_1456_);
v___x_1461_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v_newNode_1462_; size_t v___x_1463_; uint8_t v___x_1464_; 
v_newNode_1462_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1461_, v_x_1407_, v_x_1408_);
v___x_1463_ = ((size_t)7ULL);
v___x_1464_ = lean_usize_dec_le(v___x_1463_, v_x_1406_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1465_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1462_);
v___x_1466_ = lean_unsigned_to_nat(4u);
v___x_1467_ = lean_nat_dec_lt(v___x_1465_, v___x_1466_);
lean_dec(v___x_1465_);
if (v___x_1467_ == 0)
{
lean_object* v_ks_1468_; lean_object* v_vs_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_ks_1468_ = lean_ctor_get(v_newNode_1462_, 0);
lean_inc_ref(v_ks_1468_);
v_vs_1469_ = lean_ctor_get(v_newNode_1462_, 1);
lean_inc_ref(v_vs_1469_);
lean_dec_ref(v_newNode_1462_);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1472_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1406_, v_ks_1468_, v_vs_1469_, v___x_1470_, v___x_1471_);
lean_dec_ref(v_vs_1469_);
lean_dec_ref(v_ks_1468_);
return v___x_1472_;
}
else
{
return v_newNode_1462_;
}
}
else
{
return v_newNode_1462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_i_1478_, lean_object* v_entries_1479_){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_array_get_size(v_keys_1476_);
v___x_1481_ = lean_nat_dec_lt(v_i_1478_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_dec(v_i_1478_);
return v_entries_1479_;
}
else
{
lean_object* v_k_1482_; lean_object* v_v_1483_; uint64_t v___y_1485_; 
v_k_1482_ = lean_array_fget_borrowed(v_keys_1476_, v_i_1478_);
v_v_1483_ = lean_array_fget_borrowed(v_vals_1477_, v_i_1478_);
if (lean_obj_tag(v_k_1482_) == 0)
{
uint64_t v___x_1496_; 
v___x_1496_ = 1723ULL;
v___y_1485_ = v___x_1496_;
goto v___jp_1484_;
}
else
{
uint64_t v_hash_1497_; 
v_hash_1497_ = lean_ctor_get_uint64(v_k_1482_, sizeof(void*)*2);
v___y_1485_ = v_hash_1497_;
goto v___jp_1484_;
}
v___jp_1484_:
{
size_t v_h_1486_; size_t v___x_1487_; lean_object* v___x_1488_; size_t v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; size_t v_h_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_h_1486_ = lean_uint64_to_usize(v___y_1485_);
v___x_1487_ = ((size_t)5ULL);
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = ((size_t)1ULL);
v___x_1490_ = lean_usize_sub(v_depth_1475_, v___x_1489_);
v___x_1491_ = lean_usize_mul(v___x_1487_, v___x_1490_);
v_h_1492_ = lean_usize_shift_right(v_h_1486_, v___x_1491_);
v___x_1493_ = lean_nat_add(v_i_1478_, v___x_1488_);
lean_dec(v_i_1478_);
lean_inc(v_v_1483_);
lean_inc(v_k_1482_);
v___x_1494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1479_, v_h_1492_, v_depth_1475_, v_k_1482_, v_v_1483_);
v_i_1478_ = v___x_1493_;
v_entries_1479_ = v___x_1494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1498_, lean_object* v_keys_1499_, lean_object* v_vals_1500_, lean_object* v_i_1501_, lean_object* v_entries_1502_){
_start:
{
size_t v_depth_boxed_1503_; lean_object* v_res_1504_; 
v_depth_boxed_1503_ = lean_unbox_usize(v_depth_1498_);
lean_dec(v_depth_1498_);
v_res_1504_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1503_, v_keys_1499_, v_vals_1500_, v_i_1501_, v_entries_1502_);
lean_dec_ref(v_vals_1500_);
lean_dec_ref(v_keys_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
size_t v_x_905__boxed_1510_; size_t v_x_906__boxed_1511_; lean_object* v_res_1512_; 
v_x_905__boxed_1510_ = lean_unbox_usize(v_x_1506_);
lean_dec(v_x_1506_);
v_x_906__boxed_1511_ = lean_unbox_usize(v_x_1507_);
lean_dec(v_x_1507_);
v_res_1512_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1505_, v_x_905__boxed_1510_, v_x_906__boxed_1511_, v_x_1508_, v_x_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
uint64_t v___y_1517_; 
if (lean_obj_tag(v_x_1514_) == 0)
{
uint64_t v___x_1521_; 
v___x_1521_ = 1723ULL;
v___y_1517_ = v___x_1521_;
goto v___jp_1516_;
}
else
{
uint64_t v_hash_1522_; 
v_hash_1522_ = lean_ctor_get_uint64(v_x_1514_, sizeof(void*)*2);
v___y_1517_ = v_hash_1522_;
goto v___jp_1516_;
}
v___jp_1516_:
{
size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = lean_uint64_to_usize(v___y_1517_);
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1513_, v___x_1518_, v___x_1519_, v_x_1514_, v_x_1515_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1528_, lean_object* v_as_1529_, size_t v_i_1530_, size_t v_stop_1531_, lean_object* v_b_1532_){
_start:
{
lean_object* v___y_1534_; uint8_t v___x_1538_; 
v___x_1538_ = lean_usize_dec_eq(v_i_1530_, v_stop_1531_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_array_uget_borrowed(v_as_1529_, v_i_1530_);
v___x_1540_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1532_, v___x_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_inc(v_declName_1528_);
lean_inc(v___x_1539_);
v___x_1541_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1532_, v___x_1539_, v_declName_1528_);
v___y_1534_ = v___x_1541_;
goto v___jp_1533_;
}
else
{
lean_object* v_val_1542_; uint8_t v___x_1543_; 
v_val_1542_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1543_ = lean_name_eq(v_val_1542_, v_declName_1528_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1544_ = 1;
v___x_1545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1547_ = lean_unsigned_to_nat(231u);
v___x_1548_ = lean_unsigned_to_nat(10u);
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1539_);
v___x_1550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1539_, v___x_1544_);
v___x_1551_ = lean_string_append(v___x_1549_, v___x_1550_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1553_ = lean_string_append(v___x_1551_, v___x_1552_);
v___x_1554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1542_, v___x_1544_);
v___x_1555_ = lean_string_append(v___x_1553_, v___x_1554_);
lean_dec_ref(v___x_1554_);
v___x_1556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1557_ = lean_string_append(v___x_1555_, v___x_1556_);
v___x_1558_ = l_mkPanicMessageWithDecl(v___x_1545_, v___x_1546_, v___x_1547_, v___x_1548_, v___x_1557_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = lean_panic_fn_borrowed(v_b_1532_, v___x_1558_);
lean_dec_ref(v_b_1532_);
v___y_1534_ = v___x_1559_;
goto v___jp_1533_;
}
else
{
lean_dec(v_val_1542_);
v___y_1534_ = v_b_1532_;
goto v___jp_1533_;
}
}
}
else
{
lean_dec(v_declName_1528_);
return v_b_1532_;
}
v___jp_1533_:
{
size_t v___x_1535_; size_t v___x_1536_; 
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_add(v_i_1530_, v___x_1535_);
v_i_1530_ = v___x_1536_;
v_b_1532_ = v___y_1534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1560_, lean_object* v_as_1561_, lean_object* v_i_1562_, lean_object* v_stop_1563_, lean_object* v_b_1564_){
_start:
{
size_t v_i_boxed_1565_; size_t v_stop_boxed_1566_; lean_object* v_res_1567_; 
v_i_boxed_1565_ = lean_unbox_usize(v_i_1562_);
lean_dec(v_i_1562_);
v_stop_boxed_1566_ = lean_unbox_usize(v_stop_1563_);
lean_dec(v_stop_1563_);
v_res_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1560_, v_as_1561_, v_i_boxed_1565_, v_stop_boxed_1566_, v_b_1564_);
lean_dec_ref(v_as_1561_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1568_, lean_object* v_declName_1569_, lean_object* v_s_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = lean_array_get_size(v_eqThms_1568_);
v___x_1573_ = lean_nat_dec_lt(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_dec(v_declName_1569_);
return v_s_1570_;
}
else
{
size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = lean_usize_of_nat(v___x_1572_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1569_, v_eqThms_1568_, v___x_1574_, v___x_1575_, v_s_1570_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1577_, lean_object* v_declName_1578_, lean_object* v_s_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1577_, v_declName_1578_, v_s_1579_);
lean_dec_ref(v_eqThms_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1581_, lean_object* v_eqThms_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___f_1585_; lean_object* v___x_1586_; lean_object* v_env_1587_; lean_object* v_nextMacroScope_1588_; lean_object* v_ngen_1589_; lean_object* v_auxDeclNGen_1590_; lean_object* v_traceState_1591_; lean_object* v_recordedDeps_1592_; lean_object* v_messages_1593_; lean_object* v_infoState_1594_; lean_object* v_snapshotTasks_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1611_; 
v___f_1585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1585_, 0, v_eqThms_1582_);
lean_closure_set(v___f_1585_, 1, v_declName_1581_);
v___x_1586_ = lean_st_ref_take(v_a_1583_);
v_env_1587_ = lean_ctor_get(v___x_1586_, 0);
v_nextMacroScope_1588_ = lean_ctor_get(v___x_1586_, 1);
v_ngen_1589_ = lean_ctor_get(v___x_1586_, 2);
v_auxDeclNGen_1590_ = lean_ctor_get(v___x_1586_, 3);
v_traceState_1591_ = lean_ctor_get(v___x_1586_, 4);
v_recordedDeps_1592_ = lean_ctor_get(v___x_1586_, 6);
v_messages_1593_ = lean_ctor_get(v___x_1586_, 7);
v_infoState_1594_ = lean_ctor_get(v___x_1586_, 8);
v_snapshotTasks_1595_ = lean_ctor_get(v___x_1586_, 9);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1586_, 5);
lean_dec(v_unused_1612_);
v___x_1597_ = v___x_1586_;
v_isShared_1598_ = v_isSharedCheck_1611_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_snapshotTasks_1595_);
lean_inc(v_infoState_1594_);
lean_inc(v_messages_1593_);
lean_inc(v_recordedDeps_1592_);
lean_inc(v_traceState_1591_);
lean_inc(v_auxDeclNGen_1590_);
lean_inc(v_ngen_1589_);
lean_inc(v_nextMacroScope_1588_);
lean_inc(v_env_1587_);
lean_dec(v___x_1586_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1611_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v_asyncMode_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1599_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1600_ = lean_ctor_get(v___x_1599_, 2);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_box(0);
v___x_1603_ = 1;
v___x_1604_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1599_, v_env_1587_, v___f_1585_, v_asyncMode_1600_, v___x_1602_, v___x_1603_);
v___x_1605_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 5, v___x_1605_);
lean_ctor_set(v___x_1597_, 0, v___x_1604_);
v___x_1607_ = v___x_1597_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_nextMacroScope_1588_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_ngen_1589_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_auxDeclNGen_1590_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_traceState_1591_);
lean_ctor_set(v_reuseFailAlloc_1610_, 5, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1610_, 6, v_recordedDeps_1592_);
lean_ctor_set(v_reuseFailAlloc_1610_, 7, v_messages_1593_);
lean_ctor_set(v_reuseFailAlloc_1610_, 8, v_infoState_1594_);
lean_ctor_set(v_reuseFailAlloc_1610_, 9, v_snapshotTasks_1595_);
v___x_1607_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_st_ref_put(v_a_1583_, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1601_);
return v___x_1609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1613_, lean_object* v_eqThms_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1613_, v_eqThms_1614_, v_a_1615_);
lean_dec(v_a_1615_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1618_, lean_object* v_eqThms_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1618_, v_eqThms_1619_, v_a_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1624_, lean_object* v_eqThms_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1624_, v_eqThms_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1631_, v_x_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1635_, lean_object* v_x_1636_, size_t v_x_1637_, size_t v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1636_, v_x_1637_, v_x_1638_, v_x_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
size_t v_x_1219__boxed_1648_; size_t v_x_1220__boxed_1649_; lean_object* v_res_1650_; 
v_x_1219__boxed_1648_ = lean_unbox_usize(v_x_1644_);
lean_dec(v_x_1644_);
v_x_1220__boxed_1649_ = lean_unbox_usize(v_x_1645_);
lean_dec(v_x_1645_);
v_res_1650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1642_, v_x_1643_, v_x_1219__boxed_1648_, v_x_1220__boxed_1649_, v_x_1646_, v_x_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1651_, lean_object* v_n_1652_, lean_object* v_k_1653_, lean_object* v_v_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1652_, v_k_1653_, v_v_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1656_, size_t v_depth_1657_, lean_object* v_keys_1658_, lean_object* v_vals_1659_, lean_object* v_heq_1660_, lean_object* v_i_1661_, lean_object* v_entries_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1657_, v_keys_1658_, v_vals_1659_, v_i_1661_, v_entries_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_depth_1665_, lean_object* v_keys_1666_, lean_object* v_vals_1667_, lean_object* v_heq_1668_, lean_object* v_i_1669_, lean_object* v_entries_1670_){
_start:
{
size_t v_depth_boxed_1671_; lean_object* v_res_1672_; 
v_depth_boxed_1671_ = lean_unbox_usize(v_depth_1665_);
lean_dec(v_depth_1665_);
v_res_1672_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1664_, v_depth_boxed_1671_, v_keys_1666_, v_vals_1667_, v_heq_1668_, v_i_1669_, v_entries_1670_);
lean_dec_ref(v_vals_1667_);
lean_dec_ref(v_keys_1666_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1674_, v_x_1675_, v_x_1676_, v_x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1679_, lean_object* v_env_1680_, lean_object* v_idx_1681_, lean_object* v_eqs_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v_nextEq_1689_; uint8_t v___x_1690_; 
v___x_1684_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1685_ = lean_unsigned_to_nat(1u);
v___x_1686_ = lean_nat_add(v_idx_1681_, v___x_1685_);
lean_dec(v_idx_1681_);
lean_inc(v___x_1686_);
v___x_1687_ = l_Nat_reprFast(v___x_1686_);
v___x_1688_ = lean_string_append(v___x_1684_, v___x_1687_);
lean_dec_ref(v___x_1687_);
lean_inc(v_declName_1679_);
lean_inc_ref(v_env_1680_);
v_nextEq_1689_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1680_, v_declName_1679_, v___x_1688_);
v___x_1690_ = l_Lean_Environment_containsOnBranch(v_env_1680_, v_nextEq_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_dec(v_nextEq_1689_);
lean_dec(v___x_1686_);
lean_dec_ref(v_env_1680_);
lean_dec(v_declName_1679_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_eqs_1682_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_array_push(v_eqs_1682_, v_nextEq_1689_);
v_idx_1681_ = v___x_1686_;
v_eqs_1682_ = v___x_1692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1694_, lean_object* v_env_1695_, lean_object* v_idx_1696_, lean_object* v_eqs_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1694_, v_env_1695_, v_idx_1696_, v_eqs_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1700_, lean_object* v_env_1701_, lean_object* v_idx_1702_, lean_object* v_eqs_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1700_, v_env_1701_, v_idx_1702_, v_eqs_1703_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1710_, lean_object* v_env_1711_, lean_object* v_idx_1712_, lean_object* v_eqs_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1710_, v_env_1711_, v_idx_1712_, v_eqs_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v_env_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; uint8_t v___x_1728_; 
v___x_1723_ = lean_st_ref_get(v_a_1721_);
v_env_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_ref_n(v_env_1724_, 3);
lean_dec(v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1720_);
v___x_1726_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1724_, v_declName_1720_, v___x_1725_);
v___x_1727_ = 1;
lean_inc(v___x_1726_);
v___x_1728_ = l_Lean_Environment_contains(v_env_1724_, v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v___x_1726_);
lean_dec_ref(v_env_1724_);
lean_dec(v_declName_1720_);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_mk_empty_array_with_capacity(v___x_1731_);
v___x_1733_ = lean_array_push(v___x_1732_, v___x_1726_);
lean_inc(v_declName_1720_);
v___x_1734_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1720_, v_env_1724_, v___x_1731_, v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1744_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_n(v_a_1735_, 2);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1720_, v_a_1735_, v_a_1721_);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v___x_1736_, 0);
lean_dec(v_unused_1745_);
v___x_1738_ = v___x_1736_;
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v___x_1736_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_a_1735_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1740_);
v___x_1742_ = v___x_1738_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_declName_1720_);
v_a_1746_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1734_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1734_);
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
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1754_, v_a_1755_);
lean_dec(v_a_1755_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1758_, v_a_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_alreadyGenerated_x3f(v_declName_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1772_, lean_object* v_localInsts_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1772_, v_localInsts_1773_, v_x_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
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
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1780_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1780_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1797_, lean_object* v_localInsts_1798_, lean_object* v_x_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1797_, v_localInsts_1798_, v_x_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1806_, lean_object* v_lctx_1807_, lean_object* v_localInsts_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1807_, v_localInsts_1808_, v_x_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1816_, lean_object* v_lctx_1817_, lean_object* v_localInsts_1818_, lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1816_, v_lctx_1817_, v_localInsts_1818_, v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1829_, lean_object* v_as_x27_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
if (lean_obj_tag(v_as_x27_1830_) == 0)
{
lean_object* v___x_1837_; 
lean_dec(v_declName_1829_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v_b_1831_);
return v___x_1837_;
}
else
{
lean_object* v_head_1838_; lean_object* v_tail_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec_ref(v_b_1831_);
v_head_1838_ = lean_ctor_get(v_as_x27_1830_, 0);
v_tail_1839_ = lean_ctor_get(v_as_x27_1830_, 1);
v___x_1840_ = lean_box(0);
v___x_1841_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1838_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v_declName_1829_);
v___x_1842_ = lean_apply_6(v_head_1838_, v_declName_1829_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, lean_box(0));
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
if (lean_obj_tag(v_a_1843_) == 1)
{
lean_object* v_val_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1854_; 
v_val_1844_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_val_1844_);
v___x_1845_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1829_, v_val_1844_, v___y_1835_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v___x_1845_, 0);
lean_dec(v_unused_1855_);
v___x_1847_ = v___x_1845_;
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
else
{
lean_dec(v___x_1845_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1843_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1840_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
lean_dec(v_a_1843_);
v_as_x27_1830_ = v_tail_1839_;
v_b_1831_ = v___x_1841_;
goto _start;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_declName_1829_);
v_a_1857_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1842_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1842_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1865_, lean_object* v_as_x27_1866_, lean_object* v_b_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1865_, v_as_x27_1866_, v_b_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v_as_x27_1866_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
lean_inc(v_declName_1874_);
v___x_1880_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1918_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1918_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1918_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_unbox(v_a_1881_);
lean_dec(v_a_1881_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_dec(v_declName_1874_);
v___x_1886_ = lean_box(0);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
else
{
lean_object* v___x_1890_; 
lean_del_object(v___x_1883_);
lean_inc(v_declName_1874_);
v___x_1890_ = l_Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1874_, v___y_1878_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
if (lean_obj_tag(v_a_1891_) == 1)
{
lean_dec(v_declName_1874_);
return v___x_1890_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1893_ = lean_st_ref_get(v___x_1892_);
v___x_1894_ = lean_box(0);
v___x_1895_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1896_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1874_, v___x_1893_, v___x_1895_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___x_1893_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1909_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_fst_1901_; 
v_fst_1901_ = lean_ctor_get(v_a_1897_, 0);
lean_inc(v_fst_1901_);
lean_dec(v_a_1897_);
if (lean_obj_tag(v_fst_1901_) == 0)
{
lean_object* v___x_1903_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1894_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1894_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
else
{
lean_object* v_val_1905_; lean_object* v___x_1907_; 
v_val_1905_ = lean_ctor_get(v_fst_1901_, 0);
lean_inc(v_val_1905_);
lean_dec_ref_known(v_fst_1901_, 1);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_val_1905_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_val_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1896_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1896_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
else
{
lean_dec(v_declName_1874_);
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_declName_1874_);
v_a_1919_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1880_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1880_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = lean_box(1);
v___x_1937_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1938_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1937_);
lean_ctor_set(v___x_1939_, 2, v___x_1936_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___f_1948_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1948_, 0, v_declName_1942_);
v___x_1949_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1951_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1949_, v___x_1950_, v___f_1948_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1959_, lean_object* v_as_1960_, lean_object* v_as_x27_1961_, lean_object* v_b_1962_, lean_object* v_a_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1959_, v_as_x27_1961_, v_b_1962_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1970_, lean_object* v_as_1971_, lean_object* v_as_x27_1972_, lean_object* v_b_1973_, lean_object* v_a_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1970_, v_as_1971_, v_as_x27_1972_, v_b_1973_, v_a_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v_as_x27_1972_);
lean_dec(v_as_1971_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = lean_unsigned_to_nat(32u);
v___x_1988_ = lean_mk_empty_array_with_capacity(v___x_1987_);
lean_dec_ref(v___x_1988_);
v___x_1989_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1990_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1981_);
v___x_1991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1991_, 0, v_declName_1981_);
v___x_1992_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1992_, 0, lean_box(0));
lean_closure_set(v___x_1992_, 1, v_declName_1981_);
lean_closure_set(v___x_1992_, 2, v___x_1991_);
v___x_1993_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1989_, v___x_1990_, v___x_1992_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
return v_res_2000_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_2001_, lean_object* v_opt_2002_){
_start:
{
lean_object* v_name_2003_; lean_object* v_defValue_2004_; lean_object* v_map_2005_; lean_object* v___x_2006_; 
v_name_2003_ = lean_ctor_get(v_opt_2002_, 0);
v_defValue_2004_ = lean_ctor_get(v_opt_2002_, 1);
v_map_2005_ = lean_ctor_get(v_opts_2001_, 0);
v___x_2006_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2005_, v_name_2003_);
if (lean_obj_tag(v___x_2006_) == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_unbox(v_defValue_2004_);
return v___x_2007_;
}
else
{
lean_object* v_val_2008_; 
v_val_2008_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v___x_2006_, 1);
if (lean_obj_tag(v_val_2008_) == 1)
{
uint8_t v_v_2009_; 
v_v_2009_ = lean_ctor_get_uint8(v_val_2008_, 0);
lean_dec_ref_known(v_val_2008_, 0);
return v_v_2009_;
}
else
{
uint8_t v___x_2010_; 
lean_dec(v_val_2008_);
v___x_2010_ = lean_unbox(v_defValue_2004_);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_2011_, lean_object* v_opt_2012_){
_start:
{
uint8_t v_res_2013_; lean_object* v_r_2014_; 
v_res_2013_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2011_, v_opt_2012_);
lean_dec_ref(v_opt_2012_);
lean_dec_ref(v_opts_2011_);
v_r_2014_ = lean_box(v_res_2013_);
return v_r_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2015_, lean_object* v_as_2016_, size_t v_sz_2017_, size_t v_i_2018_, lean_object* v_b_2019_){
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
lean_object* v_a_2028_; lean_object* v_name_2029_; lean_object* v_defValue_2030_; uint8_t v___x_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2042_; 
v_a_2028_ = lean_array_uget(v_as_2016_, v_i_2018_);
v_name_2029_ = lean_ctor_get(v_a_2028_, 0);
lean_inc(v_name_2029_);
v_defValue_2030_ = lean_ctor_get(v_a_2028_, 1);
lean_inc(v_defValue_2030_);
v___x_2031_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2015_, v_a_2028_);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_2028_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; lean_object* v_unused_2044_; 
v_unused_2043_ = lean_ctor_get(v_a_2028_, 1);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_a_2028_, 0);
lean_dec(v_unused_2044_);
v___x_2033_ = v_a_2028_;
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v_a_2028_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
uint8_t v___x_2041_; 
v___x_2041_ = lean_unbox(v_defValue_2030_);
lean_dec(v_defValue_2030_);
if (v___x_2041_ == 0)
{
if (v___x_2031_ == 0)
{
lean_del_object(v___x_2033_);
lean_dec(v_name_2029_);
v_a_2022_ = v_b_2019_;
goto v___jp_2021_;
}
else
{
goto v___jp_2035_;
}
}
else
{
if (v___x_2031_ == 0)
{
goto v___jp_2035_;
}
else
{
lean_del_object(v___x_2033_);
lean_dec(v_name_2029_);
v_a_2022_ = v_b_2019_;
goto v___jp_2021_;
}
}
v___jp_2035_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2036_, 0, v___x_2031_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2036_);
v___x_2038_ = v___x_2033_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_name_2029_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2045_, lean_object* v_as_2046_, lean_object* v_sz_2047_, lean_object* v_i_2048_, lean_object* v_b_2049_, lean_object* v___y_2050_){
_start:
{
size_t v_sz_boxed_2051_; size_t v_i_boxed_2052_; lean_object* v_res_2053_; 
v_sz_boxed_2051_ = lean_unbox_usize(v_sz_2047_);
lean_dec(v_sz_2047_);
v_i_boxed_2052_ = lean_unbox_usize(v_i_2048_);
lean_dec(v_i_2048_);
v_res_2053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2045_, v_as_2046_, v_sz_boxed_2051_, v_i_boxed_2052_, v_b_2049_);
lean_dec_ref(v_as_2046_);
lean_dec_ref(v___x_2045_);
return v_res_2053_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg();
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(lean_object* v_msgData_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v_env_2067_; uint8_t v___x_2068_; lean_object* v_env_2069_; lean_object* v___x_2070_; lean_object* v_toCold_2071_; lean_object* v_mctx_2072_; lean_object* v_lctx_2073_; lean_object* v_options_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2066_ = lean_st_ref_get(v___y_2064_);
v_env_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2066_);
v___x_2068_ = 0;
v_env_2069_ = l_Lean_Environment_setRecordingDeps(v_env_2067_, v___x_2068_);
v___x_2070_ = lean_st_ref_get(v___y_2062_);
v_toCold_2071_ = lean_ctor_get(v___y_2063_, 0);
v_mctx_2072_ = lean_ctor_get(v___x_2070_, 0);
lean_inc_ref(v_mctx_2072_);
lean_dec(v___x_2070_);
v_lctx_2073_ = lean_ctor_get(v___y_2061_, 2);
v_options_2074_ = lean_ctor_get(v_toCold_2071_, 2);
lean_inc_ref(v_options_2074_);
lean_inc_ref(v_lctx_2073_);
v___x_2075_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2075_, 0, v_env_2069_);
lean_ctor_set(v___x_2075_, 1, v_mctx_2072_);
lean_ctor_set(v___x_2075_, 2, v_lctx_2073_);
lean_ctor_set(v___x_2075_, 3, v_options_2074_);
v___x_2076_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_msgData_2060_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4___boxed(lean_object* v_msgData_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msgData_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2084_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2085_; double v___x_2086_; 
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_float_of_nat(v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(lean_object* v_cls_2090_, lean_object* v_msg_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_ref_2097_; lean_object* v___x_2098_; lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2144_; 
v_ref_2097_ = lean_ctor_get(v___y_2094_, 2);
v___x_2098_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msg_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2144_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2144_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v_traceState_2104_; lean_object* v_env_2105_; lean_object* v_nextMacroScope_2106_; lean_object* v_ngen_2107_; lean_object* v_auxDeclNGen_2108_; lean_object* v_cache_2109_; lean_object* v_recordedDeps_2110_; lean_object* v_messages_2111_; lean_object* v_infoState_2112_; lean_object* v_snapshotTasks_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2143_; 
v___x_2103_ = lean_st_ref_take(v___y_2095_);
v_traceState_2104_ = lean_ctor_get(v___x_2103_, 4);
v_env_2105_ = lean_ctor_get(v___x_2103_, 0);
v_nextMacroScope_2106_ = lean_ctor_get(v___x_2103_, 1);
v_ngen_2107_ = lean_ctor_get(v___x_2103_, 2);
v_auxDeclNGen_2108_ = lean_ctor_get(v___x_2103_, 3);
v_cache_2109_ = lean_ctor_get(v___x_2103_, 5);
v_recordedDeps_2110_ = lean_ctor_get(v___x_2103_, 6);
v_messages_2111_ = lean_ctor_get(v___x_2103_, 7);
v_infoState_2112_ = lean_ctor_get(v___x_2103_, 8);
v_snapshotTasks_2113_ = lean_ctor_get(v___x_2103_, 9);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2115_ = v___x_2103_;
v_isShared_2116_ = v_isSharedCheck_2143_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_snapshotTasks_2113_);
lean_inc(v_infoState_2112_);
lean_inc(v_messages_2111_);
lean_inc(v_recordedDeps_2110_);
lean_inc(v_cache_2109_);
lean_inc(v_traceState_2104_);
lean_inc(v_auxDeclNGen_2108_);
lean_inc(v_ngen_2107_);
lean_inc(v_nextMacroScope_2106_);
lean_inc(v_env_2105_);
lean_dec(v___x_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2143_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint64_t v_tid_2117_; lean_object* v_traces_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2142_; 
v_tid_2117_ = lean_ctor_get_uint64(v_traceState_2104_, sizeof(void*)*1);
v_traces_2118_ = lean_ctor_get(v_traceState_2104_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_traceState_2104_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2120_ = v_traceState_2104_;
v_isShared_2121_ = v_isSharedCheck_2142_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_traces_2118_);
lean_dec(v_traceState_2104_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2142_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; double v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0);
v___x_2125_ = 0;
v___x_2126_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1));
v___x_2127_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2127_, 0, v_cls_2090_);
lean_ctor_set(v___x_2127_, 1, v___x_2123_);
lean_ctor_set(v___x_2127_, 2, v___x_2126_);
lean_ctor_set_float(v___x_2127_, sizeof(void*)*3, v___x_2124_);
lean_ctor_set_float(v___x_2127_, sizeof(void*)*3 + 8, v___x_2124_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*3 + 16, v___x_2125_);
v___x_2128_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__2));
v___x_2129_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v_a_2099_);
lean_ctor_set(v___x_2129_, 2, v___x_2128_);
lean_inc(v_ref_2097_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_ref_2097_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_PersistentArray_push___redArg(v_traces_2118_, v___x_2130_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2131_);
v___x_2133_ = v___x_2120_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2131_);
lean_ctor_set_uint64(v_reuseFailAlloc_2141_, sizeof(void*)*1, v_tid_2117_);
v___x_2133_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 4, v___x_2133_);
v___x_2135_ = v___x_2115_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_env_2105_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_nextMacroScope_2106_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_ngen_2107_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_auxDeclNGen_2108_);
lean_ctor_set(v_reuseFailAlloc_2140_, 4, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2140_, 5, v_cache_2109_);
lean_ctor_set(v_reuseFailAlloc_2140_, 6, v_recordedDeps_2110_);
lean_ctor_set(v_reuseFailAlloc_2140_, 7, v_messages_2111_);
lean_ctor_set(v_reuseFailAlloc_2140_, 8, v_infoState_2112_);
lean_ctor_set(v_reuseFailAlloc_2140_, 9, v_snapshotTasks_2113_);
v___x_2135_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = lean_st_ref_put(v___y_2095_, v___x_2135_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2122_);
v___x_2138_ = v___x_2101_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2122_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___boxed(lean_object* v_cls_2145_, lean_object* v_msg_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(v_cls_2145_, v_msg_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2152_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2155_; size_t v_sz_2156_; 
v___x_2155_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2156_ = lean_array_size(v___x_2155_);
return v_sz_2156_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg();
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__3(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__4(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
lean_ctor_set(v___x_2162_, 2, v___x_2160_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__5(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2163_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__4, &l_Lean_Meta_saveEqnAffectingOptions___closed__4_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__4);
v___x_2164_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__3, &l_Lean_Meta_saveEqnAffectingOptions___closed__3_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__3);
v___x_2165_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2166_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
v___x_2167_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___x_2165_);
lean_ctor_set(v___x_2167_, 2, v___x_2164_);
lean_ctor_set(v___x_2167_, 3, v___x_2165_);
lean_ctor_set(v___x_2167_, 4, v___x_2165_);
lean_ctor_set(v___x_2167_, 5, v___x_2165_);
lean_ctor_set(v___x_2167_, 6, v___x_2163_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__9(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__8));
v___x_2175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2176_ = l_Lean_Name_append(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__11(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__10));
v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; size_t v_sz_2190_; size_t v___x_2191_; lean_object* v___x_2192_; 
v___x_2186_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2183_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2189_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2190_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2191_ = ((size_t)0ULL);
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2186_, v___x_2189_, v_sz_2190_, v___x_2191_, v___x_2188_);
lean_dec_ref(v___x_2186_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2256_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2256_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2256_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; lean_object* v___y_2200_; lean_object* v___y_2201_; 
v___x_2197_ = lean_array_get_size(v_a_2193_);
v___x_2198_ = lean_nat_dec_eq(v___x_2197_, v___x_2187_);
if (v___x_2198_ == 0)
{
lean_object* v_toCold_2243_; lean_object* v_options_2244_; uint8_t v_hasTrace_2245_; 
v_toCold_2243_ = lean_ctor_get(v_a_2183_, 0);
v_options_2244_ = lean_ctor_get(v_toCold_2243_, 2);
v_hasTrace_2245_ = lean_ctor_get_uint8(v_options_2244_, sizeof(void*)*1);
if (v_hasTrace_2245_ == 0)
{
v___y_2200_ = v_a_2182_;
v___y_2201_ = v_a_2184_;
goto v___jp_2199_;
}
else
{
lean_object* v_inheritedTraceOptions_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v_inheritedTraceOptions_2246_ = lean_ctor_get(v_toCold_2243_, 11);
v___x_2247_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__8));
v___x_2248_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__9, &l_Lean_Meta_saveEqnAffectingOptions___closed__9_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__9);
v___x_2249_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2246_, v_options_2244_, v___x_2248_);
if (v___x_2249_ == 0)
{
v___y_2200_ = v_a_2182_;
v___y_2201_ = v_a_2184_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2250_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__11, &l_Lean_Meta_saveEqnAffectingOptions___closed__11_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__11);
lean_inc(v_declName_2180_);
v___x_2251_ = l_Lean_MessageData_ofName(v_declName_2180_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(v___x_2247_, v___x_2252_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_dec_ref_known(v___x_2253_, 1);
v___y_2200_ = v_a_2182_;
v___y_2201_ = v_a_2184_;
goto v___jp_2199_;
}
else
{
lean_del_object(v___x_2195_);
lean_dec(v_a_2193_);
lean_dec(v_declName_2180_);
return v___x_2253_;
}
}
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_del_object(v___x_2195_);
lean_dec(v_a_2193_);
lean_dec(v_declName_2180_);
v___x_2254_ = lean_box(0);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
v___jp_2199_:
{
lean_object* v___x_2202_; lean_object* v_env_2203_; lean_object* v_nextMacroScope_2204_; lean_object* v_ngen_2205_; lean_object* v_auxDeclNGen_2206_; lean_object* v_traceState_2207_; lean_object* v_recordedDeps_2208_; lean_object* v_messages_2209_; lean_object* v_infoState_2210_; lean_object* v_snapshotTasks_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2241_; 
v___x_2202_ = lean_st_ref_take(v___y_2201_);
v_env_2203_ = lean_ctor_get(v___x_2202_, 0);
v_nextMacroScope_2204_ = lean_ctor_get(v___x_2202_, 1);
v_ngen_2205_ = lean_ctor_get(v___x_2202_, 2);
v_auxDeclNGen_2206_ = lean_ctor_get(v___x_2202_, 3);
v_traceState_2207_ = lean_ctor_get(v___x_2202_, 4);
v_recordedDeps_2208_ = lean_ctor_get(v___x_2202_, 6);
v_messages_2209_ = lean_ctor_get(v___x_2202_, 7);
v_infoState_2210_ = lean_ctor_get(v___x_2202_, 8);
v_snapshotTasks_2211_ = lean_ctor_get(v___x_2202_, 9);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v___x_2202_, 5);
lean_dec(v_unused_2242_);
v___x_2213_ = v___x_2202_;
v_isShared_2214_ = v_isSharedCheck_2241_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snapshotTasks_2211_);
lean_inc(v_infoState_2210_);
lean_inc(v_messages_2209_);
lean_inc(v_recordedDeps_2208_);
lean_inc(v_traceState_2207_);
lean_inc(v_auxDeclNGen_2206_);
lean_inc(v_ngen_2205_);
lean_inc(v_nextMacroScope_2204_);
lean_inc(v_env_2203_);
lean_dec(v___x_2202_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2241_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2215_ = l_Lean_Meta_eqnOptionsExt;
v___x_2216_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2215_, v_env_2203_, v_declName_2180_, v_a_2193_, v___x_2198_);
v___x_2217_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 5, v___x_2217_);
lean_ctor_set(v___x_2213_, 0, v___x_2216_);
v___x_2219_ = v___x_2213_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_nextMacroScope_2204_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_ngen_2205_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_auxDeclNGen_2206_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_traceState_2207_);
lean_ctor_set(v_reuseFailAlloc_2240_, 5, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2240_, 6, v_recordedDeps_2208_);
lean_ctor_set(v_reuseFailAlloc_2240_, 7, v_messages_2209_);
lean_ctor_set(v_reuseFailAlloc_2240_, 8, v_infoState_2210_);
lean_ctor_set(v_reuseFailAlloc_2240_, 9, v_snapshotTasks_2211_);
v___x_2219_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_mctx_2222_; lean_object* v_zetaDeltaFVarIds_2223_; lean_object* v_postponed_2224_; lean_object* v_diag_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2238_; 
v___x_2220_ = lean_st_ref_put(v___y_2201_, v___x_2219_);
v___x_2221_ = lean_st_ref_take(v___y_2200_);
v_mctx_2222_ = lean_ctor_get(v___x_2221_, 0);
v_zetaDeltaFVarIds_2223_ = lean_ctor_get(v___x_2221_, 2);
v_postponed_2224_ = lean_ctor_get(v___x_2221_, 3);
v_diag_2225_ = lean_ctor_get(v___x_2221_, 4);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v___x_2221_, 1);
lean_dec(v_unused_2239_);
v___x_2227_ = v___x_2221_;
v_isShared_2228_ = v_isSharedCheck_2238_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_diag_2225_);
lean_inc(v_postponed_2224_);
lean_inc(v_zetaDeltaFVarIds_2223_);
lean_inc(v_mctx_2222_);
lean_dec(v___x_2221_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2238_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__5, &l_Lean_Meta_saveEqnAffectingOptions___closed__5_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__5);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v___x_2230_);
v___x_2232_ = v___x_2227_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_mctx_2222_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_zetaDeltaFVarIds_2223_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_postponed_2224_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_diag_2225_);
v___x_2232_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_st_ref_put(v___y_2200_, v___x_2232_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2229_);
v___x_2235_ = v___x_2195_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2229_);
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
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_declName_2180_);
v_a_2257_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2192_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2192_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2272_, lean_object* v_as_2273_, size_t v_sz_2274_, size_t v_i_2275_, lean_object* v_b_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2272_, v_as_2273_, v_sz_2274_, v_i_2275_, v_b_2276_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2283_, lean_object* v_as_2284_, lean_object* v_sz_2285_, lean_object* v_i_2286_, lean_object* v_b_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2285_);
lean_dec(v_sz_2285_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2286_);
lean_dec(v_i_2286_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2283_, v_as_2284_, v_sz_boxed_2293_, v_i_boxed_2294_, v_b_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v_as_2284_);
lean_dec_ref(v___x_2283_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_00_u03b2_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg(){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg___boxed(lean_object* v___dummy_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg();
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_00_u03b2_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_st_mk_ref(v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2310_){
_start:
{
uint8_t v___x_2312_; 
v___x_2312_ = l_Lean_initializing();
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_dec_ref(v_f_2310_);
v___x_2313_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2316_ = lean_st_ref_take(v___x_2315_);
v___x_2317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_f_2310_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_st_ref_put(v___x_2315_, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2320_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2326_, lean_object* v_as_x27_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
if (lean_obj_tag(v_as_x27_2327_) == 0)
{
lean_object* v___x_2334_; 
lean_dec(v_declName_2326_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_b_2328_);
return v___x_2334_;
}
else
{
lean_object* v_head_2335_; lean_object* v_tail_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec_ref(v_b_2328_);
v_head_2335_ = lean_ctor_get(v_as_x27_2327_, 0);
v_tail_2336_ = lean_ctor_get(v_as_x27_2327_, 1);
v___x_2337_ = lean_box(0);
v___x_2338_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2335_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v_declName_2326_);
v___x_2339_ = lean_apply_6(v_head_2335_, v_declName_2326_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, lean_box(0));
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2350_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2350_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2350_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
if (lean_obj_tag(v_a_2340_) == 1)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec(v_declName_2326_);
v___x_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_a_2340_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___x_2337_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2345_);
v___x_2347_ = v___x_2342_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
else
{
lean_del_object(v___x_2342_);
lean_dec(v_a_2340_);
v_as_x27_2327_ = v_tail_2336_;
v_b_2328_ = v___x_2338_;
goto _start;
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_declName_2326_);
v_a_2351_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2339_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2339_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2359_, lean_object* v_as_x27_2360_, lean_object* v_b_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2359_, v_as_x27_2360_, v_b_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_as_x27_2360_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v_declName_2368_, uint8_t v_nonRec_2369_, lean_object* v___x_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v___x_2379_; 
lean_inc(v_declName_2368_);
v___x_2379_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2368_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; uint8_t v___x_2381_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = lean_unbox(v_a_2380_);
if (v___x_2381_ == 0)
{
lean_dec(v_a_2380_);
lean_dec(v___x_2370_);
lean_dec(v_declName_2368_);
goto v___jp_2376_;
}
else
{
lean_object* v___x_2382_; 
lean_inc(v_declName_2368_);
v___x_2382_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2368_, v___y_2374_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2427_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2427_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2427_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
uint8_t v___x_2387_; 
v___x_2387_ = lean_unbox(v_a_2383_);
lean_dec(v_a_2383_);
if (v___x_2387_ == 0)
{
if (v_nonRec_2369_ == 0)
{
lean_del_object(v___x_2385_);
lean_dec(v_a_2380_);
lean_dec(v___x_2370_);
lean_dec(v_declName_2368_);
goto v___jp_2376_;
}
else
{
lean_object* v___x_2388_; lean_object* v_env_2389_; uint8_t v___x_2390_; uint8_t v___x_2391_; 
v___x_2388_ = lean_st_ref_get(v___y_2374_);
v_env_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc_ref(v_env_2389_);
lean_dec(v___x_2388_);
v___x_2390_ = lean_unbox(v_a_2380_);
lean_dec(v_a_2380_);
lean_inc(v___x_2370_);
v___x_2391_ = l_Lean_Environment_contains(v_env_2389_, v___x_2370_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
lean_del_object(v___x_2385_);
v___x_2392_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2368_, v___x_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
return v___x_2392_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_dec(v_declName_2368_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2370_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2393_);
v___x_2395_ = v___x_2385_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
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
lean_object* v___x_2397_; lean_object* v_env_2398_; uint8_t v___x_2399_; uint8_t v___x_2400_; 
v___x_2397_ = lean_st_ref_get(v___y_2374_);
v_env_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc_ref(v_env_2398_);
lean_dec(v___x_2397_);
v___x_2399_ = lean_unbox(v_a_2380_);
lean_dec(v_a_2380_);
lean_inc(v___x_2370_);
v___x_2400_ = l_Lean_Environment_contains(v_env_2398_, v___x_2370_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_del_object(v___x_2385_);
lean_dec(v___x_2370_);
v___x_2401_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2402_ = lean_st_ref_get(v___x_2401_);
v___x_2403_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2404_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2368_, v___x_2402_, v___x_2403_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___x_2402_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2414_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2414_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2414_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v_fst_2409_; 
v_fst_2409_ = lean_ctor_get(v_a_2405_, 0);
lean_inc(v_fst_2409_);
lean_dec(v_a_2405_);
if (lean_obj_tag(v_fst_2409_) == 0)
{
lean_del_object(v___x_2407_);
goto v___jp_2376_;
}
else
{
lean_object* v_val_2410_; lean_object* v___x_2412_; 
v_val_2410_ = lean_ctor_get(v_fst_2409_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v_fst_2409_, 1);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v_val_2410_);
v___x_2412_ = v___x_2407_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_val_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
v_a_2415_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2404_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2404_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec(v_declName_2368_);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2370_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2423_);
v___x_2425_ = v___x_2385_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_a_2380_);
lean_dec(v___x_2370_);
lean_dec(v_declName_2368_);
v_a_2428_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2382_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2382_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v___x_2370_);
lean_dec(v_declName_2368_);
v_a_2436_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2379_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2379_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
v___jp_2376_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v_declName_2444_, lean_object* v_nonRec_2445_, lean_object* v___x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_nonRec_boxed_2452_; lean_object* v_res_2453_; 
v_nonRec_boxed_2452_ = lean_unbox(v_nonRec_2445_);
v_res_2453_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v_declName_2444_, v_nonRec_boxed_2452_, v___x_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_ref_2460_; lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2470_; 
v_ref_2460_ = lean_ctor_get(v___y_2457_, 2);
v___x_2461_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msg_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_inc(v_ref_2460_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_ref_2460_);
lean_ctor_set(v___x_2466_, 1, v_a_2462_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 1);
lean_ctor_set(v___x_2464_, 0, v___x_2466_);
v___x_2468_ = v___x_2464_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2478_, uint8_t v_isExporting_2479_, lean_object* v___x_2480_, lean_object* v___y_2481_, lean_object* v___x_2482_, lean_object* v_a_x3f_2483_){
_start:
{
lean_object* v___x_2485_; lean_object* v_env_2486_; lean_object* v_nextMacroScope_2487_; lean_object* v_ngen_2488_; lean_object* v_auxDeclNGen_2489_; lean_object* v_traceState_2490_; lean_object* v_recordedDeps_2491_; lean_object* v_messages_2492_; lean_object* v_infoState_2493_; lean_object* v_snapshotTasks_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2519_; 
v___x_2485_ = lean_st_ref_take(v___y_2478_);
v_env_2486_ = lean_ctor_get(v___x_2485_, 0);
v_nextMacroScope_2487_ = lean_ctor_get(v___x_2485_, 1);
v_ngen_2488_ = lean_ctor_get(v___x_2485_, 2);
v_auxDeclNGen_2489_ = lean_ctor_get(v___x_2485_, 3);
v_traceState_2490_ = lean_ctor_get(v___x_2485_, 4);
v_recordedDeps_2491_ = lean_ctor_get(v___x_2485_, 6);
v_messages_2492_ = lean_ctor_get(v___x_2485_, 7);
v_infoState_2493_ = lean_ctor_get(v___x_2485_, 8);
v_snapshotTasks_2494_ = lean_ctor_get(v___x_2485_, 9);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v___x_2485_, 5);
lean_dec(v_unused_2520_);
v___x_2496_ = v___x_2485_;
v_isShared_2497_ = v_isSharedCheck_2519_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_snapshotTasks_2494_);
lean_inc(v_infoState_2493_);
lean_inc(v_messages_2492_);
lean_inc(v_recordedDeps_2491_);
lean_inc(v_traceState_2490_);
lean_inc(v_auxDeclNGen_2489_);
lean_inc(v_ngen_2488_);
lean_inc(v_nextMacroScope_2487_);
lean_inc(v_env_2486_);
lean_dec(v___x_2485_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2519_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = l_Lean_Environment_setExporting(v_env_2486_, v_isExporting_2479_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 5, v___x_2480_);
lean_ctor_set(v___x_2496_, 0, v___x_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_nextMacroScope_2487_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_ngen_2488_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_auxDeclNGen_2489_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_traceState_2490_);
lean_ctor_set(v_reuseFailAlloc_2518_, 5, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_recordedDeps_2491_);
lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_messages_2492_);
lean_ctor_set(v_reuseFailAlloc_2518_, 8, v_infoState_2493_);
lean_ctor_set(v_reuseFailAlloc_2518_, 9, v_snapshotTasks_2494_);
v___x_2500_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_mctx_2503_; lean_object* v_zetaDeltaFVarIds_2504_; lean_object* v_postponed_2505_; lean_object* v_diag_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2516_; 
v___x_2501_ = lean_st_ref_put(v___y_2478_, v___x_2500_);
v___x_2502_ = lean_st_ref_take(v___y_2481_);
v_mctx_2503_ = lean_ctor_get(v___x_2502_, 0);
v_zetaDeltaFVarIds_2504_ = lean_ctor_get(v___x_2502_, 2);
v_postponed_2505_ = lean_ctor_get(v___x_2502_, 3);
v_diag_2506_ = lean_ctor_get(v___x_2502_, 4);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2502_, 1);
lean_dec(v_unused_2517_);
v___x_2508_ = v___x_2502_;
v_isShared_2509_ = v_isSharedCheck_2516_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_diag_2506_);
lean_inc(v_postponed_2505_);
lean_inc(v_zetaDeltaFVarIds_2504_);
lean_inc(v_mctx_2503_);
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2516_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = lean_box(0);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2482_);
v___x_2512_ = v___x_2508_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_mctx_2503_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_zetaDeltaFVarIds_2504_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_postponed_2505_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_diag_2506_);
v___x_2512_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_st_ref_put(v___y_2481_, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2510_);
return v___x_2514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2521_, lean_object* v_isExporting_2522_, lean_object* v___x_2523_, lean_object* v___y_2524_, lean_object* v___x_2525_, lean_object* v_a_x3f_2526_, lean_object* v___y_2527_){
_start:
{
uint8_t v_isExporting_boxed_2528_; lean_object* v_res_2529_; 
v_isExporting_boxed_2528_ = lean_unbox(v_isExporting_2522_);
v_res_2529_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2521_, v_isExporting_boxed_2528_, v___x_2523_, v___y_2524_, v___x_2525_, v_a_x3f_2526_);
lean_dec(v_a_x3f_2526_);
lean_dec(v___y_2524_);
lean_dec(v___y_2521_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2530_, uint8_t v_isExporting_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v_env_2538_; lean_object* v___x_2539_; uint8_t v_isModule_2540_; 
v___x_2537_ = lean_st_ref_get(v___y_2535_);
v_env_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc_ref(v_env_2538_);
lean_dec(v___x_2537_);
v___x_2539_ = l_Lean_Environment_header(v_env_2538_);
v_isModule_2540_ = lean_ctor_get_uint8(v___x_2539_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2539_);
if (v_isModule_2540_ == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref(v_env_2538_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v___x_2541_ = lean_apply_5(v_x_2530_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, lean_box(0));
return v___x_2541_;
}
else
{
uint8_t v_isExporting_2542_; 
v_isExporting_2542_ = lean_ctor_get_uint8(v_env_2538_, sizeof(void*)*13);
lean_dec_ref(v_env_2538_);
if (v_isExporting_2531_ == 0)
{
if (v_isExporting_2542_ == 0)
{
lean_object* v___x_2609_; 
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v___x_2609_ = lean_apply_5(v_x_2530_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, lean_box(0));
return v___x_2609_;
}
else
{
goto v___jp_2543_;
}
}
else
{
if (v_isExporting_2542_ == 0)
{
goto v___jp_2543_;
}
else
{
lean_object* v___x_2610_; 
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v___x_2610_ = lean_apply_5(v_x_2530_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, lean_box(0));
return v___x_2610_;
}
}
v___jp_2543_:
{
lean_object* v___x_2544_; lean_object* v_env_2545_; lean_object* v_nextMacroScope_2546_; lean_object* v_ngen_2547_; lean_object* v_auxDeclNGen_2548_; lean_object* v_traceState_2549_; lean_object* v_recordedDeps_2550_; lean_object* v_messages_2551_; lean_object* v_infoState_2552_; lean_object* v_snapshotTasks_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2607_; 
v___x_2544_ = lean_st_ref_take(v___y_2535_);
v_env_2545_ = lean_ctor_get(v___x_2544_, 0);
v_nextMacroScope_2546_ = lean_ctor_get(v___x_2544_, 1);
v_ngen_2547_ = lean_ctor_get(v___x_2544_, 2);
v_auxDeclNGen_2548_ = lean_ctor_get(v___x_2544_, 3);
v_traceState_2549_ = lean_ctor_get(v___x_2544_, 4);
v_recordedDeps_2550_ = lean_ctor_get(v___x_2544_, 6);
v_messages_2551_ = lean_ctor_get(v___x_2544_, 7);
v_infoState_2552_ = lean_ctor_get(v___x_2544_, 8);
v_snapshotTasks_2553_ = lean_ctor_get(v___x_2544_, 9);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; 
v_unused_2608_ = lean_ctor_get(v___x_2544_, 5);
lean_dec(v_unused_2608_);
v___x_2555_ = v___x_2544_;
v_isShared_2556_ = v_isSharedCheck_2607_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_snapshotTasks_2553_);
lean_inc(v_infoState_2552_);
lean_inc(v_messages_2551_);
lean_inc(v_recordedDeps_2550_);
lean_inc(v_traceState_2549_);
lean_inc(v_auxDeclNGen_2548_);
lean_inc(v_ngen_2547_);
lean_inc(v_nextMacroScope_2546_);
lean_inc(v_env_2545_);
lean_dec(v___x_2544_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2607_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2557_ = l_Lean_Environment_setExporting(v_env_2545_, v_isExporting_2531_);
v___x_2558_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 5, v___x_2558_);
lean_ctor_set(v___x_2555_, 0, v___x_2557_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_nextMacroScope_2546_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_ngen_2547_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_auxDeclNGen_2548_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v_traceState_2549_);
lean_ctor_set(v_reuseFailAlloc_2606_, 5, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2606_, 6, v_recordedDeps_2550_);
lean_ctor_set(v_reuseFailAlloc_2606_, 7, v_messages_2551_);
lean_ctor_set(v_reuseFailAlloc_2606_, 8, v_infoState_2552_);
lean_ctor_set(v_reuseFailAlloc_2606_, 9, v_snapshotTasks_2553_);
v___x_2560_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_mctx_2563_; lean_object* v_zetaDeltaFVarIds_2564_; lean_object* v_postponed_2565_; lean_object* v_diag_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2604_; 
v___x_2561_ = lean_st_ref_put(v___y_2535_, v___x_2560_);
v___x_2562_ = lean_st_ref_take(v___y_2533_);
v_mctx_2563_ = lean_ctor_get(v___x_2562_, 0);
v_zetaDeltaFVarIds_2564_ = lean_ctor_get(v___x_2562_, 2);
v_postponed_2565_ = lean_ctor_get(v___x_2562_, 3);
v_diag_2566_ = lean_ctor_get(v___x_2562_, 4);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v___x_2562_, 1);
lean_dec(v_unused_2605_);
v___x_2568_ = v___x_2562_;
v_isShared_2569_ = v_isSharedCheck_2604_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_diag_2566_);
lean_inc(v_postponed_2565_);
lean_inc(v_zetaDeltaFVarIds_2564_);
lean_inc(v_mctx_2563_);
lean_dec(v___x_2562_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2604_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__5, &l_Lean_Meta_saveEqnAffectingOptions___closed__5_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__5);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v___x_2570_);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_mctx_2563_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_zetaDeltaFVarIds_2564_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_postponed_2565_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_diag_2566_);
v___x_2572_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v_r_2574_; 
v___x_2573_ = lean_st_ref_put(v___y_2533_, v___x_2572_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v_r_2574_ = lean_apply_5(v_x_2530_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, lean_box(0));
if (lean_obj_tag(v_r_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2591_; 
v_a_2575_ = lean_ctor_get(v_r_2574_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_r_2574_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2577_ = v_r_2574_;
v_isShared_2578_ = v_isSharedCheck_2591_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v_r_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2591_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
lean_inc(v_a_2575_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v___x_2581_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2535_, v_isExporting_2542_, v___x_2558_, v___y_2533_, v___x_2570_, v___x_2580_);
lean_dec_ref(v___x_2580_);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2581_, 0);
lean_dec(v_unused_2589_);
v___x_2583_ = v___x_2581_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_dec(v___x_2581_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v_a_2575_);
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2575_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_a_2592_ = lean_ctor_get(v_r_2574_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v_r_2574_, 1);
v___x_2593_ = lean_box(0);
v___x_2594_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2535_, v_isExporting_2542_, v___x_2558_, v___y_2533_, v___x_2570_, v___x_2593_);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2594_, 0);
lean_dec(v_unused_2602_);
v___x_2596_ = v___x_2594_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_dec(v___x_2594_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 1);
lean_ctor_set(v___x_2596_, 0, v_a_2592_);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2592_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2611_, lean_object* v_isExporting_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v_isExporting_boxed_2618_; lean_object* v_res_2619_; 
v_isExporting_boxed_2618_ = lean_unbox(v_isExporting_2612_);
v_res_2619_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2611_, v_isExporting_boxed_2618_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2620_, uint8_t v_when_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
if (v_when_2621_ == 0)
{
lean_object* v___x_2627_; 
lean_inc(v___y_2625_);
lean_inc_ref(v___y_2624_);
lean_inc(v___y_2623_);
lean_inc_ref(v___y_2622_);
v___x_2627_ = lean_apply_5(v_x_2620_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, lean_box(0));
return v___x_2627_;
}
else
{
uint8_t v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = 0;
v___x_2629_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2620_, v___x_2628_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2630_, lean_object* v_when_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v_when_boxed_2637_; lean_object* v_res_2638_; 
v_when_boxed_2637_ = lean_unbox(v_when_2631_);
v_res_2638_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2630_, v_when_boxed_2637_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2638_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2644_ = l_Lean_stringToMessageData(v___x_2643_);
return v___x_2644_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2647_, uint8_t v_nonRec_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2654_; lean_object* v_env_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___f_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; 
v___x_2654_ = lean_st_ref_get(v___y_2652_);
v_env_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc_ref(v_env_2655_);
lean_dec(v___x_2654_);
v___x_2656_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2647_);
v___x_2657_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2655_, v_declName_2647_, v___x_2656_);
v___x_2658_ = lean_box(v_nonRec_2648_);
lean_inc(v___x_2657_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2659_, 0, v_declName_2647_);
lean_closure_set(v___f_2659_, 1, v___x_2658_);
lean_closure_set(v___f_2659_, 2, v___x_2657_);
v___x_2660_ = 1;
v___x_2661_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2659_, v___x_2660_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
if (lean_obj_tag(v_a_2662_) == 1)
{
lean_object* v_val_2663_; uint8_t v___x_2664_; 
v_val_2663_ = lean_ctor_get(v_a_2662_, 0);
v___x_2664_ = lean_name_eq(v_val_2663_, v___x_2657_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_inc(v_val_2663_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2665_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2666_ = l_Lean_MessageData_ofName(v_val_2663_);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_MessageData_ofName(v___x_2657_);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2673_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_dec(v___x_2657_);
return v___x_2661_;
}
}
else
{
lean_dec(v___x_2657_);
return v___x_2661_;
}
}
else
{
lean_dec(v___x_2657_);
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2683_, lean_object* v_nonRec_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
uint8_t v_nonRec_boxed_2690_; lean_object* v_res_2691_; 
v_nonRec_boxed_2690_ = lean_unbox(v_nonRec_2684_);
v_res_2691_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2683_, v_nonRec_boxed_2690_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2692_, uint8_t v_nonRec_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v___f_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2699_ = lean_box(v_nonRec_2693_);
v___f_2700_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2700_, 0, v_declName_2692_);
lean_closure_set(v___f_2700_, 1, v___x_2699_);
v___x_2701_ = lean_unsigned_to_nat(32u);
v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
lean_dec_ref(v___x_2702_);
v___x_2703_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2704_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2705_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2703_, v___x_2704_, v___f_2700_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2706_, lean_object* v_nonRec_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
uint8_t v_nonRec_boxed_2713_; lean_object* v_res_2714_; 
v_nonRec_boxed_2713_ = lean_unbox(v_nonRec_2707_);
v_res_2714_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2706_, v_nonRec_boxed_2713_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2715_, lean_object* v_as_2716_, lean_object* v_as_x27_2717_, lean_object* v_b_2718_, lean_object* v_a_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2715_, v_as_x27_2717_, v_b_2718_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2726_, lean_object* v_as_2727_, lean_object* v_as_x27_2728_, lean_object* v_b_2729_, lean_object* v_a_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2726_, v_as_2727_, v_as_x27_2728_, v_b_2729_, v_a_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_as_x27_2728_);
lean_dec(v_as_2727_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2737_, lean_object* v_x_2738_, uint8_t v_when_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2738_, v_when_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2746_, lean_object* v_x_2747_, lean_object* v_when_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v_when_boxed_2754_; lean_object* v_res_2755_; 
v_when_boxed_2754_ = lean_unbox(v_when_2748_);
v_res_2755_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2746_, v_x_2747_, v_when_boxed_2754_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2756_, lean_object* v_msg_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2764_, lean_object* v_msg_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2764_, v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2772_, lean_object* v_x_2773_, uint8_t v_isExporting_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2773_, v_isExporting_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2781_, lean_object* v_x_2782_, lean_object* v_isExporting_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v_isExporting_boxed_2789_; lean_object* v_res_2790_; 
v_isExporting_boxed_2789_ = lean_unbox(v_isExporting_2783_);
v_res_2790_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2781_, v_x_2782_, v_isExporting_boxed_2789_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2790_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_unsigned_to_nat(32u);
v___x_2792_ = lean_mk_empty_array_with_capacity(v___x_2791_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2794_ = ((size_t)5ULL);
v___x_2795_ = lean_unsigned_to_nat(0u);
v___x_2796_ = lean_unsigned_to_nat(32u);
v___x_2797_ = lean_mk_empty_array_with_capacity(v___x_2796_);
v___x_2798_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2799_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___x_2797_);
lean_ctor_set(v___x_2799_, 2, v___x_2795_);
lean_ctor_set(v___x_2799_, 3, v___x_2795_);
lean_ctor_set_usize(v___x_2799_, 4, v___x_2794_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v_traceState_2803_; lean_object* v_traces_2804_; lean_object* v___x_2805_; lean_object* v_traceState_2806_; lean_object* v_env_2807_; lean_object* v_nextMacroScope_2808_; lean_object* v_ngen_2809_; lean_object* v_auxDeclNGen_2810_; lean_object* v_cache_2811_; lean_object* v_recordedDeps_2812_; lean_object* v_messages_2813_; lean_object* v_infoState_2814_; lean_object* v_snapshotTasks_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2834_; 
v___x_2802_ = lean_st_ref_get(v___y_2800_);
v_traceState_2803_ = lean_ctor_get(v___x_2802_, 4);
lean_inc_ref(v_traceState_2803_);
lean_dec(v___x_2802_);
v_traces_2804_ = lean_ctor_get(v_traceState_2803_, 0);
lean_inc_ref(v_traces_2804_);
lean_dec_ref(v_traceState_2803_);
v___x_2805_ = lean_st_ref_take(v___y_2800_);
v_traceState_2806_ = lean_ctor_get(v___x_2805_, 4);
v_env_2807_ = lean_ctor_get(v___x_2805_, 0);
v_nextMacroScope_2808_ = lean_ctor_get(v___x_2805_, 1);
v_ngen_2809_ = lean_ctor_get(v___x_2805_, 2);
v_auxDeclNGen_2810_ = lean_ctor_get(v___x_2805_, 3);
v_cache_2811_ = lean_ctor_get(v___x_2805_, 5);
v_recordedDeps_2812_ = lean_ctor_get(v___x_2805_, 6);
v_messages_2813_ = lean_ctor_get(v___x_2805_, 7);
v_infoState_2814_ = lean_ctor_get(v___x_2805_, 8);
v_snapshotTasks_2815_ = lean_ctor_get(v___x_2805_, 9);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2817_ = v___x_2805_;
v_isShared_2818_ = v_isSharedCheck_2834_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_snapshotTasks_2815_);
lean_inc(v_infoState_2814_);
lean_inc(v_messages_2813_);
lean_inc(v_recordedDeps_2812_);
lean_inc(v_cache_2811_);
lean_inc(v_traceState_2806_);
lean_inc(v_auxDeclNGen_2810_);
lean_inc(v_ngen_2809_);
lean_inc(v_nextMacroScope_2808_);
lean_inc(v_env_2807_);
lean_dec(v___x_2805_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2834_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
uint64_t v_tid_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2832_; 
v_tid_2819_ = lean_ctor_get_uint64(v_traceState_2806_, sizeof(void*)*1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_traceState_2806_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v_traceState_2806_, 0);
lean_dec(v_unused_2833_);
v___x_2821_ = v_traceState_2806_;
v_isShared_2822_ = v_isSharedCheck_2832_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v_traceState_2806_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2832_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2823_);
lean_ctor_set_uint64(v_reuseFailAlloc_2831_, sizeof(void*)*1, v_tid_2819_);
v___x_2825_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2827_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 4, v___x_2825_);
v___x_2827_ = v___x_2817_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_env_2807_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_nextMacroScope_2808_);
lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_ngen_2809_);
lean_ctor_set(v_reuseFailAlloc_2830_, 3, v_auxDeclNGen_2810_);
lean_ctor_set(v_reuseFailAlloc_2830_, 4, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2830_, 5, v_cache_2811_);
lean_ctor_set(v_reuseFailAlloc_2830_, 6, v_recordedDeps_2812_);
lean_ctor_set(v_reuseFailAlloc_2830_, 7, v_messages_2813_);
lean_ctor_set(v_reuseFailAlloc_2830_, 8, v_infoState_2814_);
lean_ctor_set(v_reuseFailAlloc_2830_, 9, v_snapshotTasks_2815_);
v___x_2827_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_st_ref_put(v___y_2800_, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v_traces_2804_);
return v___x_2829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2835_);
lean_dec(v___y_2835_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = 0;
v___x_2851_ = lean_box(v___x_2850_);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2860_ = l_Lean_stringToMessageData(v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2861_, lean_object* v_x_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2867_ = l_Lean_MessageData_ofName(v_name_2861_);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2870_, v_x_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec_ref(v_x_2871_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2876_){
_start:
{
if (lean_obj_tag(v_x_2876_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
v_a_2878_ = lean_ctor_get(v_x_2876_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_x_2876_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v_x_2876_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v_x_2876_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set_tag(v___x_2880_, 1);
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v_x_2876_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v_x_2876_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v_x_2876_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v_x_2876_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set_tag(v___x_2888_, 0);
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2894_);
return v_res_2896_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2897_){
_start:
{
if (lean_obj_tag(v_e_2897_) == 0)
{
uint8_t v___x_2898_; 
v___x_2898_ = 2;
return v___x_2898_;
}
else
{
lean_object* v_a_2899_; uint8_t v___x_2900_; 
v_a_2899_ = lean_ctor_get(v_e_2897_, 0);
v___x_2900_ = lean_unbox(v_a_2899_);
if (v___x_2900_ == 0)
{
uint8_t v___x_2901_; 
v___x_2901_ = 1;
return v___x_2901_;
}
else
{
uint8_t v___x_2902_; 
v___x_2902_ = 0;
return v___x_2902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2903_){
_start:
{
uint8_t v_res_2904_; lean_object* v_r_2905_; 
v_res_2904_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2903_);
lean_dec_ref(v_e_2903_);
v_r_2905_ = lean_box(v_res_2904_);
return v_r_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2906_, size_t v_i_2907_, lean_object* v_bs_2908_){
_start:
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_usize_dec_lt(v_i_2907_, v_sz_2906_);
if (v___x_2909_ == 0)
{
return v_bs_2908_;
}
else
{
lean_object* v_v_2910_; lean_object* v_msg_2911_; lean_object* v___x_2912_; lean_object* v_bs_x27_2913_; size_t v___x_2914_; size_t v___x_2915_; lean_object* v___x_2916_; 
v_v_2910_ = lean_array_uget_borrowed(v_bs_2908_, v_i_2907_);
v_msg_2911_ = lean_ctor_get(v_v_2910_, 1);
lean_inc_ref(v_msg_2911_);
v___x_2912_ = lean_unsigned_to_nat(0u);
v_bs_x27_2913_ = lean_array_uset(v_bs_2908_, v_i_2907_, v___x_2912_);
v___x_2914_ = ((size_t)1ULL);
v___x_2915_ = lean_usize_add(v_i_2907_, v___x_2914_);
v___x_2916_ = lean_array_uset(v_bs_x27_2913_, v_i_2907_, v_msg_2911_);
v_i_2907_ = v___x_2915_;
v_bs_2908_ = v___x_2916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2918_, lean_object* v_i_2919_, lean_object* v_bs_2920_){
_start:
{
size_t v_sz_boxed_2921_; size_t v_i_boxed_2922_; lean_object* v_res_2923_; 
v_sz_boxed_2921_ = lean_unbox_usize(v_sz_2918_);
lean_dec(v_sz_2918_);
v_i_boxed_2922_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_res_2923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2921_, v_i_boxed_2922_, v_bs_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2924_, lean_object* v_data_2925_, lean_object* v_ref_2926_, lean_object* v_msg_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_toCold_2931_; lean_object* v_currRecDepth_2932_; lean_object* v_ref_2933_; uint16_t v_optionFlags_2934_; uint8_t v_suppressElabErrors_2935_; uint8_t v_checkDeprecated_2936_; uint8_t v_isRecordingDeps_2937_; lean_object* v_ref_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_traceState_2941_; lean_object* v_traces_2942_; lean_object* v___x_2943_; size_t v_sz_2944_; size_t v___x_2945_; lean_object* v___x_2946_; lean_object* v_msg_2947_; lean_object* v___x_2948_; lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2987_; 
v_toCold_2931_ = lean_ctor_get(v___y_2928_, 0);
v_currRecDepth_2932_ = lean_ctor_get(v___y_2928_, 1);
v_ref_2933_ = lean_ctor_get(v___y_2928_, 2);
v_optionFlags_2934_ = lean_ctor_get_uint16(v___y_2928_, sizeof(void*)*3);
v_suppressElabErrors_2935_ = lean_ctor_get_uint8(v___y_2928_, sizeof(void*)*3 + 2);
v_checkDeprecated_2936_ = lean_ctor_get_uint8(v___y_2928_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2937_ = lean_ctor_get_uint8(v___y_2928_, sizeof(void*)*3 + 4);
v_ref_2938_ = l_Lean_replaceRef(v_ref_2926_, v_ref_2933_);
lean_inc(v_currRecDepth_2932_);
lean_inc_ref(v_toCold_2931_);
v___x_2939_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2939_, 0, v_toCold_2931_);
lean_ctor_set(v___x_2939_, 1, v_currRecDepth_2932_);
lean_ctor_set(v___x_2939_, 2, v_ref_2938_);
lean_ctor_set_uint16(v___x_2939_, sizeof(void*)*3, v_optionFlags_2934_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*3 + 2, v_suppressElabErrors_2935_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*3 + 3, v_checkDeprecated_2936_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*3 + 4, v_isRecordingDeps_2937_);
v___x_2940_ = lean_st_ref_get(v___y_2929_);
v_traceState_2941_ = lean_ctor_get(v___x_2940_, 4);
lean_inc_ref(v_traceState_2941_);
lean_dec(v___x_2940_);
v_traces_2942_ = lean_ctor_get(v_traceState_2941_, 0);
lean_inc_ref(v_traces_2942_);
lean_dec_ref(v_traceState_2941_);
v___x_2943_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2942_);
lean_dec_ref(v_traces_2942_);
v_sz_2944_ = lean_array_size(v___x_2943_);
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2944_, v___x_2945_, v___x_2943_);
v_msg_2947_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2947_, 0, v_data_2925_);
lean_ctor_set(v_msg_2947_, 1, v_msg_2927_);
lean_ctor_set(v_msg_2947_, 2, v___x_2946_);
v___x_2948_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2947_, v___x_2939_, v___y_2929_);
lean_dec_ref_known(v___x_2939_, 3);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2987_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2987_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v_traceState_2954_; lean_object* v_env_2955_; lean_object* v_nextMacroScope_2956_; lean_object* v_ngen_2957_; lean_object* v_auxDeclNGen_2958_; lean_object* v_cache_2959_; lean_object* v_recordedDeps_2960_; lean_object* v_messages_2961_; lean_object* v_infoState_2962_; lean_object* v_snapshotTasks_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2986_; 
v___x_2953_ = lean_st_ref_take(v___y_2929_);
v_traceState_2954_ = lean_ctor_get(v___x_2953_, 4);
v_env_2955_ = lean_ctor_get(v___x_2953_, 0);
v_nextMacroScope_2956_ = lean_ctor_get(v___x_2953_, 1);
v_ngen_2957_ = lean_ctor_get(v___x_2953_, 2);
v_auxDeclNGen_2958_ = lean_ctor_get(v___x_2953_, 3);
v_cache_2959_ = lean_ctor_get(v___x_2953_, 5);
v_recordedDeps_2960_ = lean_ctor_get(v___x_2953_, 6);
v_messages_2961_ = lean_ctor_get(v___x_2953_, 7);
v_infoState_2962_ = lean_ctor_get(v___x_2953_, 8);
v_snapshotTasks_2963_ = lean_ctor_get(v___x_2953_, 9);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2965_ = v___x_2953_;
v_isShared_2966_ = v_isSharedCheck_2986_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_snapshotTasks_2963_);
lean_inc(v_infoState_2962_);
lean_inc(v_messages_2961_);
lean_inc(v_recordedDeps_2960_);
lean_inc(v_cache_2959_);
lean_inc(v_traceState_2954_);
lean_inc(v_auxDeclNGen_2958_);
lean_inc(v_ngen_2957_);
lean_inc(v_nextMacroScope_2956_);
lean_inc(v_env_2955_);
lean_dec(v___x_2953_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2986_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
uint64_t v_tid_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2984_; 
v_tid_2967_ = lean_ctor_get_uint64(v_traceState_2954_, sizeof(void*)*1);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_traceState_2954_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v_traceState_2954_, 0);
lean_dec(v_unused_2985_);
v___x_2969_ = v_traceState_2954_;
v_isShared_2970_ = v_isSharedCheck_2984_;
goto v_resetjp_2968_;
}
else
{
lean_dec(v_traceState_2954_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2984_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v_ref_2926_);
lean_ctor_set(v___x_2972_, 1, v_a_2949_);
v___x_2973_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2924_, v___x_2972_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2973_);
v___x_2975_ = v___x_2969_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2973_);
lean_ctor_set_uint64(v_reuseFailAlloc_2983_, sizeof(void*)*1, v_tid_2967_);
v___x_2975_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 4, v___x_2975_);
v___x_2977_ = v___x_2965_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_env_2955_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_nextMacroScope_2956_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_ngen_2957_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_auxDeclNGen_2958_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v_cache_2959_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_recordedDeps_2960_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_messages_2961_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_infoState_2962_);
lean_ctor_set(v_reuseFailAlloc_2982_, 9, v_snapshotTasks_2963_);
v___x_2977_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = lean_st_ref_put(v___y_2929_, v___x_2977_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2971_);
v___x_2980_ = v___x_2951_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2971_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2988_, lean_object* v_data_2989_, lean_object* v_ref_2990_, lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2988_, v_data_2989_, v_ref_2990_, v_msg_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
return v_res_2995_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2998_ = l_Lean_stringToMessageData(v___x_2997_);
return v___x_2998_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2999_; double v___x_3000_; 
v___x_2999_ = lean_unsigned_to_nat(1000u);
v___x_3000_ = lean_float_of_nat(v___x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_3001_, uint8_t v_collapsed_3002_, lean_object* v_tag_3003_, lean_object* v_opts_3004_, uint8_t v_clsEnabled_3005_, lean_object* v_oldTraces_3006_, lean_object* v_msg_3007_, lean_object* v_resStartStop_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_fst_3012_; lean_object* v_snd_3013_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v_data_3017_; lean_object* v_fst_3028_; lean_object* v_snd_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; lean_object* v___y_3033_; lean_object* v_a_3034_; uint8_t v___y_3049_; double v___y_3081_; 
v_fst_3012_ = lean_ctor_get(v_resStartStop_3008_, 0);
lean_inc(v_fst_3012_);
v_snd_3013_ = lean_ctor_get(v_resStartStop_3008_, 1);
lean_inc(v_snd_3013_);
lean_dec_ref(v_resStartStop_3008_);
v_fst_3028_ = lean_ctor_get(v_snd_3013_, 0);
lean_inc(v_fst_3028_);
v_snd_3029_ = lean_ctor_get(v_snd_3013_, 1);
lean_inc(v_snd_3029_);
lean_dec(v_snd_3013_);
v___x_3030_ = l_Lean_trace_profiler;
v___x_3031_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_3004_, v___x_3030_);
if (v___x_3031_ == 0)
{
v___y_3049_ = v___x_3031_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3087_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_3004_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; double v___x_3090_; double v___x_3091_; double v___x_3092_; 
v___x_3088_ = l_Lean_trace_profiler_threshold;
v___x_3089_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_3004_, v___x_3088_);
v___x_3090_ = lean_float_of_nat(v___x_3089_);
v___x_3091_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3092_ = lean_float_div(v___x_3090_, v___x_3091_);
v___y_3081_ = v___x_3092_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; double v___x_3095_; 
v___x_3093_ = l_Lean_trace_profiler_threshold;
v___x_3094_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_3004_, v___x_3093_);
v___x_3095_ = lean_float_of_nat(v___x_3094_);
v___y_3081_ = v___x_3095_;
goto v___jp_3080_;
}
}
v___jp_3014_:
{
lean_object* v___x_3018_; 
lean_inc(v___y_3016_);
v___x_3018_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_3006_, v_data_3017_, v___y_3016_, v___y_3015_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3019_; 
lean_dec_ref_known(v___x_3018_, 1);
v___x_3019_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_3012_);
return v___x_3019_;
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_fst_3012_);
v_a_3020_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3018_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3018_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
v___jp_3032_:
{
uint8_t v_result_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; double v___x_3038_; lean_object* v_data_3039_; 
v_result_3035_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_3012_);
v___x_3036_ = lean_box(v_result_3035_);
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
v___x_3038_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0);
lean_inc_ref(v_tag_3003_);
lean_inc_ref(v___x_3037_);
lean_inc(v_cls_3001_);
v_data_3039_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3039_, 0, v_cls_3001_);
lean_ctor_set(v_data_3039_, 1, v___x_3037_);
lean_ctor_set(v_data_3039_, 2, v_tag_3003_);
lean_ctor_set_float(v_data_3039_, sizeof(void*)*3, v___x_3038_);
lean_ctor_set_float(v_data_3039_, sizeof(void*)*3 + 8, v___x_3038_);
lean_ctor_set_uint8(v_data_3039_, sizeof(void*)*3 + 16, v_collapsed_3002_);
if (v___x_3031_ == 0)
{
lean_dec_ref_known(v___x_3037_, 1);
lean_dec(v_snd_3029_);
lean_dec(v_fst_3028_);
lean_dec_ref(v_tag_3003_);
lean_dec(v_cls_3001_);
v___y_3015_ = v_a_3034_;
v___y_3016_ = v___y_3033_;
v_data_3017_ = v_data_3039_;
goto v___jp_3014_;
}
else
{
lean_object* v_data_3040_; double v___x_3041_; double v___x_3042_; 
lean_dec_ref_known(v_data_3039_, 3);
v_data_3040_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3040_, 0, v_cls_3001_);
lean_ctor_set(v_data_3040_, 1, v___x_3037_);
lean_ctor_set(v_data_3040_, 2, v_tag_3003_);
v___x_3041_ = lean_unbox_float(v_fst_3028_);
lean_dec(v_fst_3028_);
lean_ctor_set_float(v_data_3040_, sizeof(void*)*3, v___x_3041_);
v___x_3042_ = lean_unbox_float(v_snd_3029_);
lean_dec(v_snd_3029_);
lean_ctor_set_float(v_data_3040_, sizeof(void*)*3 + 8, v___x_3042_);
lean_ctor_set_uint8(v_data_3040_, sizeof(void*)*3 + 16, v_collapsed_3002_);
v___y_3015_ = v_a_3034_;
v___y_3016_ = v___y_3033_;
v_data_3017_ = v_data_3040_;
goto v___jp_3014_;
}
}
v___jp_3043_:
{
lean_object* v_ref_3044_; lean_object* v___x_3045_; 
v_ref_3044_ = lean_ctor_get(v___y_3009_, 2);
lean_inc(v___y_3010_);
lean_inc_ref(v___y_3009_);
lean_inc(v_fst_3012_);
v___x_3045_ = lean_apply_4(v_msg_3007_, v_fst_3012_, v___y_3009_, v___y_3010_, lean_box(0));
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___y_3033_ = v_ref_3044_;
v_a_3034_ = v_a_3046_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3047_; 
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_3033_ = v_ref_3044_;
v_a_3034_ = v___x_3047_;
goto v___jp_3032_;
}
}
v___jp_3048_:
{
if (v_clsEnabled_3005_ == 0)
{
if (v___y_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v_traceState_3051_; lean_object* v_env_3052_; lean_object* v_nextMacroScope_3053_; lean_object* v_ngen_3054_; lean_object* v_auxDeclNGen_3055_; lean_object* v_cache_3056_; lean_object* v_recordedDeps_3057_; lean_object* v_messages_3058_; lean_object* v_infoState_3059_; lean_object* v_snapshotTasks_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_snd_3029_);
lean_dec(v_fst_3028_);
lean_dec_ref(v_msg_3007_);
lean_dec_ref(v_tag_3003_);
lean_dec(v_cls_3001_);
v___x_3050_ = lean_st_ref_take(v___y_3010_);
v_traceState_3051_ = lean_ctor_get(v___x_3050_, 4);
v_env_3052_ = lean_ctor_get(v___x_3050_, 0);
v_nextMacroScope_3053_ = lean_ctor_get(v___x_3050_, 1);
v_ngen_3054_ = lean_ctor_get(v___x_3050_, 2);
v_auxDeclNGen_3055_ = lean_ctor_get(v___x_3050_, 3);
v_cache_3056_ = lean_ctor_get(v___x_3050_, 5);
v_recordedDeps_3057_ = lean_ctor_get(v___x_3050_, 6);
v_messages_3058_ = lean_ctor_get(v___x_3050_, 7);
v_infoState_3059_ = lean_ctor_get(v___x_3050_, 8);
v_snapshotTasks_3060_ = lean_ctor_get(v___x_3050_, 9);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3062_ = v___x_3050_;
v_isShared_3063_ = v_isSharedCheck_3079_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_snapshotTasks_3060_);
lean_inc(v_infoState_3059_);
lean_inc(v_messages_3058_);
lean_inc(v_recordedDeps_3057_);
lean_inc(v_cache_3056_);
lean_inc(v_traceState_3051_);
lean_inc(v_auxDeclNGen_3055_);
lean_inc(v_ngen_3054_);
lean_inc(v_nextMacroScope_3053_);
lean_inc(v_env_3052_);
lean_dec(v___x_3050_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3079_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
uint64_t v_tid_3064_; lean_object* v_traces_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3078_; 
v_tid_3064_ = lean_ctor_get_uint64(v_traceState_3051_, sizeof(void*)*1);
v_traces_3065_ = lean_ctor_get(v_traceState_3051_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_traceState_3051_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3067_ = v_traceState_3051_;
v_isShared_3068_ = v_isSharedCheck_3078_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_traces_3065_);
lean_dec(v_traceState_3051_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3078_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3069_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3006_, v_traces_3065_);
lean_dec_ref(v_traces_3065_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 0, v___x_3069_);
v___x_3071_ = v___x_3067_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3069_);
lean_ctor_set_uint64(v_reuseFailAlloc_3077_, sizeof(void*)*1, v_tid_3064_);
v___x_3071_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3073_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v___x_3071_);
v___x_3073_ = v___x_3062_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_env_3052_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_nextMacroScope_3053_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_ngen_3054_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_auxDeclNGen_3055_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3076_, 5, v_cache_3056_);
lean_ctor_set(v_reuseFailAlloc_3076_, 6, v_recordedDeps_3057_);
lean_ctor_set(v_reuseFailAlloc_3076_, 7, v_messages_3058_);
lean_ctor_set(v_reuseFailAlloc_3076_, 8, v_infoState_3059_);
lean_ctor_set(v_reuseFailAlloc_3076_, 9, v_snapshotTasks_3060_);
v___x_3073_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_st_ref_put(v___y_3010_, v___x_3073_);
v___x_3075_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_3012_);
return v___x_3075_;
}
}
}
}
}
else
{
goto v___jp_3043_;
}
}
else
{
goto v___jp_3043_;
}
}
v___jp_3080_:
{
double v___x_3082_; double v___x_3083_; double v___x_3084_; uint8_t v___x_3085_; 
v___x_3082_ = lean_unbox_float(v_snd_3029_);
v___x_3083_ = lean_unbox_float(v_fst_3028_);
v___x_3084_ = lean_float_sub(v___x_3082_, v___x_3083_);
v___x_3085_ = lean_float_decLt(v___y_3081_, v___x_3084_);
v___y_3049_ = v___x_3085_;
goto v___jp_3048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3096_, lean_object* v_collapsed_3097_, lean_object* v_tag_3098_, lean_object* v_opts_3099_, lean_object* v_clsEnabled_3100_, lean_object* v_oldTraces_3101_, lean_object* v_msg_3102_, lean_object* v_resStartStop_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
uint8_t v_collapsed_boxed_3107_; uint8_t v_clsEnabled_boxed_3108_; lean_object* v_res_3109_; 
v_collapsed_boxed_3107_ = lean_unbox(v_collapsed_3097_);
v_clsEnabled_boxed_3108_ = lean_unbox(v_clsEnabled_3100_);
v_res_3109_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3096_, v_collapsed_boxed_3107_, v_tag_3098_, v_opts_3099_, v_clsEnabled_boxed_3108_, v_oldTraces_3101_, v_msg_3102_, v_resStartStop_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v_opts_3099_);
return v_res_3109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
lean_ctor_set(v___x_3114_, 2, v___x_3113_);
lean_ctor_set(v___x_3114_, 3, v___x_3113_);
lean_ctor_set(v___x_3114_, 4, v___x_3112_);
lean_ctor_set(v___x_3114_, 5, v___x_3112_);
lean_ctor_set(v___x_3114_, 6, v___x_3112_);
lean_ctor_set(v___x_3114_, 7, v___x_3112_);
lean_ctor_set(v___x_3114_, 8, v___x_3112_);
lean_ctor_set(v___x_3114_, 9, v___x_3112_);
lean_ctor_set(v___x_3114_, 10, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
lean_ctor_set(v___x_3119_, 2, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3120_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3121_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3122_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3123_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
v___x_3124_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set(v___x_3124_, 1, v___x_3122_);
lean_ctor_set(v___x_3124_, 2, v___x_3121_);
lean_ctor_set(v___x_3124_, 3, v___x_3122_);
lean_ctor_set(v___x_3124_, 4, v___x_3122_);
lean_ctor_set(v___x_3124_, 5, v___x_3122_);
lean_ctor_set(v___x_3124_, 6, v___x_3120_);
return v___x_3124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
lean_ctor_set(v___x_3126_, 2, v___x_3125_);
lean_ctor_set(v___x_3126_, 3, v___x_3125_);
lean_ctor_set(v___x_3126_, 4, v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3132_ = l_Lean_Name_append(v___x_3131_, v___x_3130_);
return v___x_3132_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3133_; double v___x_3134_; 
v___x_3133_ = lean_unsigned_to_nat(1000000000u);
v___x_3134_ = lean_float_of_nat(v___x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3135_, lean_object* v___f_3136_, lean_object* v_name_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_toCold_3141_; lean_object* v_options_3142_; uint8_t v_hasTrace_3143_; 
v_toCold_3141_ = lean_ctor_get(v___y_3138_, 0);
v_options_3142_ = lean_ctor_get(v_toCold_3141_, 2);
v_hasTrace_3143_ = lean_ctor_get_uint8(v_options_3142_, sizeof(void*)*1);
if (v_hasTrace_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v_env_3145_; lean_object* v___x_3146_; 
lean_dec_ref(v___f_3136_);
v___x_3144_ = lean_st_ref_get(v___y_3139_);
v_env_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc_ref(v_env_3145_);
lean_dec(v___x_3144_);
lean_inc(v_name_3137_);
v___x_3146_ = l_Lean_Meta_declFromEqLikeName(v_env_3145_, v_name_3137_);
if (lean_obj_tag(v___x_3146_) == 1)
{
lean_object* v_val_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3248_; 
v_val_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3248_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_val_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3248_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_fst_3151_; lean_object* v_snd_3152_; lean_object* v___x_3153_; lean_object* v_env_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v_fst_3151_ = lean_ctor_get(v_val_3147_, 0);
lean_inc_n(v_fst_3151_, 2);
v_snd_3152_ = lean_ctor_get(v_val_3147_, 1);
lean_inc_n(v_snd_3152_, 2);
lean_dec(v_val_3147_);
v___x_3153_ = lean_st_ref_get(v___y_3139_);
v_env_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc_ref(v_env_3154_);
lean_dec(v___x_3153_);
v___x_3155_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3154_, v_fst_3151_, v_snd_3152_);
v___x_3156_ = lean_name_eq(v_name_3137_, v___x_3155_);
lean_dec(v___x_3155_);
lean_dec(v_name_3137_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
lean_dec(v_snd_3152_);
lean_dec(v_fst_3151_);
lean_dec(v___x_3135_);
v___x_3157_ = lean_box(v_hasTrace_3143_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3157_);
v___x_3159_ = v___x_3149_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
else
{
uint8_t v___x_3161_; 
lean_inc(v_snd_3152_);
v___x_3161_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3152_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3163_ = lean_string_dec_eq(v_snd_3152_, v___x_3162_);
lean_dec(v_snd_3152_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
lean_dec(v_fst_3151_);
lean_dec(v___x_3135_);
v___x_3164_ = lean_box(v_hasTrace_3143_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3164_);
v___x_3166_ = v___x_3149_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
else
{
uint8_t v___x_3168_; uint8_t v___x_3169_; uint8_t v___x_3170_; lean_object* v___x_3171_; uint64_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_del_object(v___x_3149_);
v___x_3168_ = 1;
v___x_3169_ = 0;
v___x_3170_ = 2;
v___x_3171_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3171_, 0, v___x_3161_);
lean_ctor_set_uint8(v___x_3171_, 1, v___x_3161_);
lean_ctor_set_uint8(v___x_3171_, 2, v___x_3161_);
lean_ctor_set_uint8(v___x_3171_, 3, v___x_3161_);
lean_ctor_set_uint8(v___x_3171_, 4, v___x_3161_);
lean_ctor_set_uint8(v___x_3171_, 5, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 6, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 7, v___x_3161_);
lean_ctor_set_uint8(v___x_3171_, 8, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 9, v___x_3168_);
lean_ctor_set_uint8(v___x_3171_, 10, v___x_3169_);
lean_ctor_set_uint8(v___x_3171_, 11, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 12, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 13, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 14, v___x_3170_);
lean_ctor_set_uint8(v___x_3171_, 15, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 16, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 17, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 18, v___x_3163_);
lean_ctor_set_uint8(v___x_3171_, 19, v___x_3161_);
lean_ctor_set_uint8(v___x_3171_, 20, v___x_3163_);
v___x_3172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3171_);
v___x_3173_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3173_, 0, v___x_3171_);
lean_ctor_set_uint64(v___x_3173_, sizeof(void*)*1, v___x_3172_);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3176_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3177_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3178_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3179_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3179_, 0, v___x_3173_);
lean_ctor_set(v___x_3179_, 1, v___x_3135_);
lean_ctor_set(v___x_3179_, 2, v___x_3176_);
lean_ctor_set(v___x_3179_, 3, v___x_3177_);
lean_ctor_set(v___x_3179_, 4, v___x_3178_);
lean_ctor_set(v___x_3179_, 5, v___x_3174_);
lean_ctor_set(v___x_3179_, 6, v___x_3178_);
lean_ctor_set_uint8(v___x_3179_, sizeof(void*)*7, v___x_3161_);
lean_ctor_set_uint8(v___x_3179_, sizeof(void*)*7 + 1, v___x_3161_);
lean_ctor_set_uint8(v___x_3179_, sizeof(void*)*7 + 2, v___x_3161_);
lean_ctor_set_uint8(v___x_3179_, sizeof(void*)*7 + 3, v___x_3156_);
v___x_3180_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3181_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3182_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3180_);
lean_ctor_set(v___x_3183_, 1, v___x_3181_);
lean_ctor_set(v___x_3183_, 2, v___x_3135_);
lean_ctor_set(v___x_3183_, 3, v___x_3175_);
lean_ctor_set(v___x_3183_, 4, v___x_3182_);
v___x_3184_ = lean_st_mk_ref(v___x_3183_);
v___x_3185_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3151_, v___x_3156_, v___x_3179_, v___x_3184_, v___y_3138_, v___y_3139_);
lean_dec_ref_known(v___x_3179_, 7);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3199_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3199_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3199_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_st_ref_get(v___x_3184_);
lean_dec(v___x_3184_);
lean_dec(v___x_3190_);
if (lean_obj_tag(v_a_3186_) == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3191_ = lean_box(v___x_3161_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3191_);
v___x_3193_ = v___x_3188_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_dec_ref_known(v_a_3186_, 1);
v___x_3195_ = lean_box(v___x_3163_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3195_);
v___x_3197_ = v___x_3188_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v___x_3184_);
v_a_3200_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3185_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3185_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
uint8_t v___x_3208_; uint8_t v___x_3209_; uint8_t v___x_3210_; lean_object* v___x_3211_; uint64_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec(v_snd_3152_);
lean_del_object(v___x_3149_);
v___x_3208_ = 1;
v___x_3209_ = 0;
v___x_3210_ = 2;
v___x_3211_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3211_, 0, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3211_, 1, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3211_, 2, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3211_, 3, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3211_, 4, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3211_, 5, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 6, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 7, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3211_, 8, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 9, v___x_3208_);
lean_ctor_set_uint8(v___x_3211_, 10, v___x_3209_);
lean_ctor_set_uint8(v___x_3211_, 11, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 12, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 13, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 14, v___x_3210_);
lean_ctor_set_uint8(v___x_3211_, 15, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 16, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 17, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 18, v___x_3161_);
lean_ctor_set_uint8(v___x_3211_, 19, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3211_, 20, v___x_3161_);
v___x_3212_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3213_, 0, v___x_3211_);
lean_ctor_set_uint64(v___x_3213_, sizeof(void*)*1, v___x_3212_);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3216_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3217_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3218_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3219_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3219_, 0, v___x_3213_);
lean_ctor_set(v___x_3219_, 1, v___x_3135_);
lean_ctor_set(v___x_3219_, 2, v___x_3216_);
lean_ctor_set(v___x_3219_, 3, v___x_3217_);
lean_ctor_set(v___x_3219_, 4, v___x_3218_);
lean_ctor_set(v___x_3219_, 5, v___x_3214_);
lean_ctor_set(v___x_3219_, 6, v___x_3218_);
lean_ctor_set_uint8(v___x_3219_, sizeof(void*)*7, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3219_, sizeof(void*)*7 + 1, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3219_, sizeof(void*)*7 + 2, v_hasTrace_3143_);
lean_ctor_set_uint8(v___x_3219_, sizeof(void*)*7 + 3, v___x_3156_);
v___x_3220_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3221_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3222_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3220_);
lean_ctor_set(v___x_3223_, 1, v___x_3221_);
lean_ctor_set(v___x_3223_, 2, v___x_3135_);
lean_ctor_set(v___x_3223_, 3, v___x_3215_);
lean_ctor_set(v___x_3223_, 4, v___x_3222_);
v___x_3224_ = lean_st_mk_ref(v___x_3223_);
v___x_3225_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3151_, v___x_3219_, v___x_3224_, v___y_3138_, v___y_3139_);
lean_dec_ref_known(v___x_3219_, 7);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3239_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3239_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3239_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_st_ref_get(v___x_3224_);
lean_dec(v___x_3224_);
lean_dec(v___x_3230_);
if (lean_obj_tag(v_a_3226_) == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3231_ = lean_box(v_hasTrace_3143_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3231_);
v___x_3233_ = v___x_3228_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_dec_ref_known(v_a_3226_, 1);
v___x_3235_ = lean_box(v___x_3161_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3235_);
v___x_3237_ = v___x_3228_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v___x_3224_);
v_a_3240_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3225_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3225_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
lean_dec(v___x_3146_);
lean_dec(v_name_3137_);
lean_dec(v___x_3135_);
v___x_3249_ = lean_box(v_hasTrace_3143_);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3251_; lean_object* v___f_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v_a_3260_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v_a_3275_; lean_object* v___y_3278_; lean_object* v___y_3279_; uint8_t v_a_3280_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v_a_3286_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v_a_3298_; lean_object* v___y_3301_; lean_object* v___y_3302_; uint8_t v_a_3303_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; 
v_inheritedTraceOptions_3251_ = lean_ctor_get(v_toCold_3141_, 11);
lean_inc(v_name_3137_);
v___f_3252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3252_, 0, v_name_3137_);
v___x_3253_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3254_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1));
v___x_3255_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3251_, v_options_3142_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = l_Lean_trace_profiler;
v___x_3438_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3142_, v___x_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; lean_object* v_env_3440_; lean_object* v___x_3441_; 
lean_dec_ref(v___f_3252_);
lean_dec_ref(v___f_3136_);
v___x_3439_ = lean_st_ref_get(v___y_3139_);
v_env_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc_ref(v_env_3440_);
lean_dec(v___x_3439_);
lean_inc(v_name_3137_);
v___x_3441_ = l_Lean_Meta_declFromEqLikeName(v_env_3440_, v_name_3137_);
if (lean_obj_tag(v___x_3441_) == 1)
{
lean_object* v_val_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3543_; 
v_val_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3543_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_val_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3543_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v_fst_3446_; lean_object* v_snd_3447_; lean_object* v___x_3448_; lean_object* v_env_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v_fst_3446_ = lean_ctor_get(v_val_3442_, 0);
lean_inc_n(v_fst_3446_, 2);
v_snd_3447_ = lean_ctor_get(v_val_3442_, 1);
lean_inc_n(v_snd_3447_, 2);
lean_dec(v_val_3442_);
v___x_3448_ = lean_st_ref_get(v___y_3139_);
v_env_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc_ref(v_env_3449_);
lean_dec(v___x_3448_);
v___x_3450_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3449_, v_fst_3446_, v_snd_3447_);
v___x_3451_ = lean_name_eq(v_name_3137_, v___x_3450_);
lean_dec(v___x_3450_);
lean_dec(v_name_3137_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
lean_dec(v_snd_3447_);
lean_dec(v_fst_3446_);
lean_dec(v___x_3135_);
v___x_3452_ = lean_box(v___x_3438_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set_tag(v___x_3444_, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3452_);
v___x_3454_ = v___x_3444_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
else
{
uint8_t v___x_3456_; 
lean_inc(v_snd_3447_);
v___x_3456_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3447_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3458_ = lean_string_dec_eq(v_snd_3447_, v___x_3457_);
lean_dec(v_snd_3447_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
lean_dec(v_fst_3446_);
lean_dec(v___x_3135_);
v___x_3459_ = lean_box(v___x_3438_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set_tag(v___x_3444_, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3459_);
v___x_3461_ = v___x_3444_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
else
{
uint8_t v___x_3463_; uint8_t v___x_3464_; uint8_t v___x_3465_; lean_object* v___x_3466_; uint64_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_del_object(v___x_3444_);
v___x_3463_ = 1;
v___x_3464_ = 0;
v___x_3465_ = 2;
v___x_3466_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3466_, 0, v___x_3456_);
lean_ctor_set_uint8(v___x_3466_, 1, v___x_3456_);
lean_ctor_set_uint8(v___x_3466_, 2, v___x_3456_);
lean_ctor_set_uint8(v___x_3466_, 3, v___x_3456_);
lean_ctor_set_uint8(v___x_3466_, 4, v___x_3456_);
lean_ctor_set_uint8(v___x_3466_, 5, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 6, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 7, v___x_3456_);
lean_ctor_set_uint8(v___x_3466_, 8, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 9, v___x_3463_);
lean_ctor_set_uint8(v___x_3466_, 10, v___x_3464_);
lean_ctor_set_uint8(v___x_3466_, 11, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 12, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 13, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 14, v___x_3465_);
lean_ctor_set_uint8(v___x_3466_, 15, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 16, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 17, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 18, v___x_3458_);
lean_ctor_set_uint8(v___x_3466_, 19, v___x_3456_);
lean_ctor_set_uint8(v___x_3466_, 20, v___x_3458_);
v___x_3467_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set_uint64(v___x_3468_, sizeof(void*)*1, v___x_3467_);
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3471_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3472_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3473_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3474_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3474_, 0, v___x_3468_);
lean_ctor_set(v___x_3474_, 1, v___x_3135_);
lean_ctor_set(v___x_3474_, 2, v___x_3471_);
lean_ctor_set(v___x_3474_, 3, v___x_3472_);
lean_ctor_set(v___x_3474_, 4, v___x_3473_);
lean_ctor_set(v___x_3474_, 5, v___x_3469_);
lean_ctor_set(v___x_3474_, 6, v___x_3473_);
lean_ctor_set_uint8(v___x_3474_, sizeof(void*)*7, v___x_3456_);
lean_ctor_set_uint8(v___x_3474_, sizeof(void*)*7 + 1, v___x_3456_);
lean_ctor_set_uint8(v___x_3474_, sizeof(void*)*7 + 2, v___x_3456_);
lean_ctor_set_uint8(v___x_3474_, sizeof(void*)*7 + 3, v_hasTrace_3143_);
v___x_3475_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3476_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3477_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3475_);
lean_ctor_set(v___x_3478_, 1, v___x_3476_);
lean_ctor_set(v___x_3478_, 2, v___x_3135_);
lean_ctor_set(v___x_3478_, 3, v___x_3470_);
lean_ctor_set(v___x_3478_, 4, v___x_3477_);
v___x_3479_ = lean_st_mk_ref(v___x_3478_);
v___x_3480_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3446_, v_hasTrace_3143_, v___x_3474_, v___x_3479_, v___y_3138_, v___y_3139_);
lean_dec_ref_known(v___x_3474_, 7);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3494_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3494_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3494_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_st_ref_get(v___x_3479_);
lean_dec(v___x_3479_);
lean_dec(v___x_3485_);
if (lean_obj_tag(v_a_3481_) == 0)
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = lean_box(v___x_3456_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3486_);
v___x_3488_ = v___x_3483_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_dec_ref_known(v_a_3481_, 1);
v___x_3490_ = lean_box(v___x_3458_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3490_);
v___x_3492_ = v___x_3483_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v___x_3479_);
v_a_3495_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3480_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3480_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
else
{
uint8_t v___x_3503_; uint8_t v___x_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; uint64_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec(v_snd_3447_);
lean_del_object(v___x_3444_);
v___x_3503_ = 1;
v___x_3504_ = 0;
v___x_3505_ = 2;
v___x_3506_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3506_, 0, v___x_3438_);
lean_ctor_set_uint8(v___x_3506_, 1, v___x_3438_);
lean_ctor_set_uint8(v___x_3506_, 2, v___x_3438_);
lean_ctor_set_uint8(v___x_3506_, 3, v___x_3438_);
lean_ctor_set_uint8(v___x_3506_, 4, v___x_3438_);
lean_ctor_set_uint8(v___x_3506_, 5, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 6, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 7, v___x_3438_);
lean_ctor_set_uint8(v___x_3506_, 8, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 9, v___x_3503_);
lean_ctor_set_uint8(v___x_3506_, 10, v___x_3504_);
lean_ctor_set_uint8(v___x_3506_, 11, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 12, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 13, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 14, v___x_3505_);
lean_ctor_set_uint8(v___x_3506_, 15, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 16, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 17, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 18, v___x_3456_);
lean_ctor_set_uint8(v___x_3506_, 19, v___x_3438_);
lean_ctor_set_uint8(v___x_3506_, 20, v___x_3456_);
v___x_3507_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3506_);
v___x_3508_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3508_, 0, v___x_3506_);
lean_ctor_set_uint64(v___x_3508_, sizeof(void*)*1, v___x_3507_);
v___x_3509_ = lean_unsigned_to_nat(0u);
v___x_3510_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3511_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3512_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3513_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3514_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3514_, 0, v___x_3508_);
lean_ctor_set(v___x_3514_, 1, v___x_3135_);
lean_ctor_set(v___x_3514_, 2, v___x_3511_);
lean_ctor_set(v___x_3514_, 3, v___x_3512_);
lean_ctor_set(v___x_3514_, 4, v___x_3513_);
lean_ctor_set(v___x_3514_, 5, v___x_3509_);
lean_ctor_set(v___x_3514_, 6, v___x_3513_);
lean_ctor_set_uint8(v___x_3514_, sizeof(void*)*7, v___x_3438_);
lean_ctor_set_uint8(v___x_3514_, sizeof(void*)*7 + 1, v___x_3438_);
lean_ctor_set_uint8(v___x_3514_, sizeof(void*)*7 + 2, v___x_3438_);
lean_ctor_set_uint8(v___x_3514_, sizeof(void*)*7 + 3, v_hasTrace_3143_);
v___x_3515_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3516_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3515_);
lean_ctor_set(v___x_3518_, 1, v___x_3516_);
lean_ctor_set(v___x_3518_, 2, v___x_3135_);
lean_ctor_set(v___x_3518_, 3, v___x_3510_);
lean_ctor_set(v___x_3518_, 4, v___x_3517_);
v___x_3519_ = lean_st_mk_ref(v___x_3518_);
v___x_3520_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3446_, v___x_3514_, v___x_3519_, v___y_3138_, v___y_3139_);
lean_dec_ref_known(v___x_3514_, 7);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3534_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3523_ = v___x_3520_;
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_st_ref_get(v___x_3519_);
lean_dec(v___x_3519_);
lean_dec(v___x_3525_);
if (lean_obj_tag(v_a_3521_) == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = lean_box(v___x_3438_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3526_);
v___x_3528_ = v___x_3523_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
lean_dec_ref_known(v_a_3521_, 1);
v___x_3530_ = lean_box(v___x_3456_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3530_);
v___x_3532_ = v___x_3523_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec(v___x_3519_);
v_a_3535_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3520_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3520_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v___x_3441_);
lean_dec(v_name_3137_);
lean_dec(v___x_3135_);
v___x_3544_ = lean_box(v___x_3438_);
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
}
else
{
goto v___jp_3313_;
}
}
else
{
goto v___jp_3313_;
}
v___jp_3257_:
{
lean_object* v___x_3261_; double v___x_3262_; double v___x_3263_; double v___x_3264_; double v___x_3265_; double v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3261_ = lean_io_mono_nanos_now();
v___x_3262_ = lean_float_of_nat(v___y_3258_);
v___x_3263_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3264_ = lean_float_div(v___x_3262_, v___x_3263_);
v___x_3265_ = lean_float_of_nat(v___x_3261_);
v___x_3266_ = lean_float_div(v___x_3265_, v___x_3263_);
v___x_3267_ = lean_box_float(v___x_3264_);
v___x_3268_ = lean_box_float(v___x_3266_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_a_3260_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3253_, v_hasTrace_3143_, v___x_3254_, v_options_3142_, v___x_3256_, v___y_3259_, v___f_3252_, v___x_3270_, v___y_3138_, v___y_3139_);
return v___x_3271_;
}
v___jp_3272_:
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3275_);
v___y_3258_ = v___y_3273_;
v___y_3259_ = v___y_3274_;
v_a_3260_ = v___x_3276_;
goto v___jp_3257_;
}
v___jp_3277_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = lean_box(v_a_3280_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
v___y_3258_ = v___y_3278_;
v___y_3259_ = v___y_3279_;
v_a_3260_ = v___x_3282_;
goto v___jp_3257_;
}
v___jp_3283_:
{
lean_object* v___x_3287_; double v___x_3288_; double v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3287_ = lean_io_get_num_heartbeats();
v___x_3288_ = lean_float_of_nat(v___y_3285_);
v___x_3289_ = lean_float_of_nat(v___x_3287_);
v___x_3290_ = lean_box_float(v___x_3288_);
v___x_3291_ = lean_box_float(v___x_3289_);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_a_3286_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3253_, v_hasTrace_3143_, v___x_3254_, v_options_3142_, v___x_3256_, v___y_3284_, v___f_3252_, v___x_3293_, v___y_3138_, v___y_3139_);
return v___x_3294_;
}
v___jp_3295_:
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_a_3298_);
v___y_3284_ = v___y_3296_;
v___y_3285_ = v___y_3297_;
v_a_3286_ = v___x_3299_;
goto v___jp_3283_;
}
v___jp_3300_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_box(v_a_3303_);
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
v___y_3284_ = v___y_3301_;
v___y_3285_ = v___y_3302_;
v_a_3286_ = v___x_3305_;
goto v___jp_3283_;
}
v___jp_3306_:
{
if (lean_obj_tag(v___y_3309_) == 0)
{
lean_object* v_a_3310_; uint8_t v___x_3311_; 
v_a_3310_ = lean_ctor_get(v___y_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___y_3309_, 1);
v___x_3311_ = lean_unbox(v_a_3310_);
lean_dec(v_a_3310_);
v___y_3301_ = v___y_3307_;
v___y_3302_ = v___y_3308_;
v_a_3303_ = v___x_3311_;
goto v___jp_3300_;
}
else
{
lean_object* v_a_3312_; 
v_a_3312_ = lean_ctor_get(v___y_3309_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___y_3309_, 1);
v___y_3296_ = v___y_3307_;
v___y_3297_ = v___y_3308_;
v_a_3298_ = v_a_3312_;
goto v___jp_3295_;
}
}
v___jp_3313_:
{
lean_object* v___x_3314_; lean_object* v_a_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3314_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3139_);
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3317_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3142_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_env_3320_; lean_object* v___x_3321_; 
lean_dec_ref(v___f_3136_);
v___x_3318_ = lean_io_mono_nanos_now();
v___x_3319_ = lean_st_ref_get(v___y_3139_);
v_env_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc_ref(v_env_3320_);
lean_dec(v___x_3319_);
lean_inc(v_name_3137_);
v___x_3321_ = l_Lean_Meta_declFromEqLikeName(v_env_3320_, v_name_3137_);
if (lean_obj_tag(v___x_3321_) == 1)
{
lean_object* v_val_3322_; lean_object* v_fst_3323_; lean_object* v_snd_3324_; lean_object* v___x_3325_; lean_object* v_env_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v_val_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_val_3322_);
lean_dec_ref_known(v___x_3321_, 1);
v_fst_3323_ = lean_ctor_get(v_val_3322_, 0);
lean_inc_n(v_fst_3323_, 2);
v_snd_3324_ = lean_ctor_get(v_val_3322_, 1);
lean_inc_n(v_snd_3324_, 2);
lean_dec(v_val_3322_);
v___x_3325_ = lean_st_ref_get(v___y_3139_);
v_env_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc_ref(v_env_3326_);
lean_dec(v___x_3325_);
v___x_3327_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3326_, v_fst_3323_, v_snd_3324_);
v___x_3328_ = lean_name_eq(v_name_3137_, v___x_3327_);
lean_dec(v___x_3327_);
lean_dec(v_name_3137_);
if (v___x_3328_ == 0)
{
lean_dec(v_snd_3324_);
lean_dec(v_fst_3323_);
lean_dec(v___x_3135_);
v___y_3278_ = v___x_3318_;
v___y_3279_ = v_a_3315_;
v_a_3280_ = v___x_3317_;
goto v___jp_3277_;
}
else
{
uint8_t v___x_3329_; 
lean_inc(v_snd_3324_);
v___x_3329_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3324_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3330_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3331_ = lean_string_dec_eq(v_snd_3324_, v___x_3330_);
lean_dec(v_snd_3324_);
if (v___x_3331_ == 0)
{
lean_dec(v_fst_3323_);
lean_dec(v___x_3135_);
v___y_3278_ = v___x_3318_;
v___y_3279_ = v_a_3315_;
v_a_3280_ = v___x_3317_;
goto v___jp_3277_;
}
else
{
uint8_t v___x_3332_; uint8_t v___x_3333_; uint8_t v___x_3334_; lean_object* v___x_3335_; uint64_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3332_ = 1;
v___x_3333_ = 0;
v___x_3334_ = 2;
v___x_3335_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3335_, 0, v___x_3329_);
lean_ctor_set_uint8(v___x_3335_, 1, v___x_3329_);
lean_ctor_set_uint8(v___x_3335_, 2, v___x_3329_);
lean_ctor_set_uint8(v___x_3335_, 3, v___x_3329_);
lean_ctor_set_uint8(v___x_3335_, 4, v___x_3329_);
lean_ctor_set_uint8(v___x_3335_, 5, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 6, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 7, v___x_3329_);
lean_ctor_set_uint8(v___x_3335_, 8, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 9, v___x_3332_);
lean_ctor_set_uint8(v___x_3335_, 10, v___x_3333_);
lean_ctor_set_uint8(v___x_3335_, 11, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 12, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 13, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 14, v___x_3334_);
lean_ctor_set_uint8(v___x_3335_, 15, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 16, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 17, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 18, v___x_3331_);
lean_ctor_set_uint8(v___x_3335_, 19, v___x_3329_);
lean_ctor_set_uint8(v___x_3335_, 20, v___x_3331_);
v___x_3336_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3335_);
v___x_3337_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set_uint64(v___x_3337_, sizeof(void*)*1, v___x_3336_);
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3340_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3342_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3343_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3343_, 0, v___x_3337_);
lean_ctor_set(v___x_3343_, 1, v___x_3135_);
lean_ctor_set(v___x_3343_, 2, v___x_3340_);
lean_ctor_set(v___x_3343_, 3, v___x_3341_);
lean_ctor_set(v___x_3343_, 4, v___x_3342_);
lean_ctor_set(v___x_3343_, 5, v___x_3338_);
lean_ctor_set(v___x_3343_, 6, v___x_3342_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7, v___x_3329_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 1, v___x_3329_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 2, v___x_3329_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 3, v_hasTrace_3143_);
v___x_3344_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3345_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3346_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3344_);
lean_ctor_set(v___x_3347_, 1, v___x_3345_);
lean_ctor_set(v___x_3347_, 2, v___x_3135_);
lean_ctor_set(v___x_3347_, 3, v___x_3339_);
lean_ctor_set(v___x_3347_, 4, v___x_3346_);
v___x_3348_ = lean_st_mk_ref(v___x_3347_);
v___x_3349_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3323_, v_hasTrace_3143_, v___x_3343_, v___x_3348_, v___y_3138_, v___y_3139_);
lean_dec_ref_known(v___x_3343_, 7);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
v___x_3351_ = lean_st_ref_get(v___x_3348_);
lean_dec(v___x_3348_);
lean_dec(v___x_3351_);
if (lean_obj_tag(v_a_3350_) == 0)
{
v___y_3278_ = v___x_3318_;
v___y_3279_ = v_a_3315_;
v_a_3280_ = v___x_3329_;
goto v___jp_3277_;
}
else
{
lean_dec_ref_known(v_a_3350_, 1);
v___y_3278_ = v___x_3318_;
v___y_3279_ = v_a_3315_;
v_a_3280_ = v___x_3331_;
goto v___jp_3277_;
}
}
else
{
lean_object* v_a_3352_; 
lean_dec(v___x_3348_);
v_a_3352_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3349_, 1);
v___y_3273_ = v___x_3318_;
v___y_3274_ = v_a_3315_;
v_a_3275_ = v_a_3352_;
goto v___jp_3272_;
}
}
}
else
{
uint8_t v___x_3353_; uint8_t v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; uint64_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec(v_snd_3324_);
v___x_3353_ = 1;
v___x_3354_ = 0;
v___x_3355_ = 2;
v___x_3356_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3356_, 0, v___x_3317_);
lean_ctor_set_uint8(v___x_3356_, 1, v___x_3317_);
lean_ctor_set_uint8(v___x_3356_, 2, v___x_3317_);
lean_ctor_set_uint8(v___x_3356_, 3, v___x_3317_);
lean_ctor_set_uint8(v___x_3356_, 4, v___x_3317_);
lean_ctor_set_uint8(v___x_3356_, 5, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 6, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 7, v___x_3317_);
lean_ctor_set_uint8(v___x_3356_, 8, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 9, v___x_3353_);
lean_ctor_set_uint8(v___x_3356_, 10, v___x_3354_);
lean_ctor_set_uint8(v___x_3356_, 11, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 12, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 13, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 14, v___x_3355_);
lean_ctor_set_uint8(v___x_3356_, 15, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 16, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 17, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 18, v___x_3329_);
lean_ctor_set_uint8(v___x_3356_, 19, v___x_3317_);
lean_ctor_set_uint8(v___x_3356_, 20, v___x_3329_);
v___x_3357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set_uint64(v___x_3358_, sizeof(void*)*1, v___x_3357_);
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3361_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3363_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3364_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3364_, 0, v___x_3358_);
lean_ctor_set(v___x_3364_, 1, v___x_3135_);
lean_ctor_set(v___x_3364_, 2, v___x_3361_);
lean_ctor_set(v___x_3364_, 3, v___x_3362_);
lean_ctor_set(v___x_3364_, 4, v___x_3363_);
lean_ctor_set(v___x_3364_, 5, v___x_3359_);
lean_ctor_set(v___x_3364_, 6, v___x_3363_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7, v___x_3317_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 1, v___x_3317_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 2, v___x_3317_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 3, v_hasTrace_3143_);
v___x_3365_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3367_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3365_);
lean_ctor_set(v___x_3368_, 1, v___x_3366_);
lean_ctor_set(v___x_3368_, 2, v___x_3135_);
lean_ctor_set(v___x_3368_, 3, v___x_3360_);
lean_ctor_set(v___x_3368_, 4, v___x_3367_);
v___x_3369_ = lean_st_mk_ref(v___x_3368_);
v___x_3370_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3323_, v___x_3364_, v___x_3369_, v___y_3138_, v___y_3139_);
lean_dec_ref_known(v___x_3364_, 7);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = lean_st_ref_get(v___x_3369_);
lean_dec(v___x_3369_);
lean_dec(v___x_3372_);
if (lean_obj_tag(v_a_3371_) == 0)
{
v___y_3278_ = v___x_3318_;
v___y_3279_ = v_a_3315_;
v_a_3280_ = v___x_3317_;
goto v___jp_3277_;
}
else
{
lean_dec_ref_known(v_a_3371_, 1);
v___y_3278_ = v___x_3318_;
v___y_3279_ = v_a_3315_;
v_a_3280_ = v___x_3329_;
goto v___jp_3277_;
}
}
else
{
lean_object* v_a_3373_; 
lean_dec(v___x_3369_);
v_a_3373_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3370_, 1);
v___y_3273_ = v___x_3318_;
v___y_3274_ = v_a_3315_;
v_a_3275_ = v_a_3373_;
goto v___jp_3272_;
}
}
}
}
else
{
lean_dec(v___x_3321_);
lean_dec(v_name_3137_);
lean_dec(v___x_3135_);
v___y_3278_ = v___x_3318_;
v___y_3279_ = v_a_3315_;
v_a_3280_ = v___x_3317_;
goto v___jp_3277_;
}
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v_env_3376_; lean_object* v___x_3377_; 
v___x_3374_ = lean_io_get_num_heartbeats();
v___x_3375_ = lean_st_ref_get(v___y_3139_);
v_env_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc_ref(v_env_3376_);
lean_dec(v___x_3375_);
lean_inc(v_name_3137_);
v___x_3377_ = l_Lean_Meta_declFromEqLikeName(v_env_3376_, v_name_3137_);
if (lean_obj_tag(v___x_3377_) == 1)
{
lean_object* v_val_3378_; lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3381_; lean_object* v_env_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v_val_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_val_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v_fst_3379_ = lean_ctor_get(v_val_3378_, 0);
lean_inc_n(v_fst_3379_, 2);
v_snd_3380_ = lean_ctor_get(v_val_3378_, 1);
lean_inc_n(v_snd_3380_, 2);
lean_dec(v_val_3378_);
v___x_3381_ = lean_st_ref_get(v___y_3139_);
v_env_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc_ref(v_env_3382_);
lean_dec(v___x_3381_);
v___x_3383_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3382_, v_fst_3379_, v_snd_3380_);
v___x_3384_ = lean_name_eq(v_name_3137_, v___x_3383_);
lean_dec(v___x_3383_);
lean_dec(v_name_3137_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec(v_snd_3380_);
lean_dec(v_fst_3379_);
lean_dec(v___x_3135_);
v___x_3385_ = lean_box(0);
lean_inc(v___y_3139_);
lean_inc_ref(v___y_3138_);
v___x_3386_ = lean_apply_4(v___f_3136_, v___x_3385_, v___y_3138_, v___y_3139_, lean_box(0));
v___y_3307_ = v_a_3315_;
v___y_3308_ = v___x_3374_;
v___y_3309_ = v___x_3386_;
goto v___jp_3306_;
}
else
{
uint8_t v___x_3387_; 
lean_inc(v_snd_3380_);
v___x_3387_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3380_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3388_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3389_ = lean_string_dec_eq(v_snd_3380_, v___x_3388_);
lean_dec(v_snd_3380_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec(v_fst_3379_);
lean_dec(v___x_3135_);
v___x_3390_ = lean_box(0);
lean_inc(v___y_3139_);
lean_inc_ref(v___y_3138_);
v___x_3391_ = lean_apply_4(v___f_3136_, v___x_3390_, v___y_3138_, v___y_3139_, lean_box(0));
v___y_3307_ = v_a_3315_;
v___y_3308_ = v___x_3374_;
v___y_3309_ = v___x_3391_;
goto v___jp_3306_;
}
else
{
uint8_t v___x_3392_; uint8_t v___x_3393_; uint8_t v___x_3394_; lean_object* v___x_3395_; uint64_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_dec_ref(v___f_3136_);
v___x_3392_ = 1;
v___x_3393_ = 0;
v___x_3394_ = 2;
v___x_3395_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3395_, 0, v___x_3387_);
lean_ctor_set_uint8(v___x_3395_, 1, v___x_3387_);
lean_ctor_set_uint8(v___x_3395_, 2, v___x_3387_);
lean_ctor_set_uint8(v___x_3395_, 3, v___x_3387_);
lean_ctor_set_uint8(v___x_3395_, 4, v___x_3387_);
lean_ctor_set_uint8(v___x_3395_, 5, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 6, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 7, v___x_3387_);
lean_ctor_set_uint8(v___x_3395_, 8, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 9, v___x_3392_);
lean_ctor_set_uint8(v___x_3395_, 10, v___x_3393_);
lean_ctor_set_uint8(v___x_3395_, 11, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 12, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 13, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 14, v___x_3394_);
lean_ctor_set_uint8(v___x_3395_, 15, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 16, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 17, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 18, v___x_3389_);
lean_ctor_set_uint8(v___x_3395_, 19, v___x_3387_);
lean_ctor_set_uint8(v___x_3395_, 20, v___x_3389_);
v___x_3396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3395_);
v___x_3397_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set_uint64(v___x_3397_, sizeof(void*)*1, v___x_3396_);
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3400_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3401_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3402_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3403_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3403_, 0, v___x_3397_);
lean_ctor_set(v___x_3403_, 1, v___x_3135_);
lean_ctor_set(v___x_3403_, 2, v___x_3400_);
lean_ctor_set(v___x_3403_, 3, v___x_3401_);
lean_ctor_set(v___x_3403_, 4, v___x_3402_);
lean_ctor_set(v___x_3403_, 5, v___x_3398_);
lean_ctor_set(v___x_3403_, 6, v___x_3402_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7, v___x_3387_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7 + 1, v___x_3387_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7 + 2, v___x_3387_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7 + 3, v___x_3317_);
v___x_3404_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3405_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3404_);
lean_ctor_set(v___x_3407_, 1, v___x_3405_);
lean_ctor_set(v___x_3407_, 2, v___x_3135_);
lean_ctor_set(v___x_3407_, 3, v___x_3399_);
lean_ctor_set(v___x_3407_, 4, v___x_3406_);
v___x_3408_ = lean_st_mk_ref(v___x_3407_);
v___x_3409_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3379_, v___x_3317_, v___x_3403_, v___x_3408_, v___y_3138_, v___y_3139_);
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
if (lean_obj_tag(v_a_3410_) == 0)
{
v___y_3301_ = v_a_3315_;
v___y_3302_ = v___x_3374_;
v_a_3303_ = v___x_3387_;
goto v___jp_3300_;
}
else
{
lean_dec_ref_known(v_a_3410_, 1);
v___y_3301_ = v_a_3315_;
v___y_3302_ = v___x_3374_;
v_a_3303_ = v___x_3389_;
goto v___jp_3300_;
}
}
else
{
lean_object* v_a_3412_; 
lean_dec(v___x_3408_);
v_a_3412_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3296_ = v_a_3315_;
v___y_3297_ = v___x_3374_;
v_a_3298_ = v_a_3412_;
goto v___jp_3295_;
}
}
}
else
{
uint8_t v___x_3413_; uint8_t v___x_3414_; uint8_t v___x_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; uint64_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec(v_snd_3380_);
lean_dec_ref(v___f_3136_);
v___x_3413_ = 0;
v___x_3414_ = 1;
v___x_3415_ = 0;
v___x_3416_ = 2;
v___x_3417_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_3417_, 0, v___x_3413_);
lean_ctor_set_uint8(v___x_3417_, 1, v___x_3413_);
lean_ctor_set_uint8(v___x_3417_, 2, v___x_3413_);
lean_ctor_set_uint8(v___x_3417_, 3, v___x_3413_);
lean_ctor_set_uint8(v___x_3417_, 4, v___x_3413_);
lean_ctor_set_uint8(v___x_3417_, 5, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 6, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 7, v___x_3413_);
lean_ctor_set_uint8(v___x_3417_, 8, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 9, v___x_3414_);
lean_ctor_set_uint8(v___x_3417_, 10, v___x_3415_);
lean_ctor_set_uint8(v___x_3417_, 11, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 12, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 13, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 14, v___x_3416_);
lean_ctor_set_uint8(v___x_3417_, 15, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 16, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 17, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 18, v___x_3387_);
lean_ctor_set_uint8(v___x_3417_, 19, v___x_3413_);
lean_ctor_set_uint8(v___x_3417_, 20, v___x_3387_);
v___x_3418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3417_);
v___x_3419_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set_uint64(v___x_3419_, sizeof(void*)*1, v___x_3418_);
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3422_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3424_ = lean_box(0);
lean_inc(v___x_3135_);
v___x_3425_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3425_, 0, v___x_3419_);
lean_ctor_set(v___x_3425_, 1, v___x_3135_);
lean_ctor_set(v___x_3425_, 2, v___x_3422_);
lean_ctor_set(v___x_3425_, 3, v___x_3423_);
lean_ctor_set(v___x_3425_, 4, v___x_3424_);
lean_ctor_set(v___x_3425_, 5, v___x_3420_);
lean_ctor_set(v___x_3425_, 6, v___x_3424_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7, v___x_3413_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 1, v___x_3413_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 2, v___x_3413_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 3, v___x_3317_);
v___x_3426_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3426_);
lean_ctor_set(v___x_3429_, 1, v___x_3427_);
lean_ctor_set(v___x_3429_, 2, v___x_3135_);
lean_ctor_set(v___x_3429_, 3, v___x_3421_);
lean_ctor_set(v___x_3429_, 4, v___x_3428_);
v___x_3430_ = lean_st_mk_ref(v___x_3429_);
v___x_3431_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3379_, v___x_3425_, v___x_3430_, v___y_3138_, v___y_3139_);
lean_dec_ref_known(v___x_3425_, 7);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = lean_st_ref_get(v___x_3430_);
lean_dec(v___x_3430_);
lean_dec(v___x_3433_);
if (lean_obj_tag(v_a_3432_) == 0)
{
v___y_3301_ = v_a_3315_;
v___y_3302_ = v___x_3374_;
v_a_3303_ = v___x_3413_;
goto v___jp_3300_;
}
else
{
lean_dec_ref_known(v_a_3432_, 1);
v___y_3301_ = v_a_3315_;
v___y_3302_ = v___x_3374_;
v_a_3303_ = v___x_3387_;
goto v___jp_3300_;
}
}
else
{
lean_object* v_a_3434_; 
lean_dec(v___x_3430_);
v_a_3434_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3431_, 1);
v___y_3296_ = v_a_3315_;
v___y_3297_ = v___x_3374_;
v_a_3298_ = v_a_3434_;
goto v___jp_3295_;
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_dec(v___x_3377_);
lean_dec(v_name_3137_);
lean_dec(v___x_3135_);
v___x_3435_ = lean_box(0);
lean_inc(v___y_3139_);
lean_inc_ref(v___y_3138_);
v___x_3436_ = lean_apply_4(v___f_3136_, v___x_3435_, v___y_3138_, v___y_3139_, lean_box(0));
v___y_3307_ = v_a_3315_;
v___y_3308_ = v___x_3374_;
v___y_3309_ = v___x_3436_;
goto v___jp_3306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3546_, lean_object* v___f_3547_, lean_object* v_name_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3546_, v___f_3547_, v_name_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = lean_unsigned_to_nat(3137104340u);
v___x_3598_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3599_ = l_Lean_Name_num___override(v___x_3598_, v___x_3597_);
return v___x_3599_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3601_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3602_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3603_ = l_Lean_Name_str___override(v___x_3602_, v___x_3601_);
return v___x_3603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3605_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3606_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3607_ = l_Lean_Name_str___override(v___x_3606_, v___x_3605_);
return v___x_3607_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3608_ = lean_unsigned_to_nat(2u);
v___x_3609_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3610_ = l_Lean_Name_num___override(v___x_3609_, v___x_3608_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3612_; lean_object* v___x_3613_; 
v___f_3612_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3613_ = l_Lean_registerReservedNameAction(v___f_3612_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3614_; uint8_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_dec_ref_known(v___x_3613_, 1);
v___x_3614_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__8));
v___x_3615_ = 0;
v___x_3616_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3617_ = l_Lean_registerTraceClass(v___x_3614_, v___x_3615_, v___x_3616_);
return v___x_3617_;
}
else
{
return v___x_3613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3620_, lean_object* v_x_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3621_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3626_, lean_object* v_x_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3626_, v_x_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
return v_res_3631_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_RecExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LetToHave(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ExprDefEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_ExprDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
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
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_293013915____hygCtx___hyg_2_();
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
lean_object* initialize_Lean_Meta_ExprDefEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
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
res = initialize_Lean_Meta_ExprDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
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
