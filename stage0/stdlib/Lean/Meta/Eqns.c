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
extern lean_object* l_Lean_Meta_smartUnfolding;
extern lean_object* l_Lean_Meta_backward_whnf_reducibleClassField;
extern lean_object* l_Lean_Meta_backward_isDefEq_respectTransparency_types;
extern lean_object* l_Lean_Meta_backward_isDefEq_respectTransparency;
extern lean_object* l_Lean_backward_defeqAttrib_useBackward;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_));
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_));
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_));
v___x_66_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v___x_63_, v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_67_;
v_res_67_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_();
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_();
return v_res_69_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_));
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_));
v___x_90_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_));
v___x_91_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v___x_88_, v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_92_;
v_res_92_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_();
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4____boxed(lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_();
return v_res_94_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__0(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_95_ = l_Lean_Meta_smartUnfolding;
v___x_96_ = l_Lean_Meta_backward_whnf_reducibleClassField;
v___x_97_ = l_Lean_Meta_backward_isDefEq_respectTransparency_types;
v___x_98_ = l_Lean_Meta_backward_isDefEq_respectTransparency;
v___x_99_ = l_Lean_backward_defeqAttrib_useBackward;
v___x_100_ = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
v___x_101_ = l_Lean_Meta_backward_eqns_nonrecursive;
v___x_102_ = lean_unsigned_to_nat(7u);
v___x_103_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_104_ = lean_array_push(v___x_103_, v___x_101_);
v___x_105_ = lean_array_push(v___x_104_, v___x_100_);
v___x_106_ = lean_array_push(v___x_105_, v___x_99_);
v___x_107_ = lean_array_push(v___x_106_, v___x_98_);
v___x_108_ = lean_array_push(v___x_107_, v___x_97_);
v___x_109_ = lean_array_push(v___x_108_, v___x_96_);
v___x_110_ = lean_array_push(v___x_109_, v___x_95_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Meta_eqnAffectingOptions___closed__0, &l_Lean_Meta_eqnAffectingOptions___closed__0_once, _init_l_Lean_Meta_eqnAffectingOptions___closed__0);
return v___x_111_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(lean_object* v_env_112_, lean_object* v_as_113_, size_t v_i_114_, size_t v_stop_115_, lean_object* v_b_116_){
_start:
{
lean_object* v___y_118_; uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_114_, v_stop_115_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v_fst_124_; uint8_t v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_123_ = lean_array_uget_borrowed(v_as_113_, v_i_114_);
v_fst_124_ = lean_ctor_get(v___x_123_, 0);
v___x_125_ = 1;
lean_inc_ref(v_env_112_);
v___x_126_ = l_Lean_Environment_setExporting(v_env_112_, v___x_125_);
lean_inc(v_fst_124_);
v___x_127_ = l_Lean_Environment_contains(v___x_126_, v_fst_124_, v___x_125_);
if (v___x_127_ == 0)
{
v___y_118_ = v_b_116_;
goto v___jp_117_;
}
else
{
lean_object* v___x_128_; 
lean_inc(v___x_123_);
v___x_128_ = lean_array_push(v_b_116_, v___x_123_);
v___y_118_ = v___x_128_;
goto v___jp_117_;
}
}
else
{
lean_dec_ref(v_env_112_);
return v_b_116_;
}
v___jp_117_:
{
size_t v___x_119_; size_t v___x_120_; 
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_add(v_i_114_, v___x_119_);
v_i_114_ = v___x_120_;
v_b_116_ = v___y_118_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_112_ = stack[0].m_obj;
lean_object* v_as_113_ = stack[1].m_obj;
size_t v_i_114_ = stack[2].m_num;
size_t v_stop_115_ = stack[3].m_num;
lean_object* v_b_116_ = stack[4].m_obj;
lean_object* v_res_129_;
v_res_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_112_, v_as_113_, v_i_114_, v_stop_115_, v_b_116_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_130_, lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_stop_133_, lean_object* v_b_134_){
_start:
{
size_t v_i_boxed_135_; size_t v_stop_boxed_136_; lean_object* v_res_137_; 
v_i_boxed_135_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_stop_boxed_136_ = lean_unbox_usize(v_stop_133_);
lean_dec(v_stop_133_);
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_130_, v_as_131_, v_i_boxed_135_, v_stop_boxed_136_, v_b_134_);
lean_dec_ref(v_as_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v_k_140_; lean_object* v_v_141_; lean_object* v_l_142_; lean_object* v_r_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_k_140_ = lean_ctor_get(v_x_139_, 1);
v_v_141_ = lean_ctor_get(v_x_139_, 2);
v_l_142_ = lean_ctor_get(v_x_139_, 3);
v_r_143_ = lean_ctor_get(v_x_139_, 4);
v___x_144_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_138_, v_l_142_);
lean_inc(v_v_141_);
lean_inc(v_k_140_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_k_140_);
lean_ctor_set(v___x_145_, 1, v_v_141_);
v___x_146_ = lean_array_push(v___x_144_, v___x_145_);
v_init_138_ = v___x_146_;
v_x_139_ = v_r_143_;
goto _start;
}
else
{
return v_init_138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_148_, v_x_149_);
lean_dec(v_x_149_);
return v_res_150_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(lean_object* v_env_151_, lean_object* v_as_152_, size_t v_i_153_, size_t v_stop_154_, lean_object* v_b_155_){
_start:
{
lean_object* v___y_157_; uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_eq(v_i_153_, v_stop_154_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v_fst_163_; uint8_t v___x_164_; 
v___x_162_ = lean_array_uget_borrowed(v_as_152_, v_i_153_);
v_fst_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_fst_163_);
lean_inc_ref(v_env_151_);
v___x_164_ = l_Lean_Environment_contains(v_env_151_, v_fst_163_, v___x_161_);
if (v___x_164_ == 0)
{
v___y_157_ = v_b_155_;
goto v___jp_156_;
}
else
{
lean_object* v___x_165_; 
lean_inc(v___x_162_);
v___x_165_ = lean_array_push(v_b_155_, v___x_162_);
v___y_157_ = v___x_165_;
goto v___jp_156_;
}
}
else
{
lean_dec_ref(v_env_151_);
return v_b_155_;
}
v___jp_156_:
{
size_t v___x_158_; size_t v___x_159_; 
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_153_, v___x_158_);
v_i_153_ = v___x_159_;
v_b_155_ = v___y_157_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_151_ = stack[0].m_obj;
lean_object* v_as_152_ = stack[1].m_obj;
size_t v_i_153_ = stack[2].m_num;
size_t v_stop_154_ = stack[3].m_num;
lean_object* v_b_155_ = stack[4].m_obj;
lean_object* v_res_166_;
v_res_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_151_, v_as_152_, v_i_153_, v_stop_154_, v_b_155_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_167_, lean_object* v_as_168_, lean_object* v_i_169_, lean_object* v_stop_170_, lean_object* v_b_171_){
_start:
{
size_t v_i_boxed_172_; size_t v_stop_boxed_173_; lean_object* v_res_174_; 
v_i_boxed_172_ = lean_unbox_usize(v_i_169_);
lean_dec(v_i_169_);
v_stop_boxed_173_ = lean_unbox_usize(v_stop_170_);
lean_dec(v_stop_170_);
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_167_, v_as_168_, v_i_boxed_172_, v_stop_boxed_173_, v_b_171_);
lean_dec_ref(v_as_168_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(lean_object* v_env_179_, lean_object* v_s_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___y_183_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_199_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v___x_198_, v_s_180_);
v___x_200_ = lean_array_get_size(v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_202_ = lean_nat_dec_lt(v___x_181_, v___x_200_);
if (v___x_202_ == 0)
{
lean_dec_ref(v___x_199_);
v___y_183_ = v___x_201_;
goto v___jp_182_;
}
else
{
uint8_t v___x_203_; 
v___x_203_ = lean_nat_dec_le(v___x_200_, v___x_200_);
if (v___x_203_ == 0)
{
if (v___x_202_ == 0)
{
lean_dec_ref(v___x_199_);
v___y_183_ = v___x_201_;
goto v___jp_182_;
}
else
{
size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((size_t)0ULL);
v___x_205_ = lean_usize_of_nat(v___x_200_);
lean_inc_ref(v_env_179_);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_179_, v___x_199_, v___x_204_, v___x_205_, v___x_201_);
lean_dec_ref(v___x_199_);
v___y_183_ = v___x_206_;
goto v___jp_182_;
}
}
else
{
size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((size_t)0ULL);
v___x_208_ = lean_usize_of_nat(v___x_200_);
lean_inc_ref(v_env_179_);
v___x_209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_179_, v___x_199_, v___x_207_, v___x_208_, v___x_201_);
lean_dec_ref(v___x_199_);
v___y_183_ = v___x_209_;
goto v___jp_182_;
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_184_ = lean_array_get_size(v___y_183_);
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_186_ = lean_nat_dec_lt(v___x_181_, v___x_184_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec_ref(v_env_179_);
v___x_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
lean_ctor_set(v___x_187_, 2, v___y_183_);
return v___x_187_;
}
else
{
uint8_t v___x_188_; 
v___x_188_ = lean_nat_dec_le(v___x_184_, v___x_184_);
if (v___x_188_ == 0)
{
if (v___x_186_ == 0)
{
lean_object* v___x_189_; 
lean_dec_ref(v_env_179_);
v___x_189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_189_, 0, v___x_185_);
lean_ctor_set(v___x_189_, 1, v___x_185_);
lean_ctor_set(v___x_189_, 2, v___y_183_);
return v___x_189_;
}
else
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_190_ = ((size_t)0ULL);
v___x_191_ = lean_usize_of_nat(v___x_184_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_179_, v___y_183_, v___x_190_, v___x_191_, v___x_185_);
lean_inc_ref(v___x_192_);
v___x_193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_ctor_set(v___x_193_, 2, v___y_183_);
return v___x_193_;
}
}
else
{
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = ((size_t)0ULL);
v___x_195_ = lean_usize_of_nat(v___x_184_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_179_, v___y_183_, v___x_194_, v___x_195_, v___x_185_);
lean_inc_ref(v___x_196_);
v___x_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
lean_ctor_set(v___x_197_, 2, v___y_183_);
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_env_210_, lean_object* v_s_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(v_env_210_, v_s_211_);
lean_dec(v_s_211_);
return v_res_212_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; 
v___f_220_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_222_ = lean_box(1);
v___x_223_ = 0;
v___x_224_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_221_, v___x_222_, v___x_223_, v___f_220_);
return v___x_224_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_225_;
v_res_225_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object* v_init_228_, lean_object* v_t_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_228_, v_t_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_231_, lean_object* v_t_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_231_, v_t_232_);
lean_dec(v_t_232_);
return v_res_233_;
}
}
uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_241_ = lean_string_utf8_byte_size(v_s_240_);
v___x_242_ = lean_unsigned_to_nat(3u);
v___x_243_ = lean_nat_dec_le(v___x_242_, v___x_241_);
if (v___x_243_ == 0)
{
lean_dec_ref(v_s_240_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_string_memcmp(v_s_240_, v___x_244_, v___x_245_, v___x_245_, v___x_242_);
if (v___x_246_ == 0)
{
lean_dec_ref(v_s_240_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
lean_inc_ref(v_s_240_);
v___x_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_247_, 0, v_s_240_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_241_);
v___x_248_ = l_String_Slice_Pos_nextn(v___x_247_, v___x_245_, v___x_242_);
lean_dec_ref_known(v___x_247_, 3);
v___x_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_249_, 0, v_s_240_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
lean_ctor_set(v___x_249_, 2, v___x_241_);
v___x_250_ = l_String_Slice_isNat(v___x_249_);
lean_dec_ref_known(v___x_249_, 3);
return v___x_250_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isEqnReservedNameSuffix_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_240_ = stack[0].m_obj;
uint8_t v_res_251_;
v_res_251_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_240_);
stack->m_num = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_259_){
_start:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_261_ = lean_string_dec_eq(v_s_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_263_ = lean_string_dec_eq(v_s_259_, v___x_262_);
if (v___x_263_ == 0)
{
uint8_t v___x_264_; 
v___x_264_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_259_);
return v___x_264_;
}
else
{
lean_dec_ref(v_s_259_);
return v___x_263_;
}
}
else
{
lean_dec_ref(v_s_259_);
return v___x_261_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_isEqnLikeSuffix_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_259_ = stack[0].m_obj;
uint8_t v_res_265_;
v_res_265_ = l_Lean_Meta_isEqnLikeSuffix(v_s_259_);
stack->m_num = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Lean_Meta_isEqnLikeSuffix(v_s_266_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_272_, lean_object* v_env_273_, uint8_t v___x_274_, lean_object* v_as_x27_275_, lean_object* v_b_276_){
_start:
{
if (lean_obj_tag(v_as_x27_275_) == 0)
{
lean_dec_ref(v_env_273_);
lean_dec_ref(v_str_272_);
lean_inc_ref(v_b_276_);
return v_b_276_;
}
else
{
lean_object* v_head_277_; lean_object* v_tail_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___y_282_; uint8_t v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_head_277_ = lean_ctor_get(v_as_x27_275_, 0);
v_tail_278_ = lean_ctor_get(v_as_x27_275_, 1);
v___x_279_ = lean_box(0);
v___x_280_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_288_ = 0;
lean_inc_ref(v_env_273_);
v___x_289_ = l_Lean_Environment_setExporting(v_env_273_, v___x_288_);
lean_inc(v_head_277_);
v___x_290_ = l_Lean_Environment_isSafeDefinition(v___x_289_, v_head_277_);
if (v___x_290_ == 0)
{
v___y_282_ = v___x_290_;
goto v___jp_281_;
}
else
{
uint8_t v___x_291_; 
lean_inc(v_head_277_);
lean_inc_ref(v_env_273_);
v___x_291_ = l_Lean_Meta_isMatcherCore(v_env_273_, v_head_277_);
if (v___x_291_ == 0)
{
v___y_282_ = v___x_274_;
goto v___jp_281_;
}
else
{
v_as_x27_275_ = v_tail_278_;
v_b_276_ = v___x_280_;
goto _start;
}
}
v___jp_281_:
{
if (v___y_282_ == 0)
{
v_as_x27_275_ = v_tail_278_;
v_b_276_ = v___x_280_;
goto _start;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v_env_273_);
lean_inc(v_head_277_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_head_277_);
lean_ctor_set(v___x_284_, 1, v_str_272_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_279_);
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_str_272_ = stack[0].m_obj;
lean_object* v_env_273_ = stack[1].m_obj;
uint8_t v___x_274_ = stack[2].m_num;
lean_object* v_as_x27_275_ = stack[3].m_obj;
lean_object* v_b_276_ = stack[4].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_272_, v_env_273_, v___x_274_, v_as_x27_275_, v_b_276_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_294_, lean_object* v_env_295_, lean_object* v___x_296_, lean_object* v_as_x27_297_, lean_object* v_b_298_){
_start:
{
uint8_t v___x_616__boxed_299_; lean_object* v_res_300_; 
v___x_616__boxed_299_ = lean_unbox(v___x_296_);
v_res_300_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_294_, v_env_295_, v___x_616__boxed_299_, v_as_x27_297_, v_b_298_);
lean_dec_ref(v_b_298_);
lean_dec(v_as_x27_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_301_, lean_object* v_name_302_){
_start:
{
if (lean_obj_tag(v_name_302_) == 1)
{
lean_object* v_pre_303_; lean_object* v_str_304_; uint8_t v___x_305_; 
v_pre_303_ = lean_ctor_get(v_name_302_, 0);
lean_inc(v_pre_303_);
v_str_304_ = lean_ctor_get(v_name_302_, 1);
lean_inc_ref_n(v_str_304_, 2);
lean_dec_ref_known(v_name_302_, 2);
v___x_305_ = l_Lean_Meta_isEqnLikeSuffix(v_str_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec_ref(v_str_304_);
lean_dec(v_pre_303_);
lean_dec_ref(v_env_301_);
v___x_306_ = lean_box(0);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_fst_314_; 
lean_inc(v_pre_303_);
v___x_307_ = l_Lean_privateToUserName(v_pre_303_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v_pre_303_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_box(0);
v___x_312_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_313_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_304_, v_env_301_, v___x_305_, v___x_310_, v___x_312_);
lean_dec_ref_known(v___x_310_, 2);
v_fst_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_fst_314_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v_fst_314_) == 0)
{
return v___x_311_;
}
else
{
lean_object* v_val_315_; 
v_val_315_ = lean_ctor_get(v_fst_314_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v_fst_314_, 1);
return v_val_315_;
}
}
}
else
{
lean_object* v___x_316_; 
lean_dec(v_name_302_);
lean_dec_ref(v_env_301_);
v___x_316_ = lean_box(0);
return v___x_316_;
}
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_317_, lean_object* v_env_318_, uint8_t v___x_319_, lean_object* v_as_320_, lean_object* v_as_x27_321_, lean_object* v_b_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_317_, v_env_318_, v___x_319_, v_as_x27_321_, v_b_322_);
return v___x_324_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_str_317_ = stack[0].m_obj;
lean_object* v_env_318_ = stack[1].m_obj;
uint8_t v___x_319_ = stack[2].m_num;
lean_object* v_as_320_ = stack[3].m_obj;
lean_object* v_as_x27_321_ = stack[4].m_obj;
lean_object* v_b_322_ = stack[5].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_317_, v_env_318_, v___x_319_, v_as_320_, v_as_x27_321_, v_b_322_, lean_box(0));
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_326_, lean_object* v_env_327_, lean_object* v___x_328_, lean_object* v_as_329_, lean_object* v_as_x27_330_, lean_object* v_b_331_, lean_object* v_a_332_){
_start:
{
uint8_t v___x_723__boxed_333_; lean_object* v_res_334_; 
v___x_723__boxed_333_ = lean_unbox(v___x_328_);
v_res_334_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_326_, v_env_327_, v___x_723__boxed_333_, v_as_329_, v_as_x27_330_, v_b_331_, v_a_332_);
lean_dec_ref(v_b_331_);
lean_dec(v_as_x27_330_);
lean_dec(v_as_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_335_, lean_object* v_declName_336_, lean_object* v_suffix_337_){
_start:
{
uint8_t v_isExposed_338_; lean_object* v_name_339_; 
lean_inc(v_declName_336_);
lean_inc_ref(v_env_335_);
v_isExposed_338_ = l_Lean_Environment_hasExposedBody(v_env_335_, v_declName_336_);
v_name_339_ = l_Lean_Name_str___override(v_declName_336_, v_suffix_337_);
if (v_isExposed_338_ == 0)
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_mkPrivateName(v_env_335_, v_name_339_);
lean_dec_ref(v_env_335_);
return v___x_340_;
}
else
{
lean_dec_ref(v_env_335_);
return v_name_339_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_341_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_344_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
lean_ctor_set(v___x_347_, 2, v___x_346_);
lean_ctor_set(v___x_347_, 3, v___x_346_);
lean_ctor_set(v___x_347_, 4, v___x_345_);
lean_ctor_set(v___x_347_, 5, v___x_345_);
lean_ctor_set(v___x_347_, 6, v___x_345_);
lean_ctor_set(v___x_347_, 7, v___x_345_);
lean_ctor_set(v___x_347_, 8, v___x_345_);
lean_ctor_set(v___x_347_, 9, v___x_345_);
lean_ctor_set(v___x_347_, 10, v___x_345_);
lean_ctor_set(v___x_347_, 11, v___x_344_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_unsigned_to_nat(32u);
v___x_349_ = lean_mk_empty_array_with_capacity(v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = ((size_t)5ULL);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_unsigned_to_nat(32u);
v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
v___x_355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_356_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_352_);
lean_ctor_set(v___x_356_, 3, v___x_352_);
lean_ctor_set_usize(v___x_356_, 4, v___x_351_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_box(1);
v___x_358_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_359_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
lean_ctor_set(v___x_360_, 2, v___x_357_);
return v___x_360_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; lean_object* v_toCold_366_; lean_object* v_env_367_; lean_object* v_options_368_; uint8_t v___x_369_; lean_object* v_env_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_365_ = lean_st_ref_get(v___y_363_);
v_toCold_366_ = lean_ctor_get(v___y_362_, 0);
v_env_367_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_367_);
lean_dec(v___x_365_);
v_options_368_ = lean_ctor_get(v_toCold_366_, 2);
v___x_369_ = 0;
v_env_370_ = l_Lean_Environment_setRecordingDeps(v_env_367_, v___x_369_);
v___x_371_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_372_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_368_);
v___x_373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_373_, 0, v_env_370_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_372_);
lean_ctor_set(v___x_373_, 3, v_options_368_);
v___x_374_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_msgData_361_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_361_ = stack[0].m_obj;
lean_object* v___y_362_ = stack[1].m_obj;
lean_object* v___y_363_ = stack[2].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_361_, v___y_362_, v___y_363_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_381_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_ref_386_; lean_object* v___x_387_; lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_ref_386_ = lean_ctor_get(v___y_383_, 2);
v___x_387_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_382_, v___y_383_, v___y_384_);
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
lean_inc(v_ref_386_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_ref_386_);
lean_ctor_set(v___x_392_, 1, v_a_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set_tag(v___x_390_, 1);
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_382_ = stack[0].m_obj;
lean_object* v___y_383_ = stack[1].m_obj;
lean_object* v___y_384_ = stack[2].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_382_, v___y_383_, v___y_384_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_402_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_412_, lean_object* v_reservedName_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_417_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_418_ = 0;
v___x_419_ = l_Lean_MessageData_ofConstName(v_declName_412_, v___x_418_);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_417_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = 1;
v___x_424_ = l_Lean_MessageData_ofConstName(v_reservedName_413_, v___x_423_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_422_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_427_, v___y_414_, v___y_415_);
return v___x_428_;
}
}
LEAN_EXPORT void l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_412_ = stack[0].m_obj;
lean_object* v_reservedName_413_ = stack[1].m_obj;
lean_object* v___y_414_ = stack[2].m_obj;
lean_object* v___y_415_ = stack[3].m_obj;
lean_object* v_res_429_;
v_res_429_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_412_, v_reservedName_413_, v___y_414_, v___y_415_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_430_, lean_object* v_reservedName_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_430_, v_reservedName_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_435_;
}
}
lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_436_, lean_object* v_suffix_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_reservedName_441_; lean_object* v___x_442_; lean_object* v_env_443_; uint8_t v___x_444_; uint8_t v___x_445_; 
lean_inc(v_declName_436_);
v_reservedName_441_ = l_Lean_Name_str___override(v_declName_436_, v_suffix_437_);
v___x_442_ = lean_st_ref_get(v___y_439_);
v_env_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc_ref(v_env_443_);
lean_dec(v___x_442_);
v___x_444_ = 1;
lean_inc(v_reservedName_441_);
v___x_445_ = l_Lean_Environment_contains(v_env_443_, v_reservedName_441_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_reservedName_441_);
lean_dec(v_declName_436_);
v___x_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_436_, v_reservedName_441_, v___y_438_, v___y_439_);
return v___x_448_;
}
}
}
LEAN_EXPORT void l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_436_ = stack[0].m_obj;
lean_object* v_suffix_437_ = stack[1].m_obj;
lean_object* v___y_438_ = stack[2].m_obj;
lean_object* v___y_439_ = stack[3].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_436_, v_suffix_437_, v___y_438_, v___y_439_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_450_, lean_object* v_suffix_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_450_, v_suffix_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_455_;
}
}
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_456_);
v___x_461_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_456_, v___x_460_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref_known(v___x_461_, 1);
v___x_462_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_456_);
v___x_463_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_456_, v___x_462_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref_known(v___x_463_, 1);
v___x_464_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_465_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_456_, v___x_464_, v_a_457_, v_a_458_);
return v___x_465_;
}
else
{
lean_dec(v_declName_456_);
return v___x_463_;
}
}
else
{
lean_dec(v_declName_456_);
return v___x_461_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ensureEqnReservedNamesAvailable_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_456_ = stack[0].m_obj;
lean_object* v_a_457_ = stack[1].m_obj;
lean_object* v_a_458_ = stack[2].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_456_, v_a_457_, v_a_458_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_467_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_471_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_472_, lean_object* v_msg_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_473_, v___y_474_, v___y_475_);
return v___x_477_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_473_ = stack[1].m_obj;
lean_object* v___y_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_box(0), v_msg_473_, v___y_474_, v___y_475_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_479_, v_msg_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_484_;
}
}
uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_485_, lean_object* v_n_486_){
_start:
{
lean_object* v___x_487_; 
lean_inc(v_n_486_);
lean_inc_ref(v_env_485_);
v___x_487_ = l_Lean_Meta_declFromEqLikeName(v_env_485_, v_n_486_);
if (lean_obj_tag(v___x_487_) == 1)
{
lean_object* v_val_488_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_val_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v___x_487_, 1);
v_fst_489_ = lean_ctor_get(v_val_488_, 0);
lean_inc(v_fst_489_);
v_snd_490_ = lean_ctor_get(v_val_488_, 1);
lean_inc(v_snd_490_);
lean_dec(v_val_488_);
v___x_491_ = l_Lean_Meta_mkEqLikeNameFor(v_env_485_, v_fst_489_, v_snd_490_);
v___x_492_ = lean_name_eq(v_n_486_, v___x_491_);
lean_dec(v___x_491_);
lean_dec(v_n_486_);
return v___x_492_;
}
else
{
uint8_t v___x_493_; 
lean_dec(v___x_487_);
lean_dec(v_n_486_);
lean_dec_ref(v_env_485_);
v___x_493_ = 0;
return v___x_493_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_485_ = stack[0].m_obj;
lean_object* v_n_486_ = stack[1].m_obj;
uint8_t v_res_494_;
v_res_494_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_485_, v_n_486_);
stack->m_num = v_res_494_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_495_, lean_object* v_n_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_495_, v_n_496_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_501_; lean_object* v___x_502_; 
v___f_501_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_502_ = l_Lean_registerReservedNamePredicate(v___f_501_);
return v___x_502_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_503_;
v_res_503_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
stack->m_obj
 = v_res_503_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_505_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_st_mk_ref(v___x_507_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_510_;
v_res_510_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_512_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_515_ = lean_mk_io_user_error(v___x_514_);
return v___x_515_;
}
}
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_516_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_initializing();
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref(v_f_516_);
v___x_519_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_521_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_522_ = lean_st_ref_take(v___x_521_);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v_f_516_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_st_ref_put(v___x_521_, v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_registerGetEqnsFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_516_ = stack[0].m_obj;
lean_object* v_res_526_;
v_res_526_ = l_Lean_Meta_registerGetEqnsFn(v_f_516_);
stack->m_obj
 = v_res_526_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Meta_registerGetEqnsFn(v_f_527_);
return v_res_529_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_540_; lean_object* v_env_541_; uint8_t v___x_542_; lean_object* v___x_543_; 
v___x_540_ = lean_st_ref_get(v_a_534_);
v_env_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc_ref(v_env_541_);
lean_dec(v___x_540_);
v___x_542_ = 0;
lean_inc(v_declName_530_);
v___x_543_ = l_Lean_Environment_findAsync_x3f(v_env_541_, v_declName_530_, v___x_542_);
if (lean_obj_tag(v___x_543_) == 1)
{
lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_575_; 
v_val_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_575_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_575_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_575_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v_kind_548_; 
v_kind_548_ = lean_ctor_get_uint8(v_val_544_, sizeof(void*)*3);
if (v_kind_548_ == 0)
{
lean_object* v_sig_549_; lean_object* v___x_550_; lean_object* v_env_551_; uint8_t v___x_552_; 
v_sig_549_ = lean_ctor_get(v_val_544_, 1);
lean_inc_ref(v_sig_549_);
lean_dec(v_val_544_);
v___x_550_ = lean_st_ref_get(v_a_534_);
v_env_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc_ref(v_env_551_);
lean_dec(v___x_550_);
v___x_552_ = l_Lean_Meta_isMatcherCore(v_env_551_, v_declName_530_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v_type_554_; lean_object* v___x_555_; 
lean_del_object(v___x_546_);
v___x_553_ = lean_task_get_own(v_sig_549_);
v_type_554_ = lean_ctor_get(v___x_553_, 2);
lean_inc_ref(v_type_554_);
lean_dec(v___x_553_);
v___x_555_ = l_Lean_Meta_isProp(v_type_554_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_570_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_570_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_570_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_570_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint8_t v___x_560_; 
v___x_560_ = lean_unbox(v_a_556_);
lean_dec(v_a_556_);
if (v___x_560_ == 0)
{
uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = 1;
v___x_562_ = lean_box(v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_box(v___x_552_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_566_);
v___x_568_ = v___x_558_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
return v___x_555_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec_ref(v_sig_549_);
v___x_571_ = lean_box(v___x_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 0);
lean_ctor_set(v___x_546_, 0, v___x_571_);
v___x_573_ = v___x_546_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_del_object(v___x_546_);
lean_dec(v_val_544_);
lean_dec(v_declName_530_);
goto v___jp_536_;
}
}
}
else
{
lean_dec(v___x_543_);
lean_dec(v_declName_530_);
goto v___jp_536_;
}
v___jp_536_:
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = 0;
v___x_538_ = lean_box(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_530_ = stack[0].m_obj;
lean_object* v_a_531_ = stack[1].m_obj;
lean_object* v_a_532_ = stack[2].m_obj;
lean_object* v_a_533_ = stack[3].m_obj;
lean_object* v_a_534_ = stack[4].m_obj;
lean_object* v_res_576_;
v_res_576_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_587_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object* v___x_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
return v___x_590_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_588_ = stack[0].m_obj;
lean_object* v_res_591_;
v_res_591_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_588_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v___x_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_592_);
return v_res_594_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_595_; lean_object* v___f_596_; 
v___x_595_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_596_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_596_, 0, v___x_595_);
return v___f_596_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; 
v___f_603_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_box(1);
v___x_606_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_));
v___x_607_ = 0;
v___x_608_ = 1;
v___x_609_ = l_Lean_registerEnvExtension___redArg(v___f_603_, v___x_604_, v___x_605_, v___x_606_, v___x_607_, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_610_;
v_res_610_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_613_, lean_object* v_opt_614_){
_start:
{
lean_object* v_name_615_; lean_object* v_defValue_616_; lean_object* v_map_617_; lean_object* v___x_618_; 
v_name_615_ = lean_ctor_get(v_opt_614_, 0);
v_defValue_616_ = lean_ctor_get(v_opt_614_, 1);
v_map_617_ = lean_ctor_get(v_opts_613_, 0);
v___x_618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_617_, v_name_615_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_inc(v_defValue_616_);
return v_defValue_616_;
}
else
{
lean_object* v_val_619_; 
v_val_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v___x_618_, 1);
if (lean_obj_tag(v_val_619_) == 3)
{
lean_object* v_v_620_; 
v_v_620_ = lean_ctor_get(v_val_619_, 0);
lean_inc(v_v_620_);
lean_dec_ref_known(v_val_619_, 1);
return v_v_620_;
}
else
{
lean_dec(v_val_619_);
lean_inc(v_defValue_616_);
return v_defValue_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_621_, lean_object* v_opt_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_621_, v_opt_622_);
lean_dec_ref(v_opt_622_);
lean_dec_ref(v_opts_621_);
return v_res_623_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_627_, size_t v_sz_628_, size_t v_i_629_, lean_object* v_b_630_){
_start:
{
lean_object* v_a_632_; uint8_t v___x_636_; 
v___x_636_ = lean_usize_dec_lt(v_i_629_, v_sz_628_);
if (v___x_636_ == 0)
{
return v_b_630_;
}
else
{
lean_object* v_a_637_; lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v_map_640_; uint8_t v_hasTrace_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_654_; 
v_a_637_ = lean_array_uget_borrowed(v_as_627_, v_i_629_);
v_fst_638_ = lean_ctor_get(v_a_637_, 0);
v_snd_639_ = lean_ctor_get(v_a_637_, 1);
v_map_640_ = lean_ctor_get(v_b_630_, 0);
v_hasTrace_641_ = lean_ctor_get_uint8(v_b_630_, sizeof(void*)*1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_b_630_);
if (v_isSharedCheck_654_ == 0)
{
v___x_643_ = v_b_630_;
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_map_640_);
lean_dec(v_b_630_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; 
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_638_, v_snd_639_, v_map_640_);
if (v_hasTrace_641_ == 0)
{
lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_649_; 
v___x_646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_647_ = l_Lean_Name_isPrefixOf(v___x_646_, v_fst_638_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_649_ = v___x_643_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_645_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_647_);
v_a_632_ = v___x_649_;
goto v___jp_631_;
}
}
else
{
lean_object* v___x_652_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_652_ = v___x_643_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_645_);
lean_ctor_set_uint8(v_reuseFailAlloc_653_, sizeof(void*)*1, v_hasTrace_641_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v_a_632_ = v___x_652_;
goto v___jp_631_;
}
}
}
}
v___jp_631_:
{
size_t v___x_633_; size_t v___x_634_; 
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_i_629_, v___x_633_);
v_i_629_ = v___x_634_;
v_b_630_ = v_a_632_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_627_ = stack[0].m_obj;
size_t v_sz_628_ = stack[1].m_num;
size_t v_i_629_ = stack[2].m_num;
lean_object* v_b_630_ = stack[3].m_obj;
lean_object* v_res_655_;
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_627_, v_sz_628_, v_i_629_, v_b_630_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_656_, lean_object* v_sz_657_, lean_object* v_i_658_, lean_object* v_b_659_){
_start:
{
size_t v_sz_boxed_660_; size_t v_i_boxed_661_; lean_object* v_res_662_; 
v_sz_boxed_660_ = lean_unbox_usize(v_sz_657_);
lean_dec(v_sz_657_);
v_i_boxed_661_ = lean_unbox_usize(v_i_658_);
lean_dec(v_i_658_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_656_, v_sz_boxed_660_, v_i_boxed_661_, v_b_659_);
lean_dec_ref(v_as_656_);
return v_res_662_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_663_, lean_object* v_k_664_, uint8_t v_v_665_){
_start:
{
lean_object* v_map_666_; uint8_t v_hasTrace_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_681_; 
v_map_666_ = lean_ctor_get(v_o_663_, 0);
v_hasTrace_667_ = lean_ctor_get_uint8(v_o_663_, sizeof(void*)*1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_o_663_);
if (v_isSharedCheck_681_ == 0)
{
v___x_669_ = v_o_663_;
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_map_666_);
lean_dec(v_o_663_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_671_, 0, v_v_665_);
lean_inc(v_k_664_);
v___x_672_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_664_, v___x_671_, v_map_666_);
if (v_hasTrace_667_ == 0)
{
lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_676_; 
v___x_673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_674_ = l_Lean_Name_isPrefixOf(v___x_673_, v_k_664_);
lean_dec(v_k_664_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_672_);
v___x_676_ = v___x_669_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_672_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*1, v___x_674_);
return v___x_676_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec(v_k_664_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_672_);
v___x_679_ = v___x_669_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*1, v_hasTrace_667_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_663_ = stack[0].m_obj;
lean_object* v_k_664_ = stack[1].m_obj;
uint8_t v_v_665_ = stack[2].m_num;
lean_object* v_res_682_;
v_res_682_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_663_, v_k_664_, v_v_665_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_683_, lean_object* v_k_684_, lean_object* v_v_685_){
_start:
{
uint8_t v_v_boxed_686_; lean_object* v_res_687_; 
v_v_boxed_686_ = lean_unbox(v_v_685_);
v_res_687_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_683_, v_k_684_, v_v_boxed_686_);
return v_res_687_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_688_, lean_object* v_opt_689_, uint8_t v_val_690_){
_start:
{
lean_object* v_name_691_; lean_object* v___x_692_; 
v_name_691_ = lean_ctor_get(v_opt_689_, 0);
lean_inc(v_name_691_);
lean_dec_ref(v_opt_689_);
v___x_692_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_688_, v_name_691_, v_val_690_);
return v___x_692_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_688_ = stack[0].m_obj;
lean_object* v_opt_689_ = stack[1].m_obj;
uint8_t v_val_690_ = stack[2].m_num;
lean_object* v_res_693_;
v_res_693_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_688_, v_opt_689_, v_val_690_);
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_694_, lean_object* v_opt_695_, lean_object* v_val_696_){
_start:
{
uint8_t v_val_boxed_697_; lean_object* v_res_698_; 
v_val_boxed_697_ = lean_unbox(v_val_696_);
v_res_698_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_694_, v_opt_695_, v_val_boxed_697_);
return v_res_698_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_699_, size_t v_i_700_, size_t v_stop_701_, lean_object* v_b_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_eq(v_i_700_, v_stop_701_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v_defValue_705_; uint8_t v___x_706_; lean_object* v___x_707_; size_t v___x_708_; size_t v___x_709_; 
v___x_704_ = lean_array_uget_borrowed(v_as_699_, v_i_700_);
v_defValue_705_ = lean_ctor_get(v___x_704_, 1);
v___x_706_ = lean_unbox(v_defValue_705_);
lean_inc(v___x_704_);
v___x_707_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_702_, v___x_704_, v___x_706_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_700_, v___x_708_);
v_i_700_ = v___x_709_;
v_b_702_ = v___x_707_;
goto _start;
}
else
{
return v_b_702_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_699_ = stack[0].m_obj;
size_t v_i_700_ = stack[1].m_num;
size_t v_stop_701_ = stack[2].m_num;
lean_object* v_b_702_ = stack[3].m_obj;
lean_object* v_res_711_;
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_699_, v_i_700_, v_stop_701_, v_b_702_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_712_, lean_object* v_i_713_, lean_object* v_stop_714_, lean_object* v_b_715_){
_start:
{
size_t v_i_boxed_716_; size_t v_stop_boxed_717_; lean_object* v_res_718_; 
v_i_boxed_716_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_stop_boxed_717_ = lean_unbox_usize(v_stop_714_);
lean_dec(v_stop_714_);
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_712_, v_i_boxed_716_, v_stop_boxed_717_, v_b_715_);
lean_dec_ref(v_as_712_);
return v_res_718_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Array_instInhabited___redArg();
return v___x_723_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = l_Lean_Meta_eqnAffectingOptions;
v___x_725_ = lean_array_get_size(v___x_724_);
return v___x_725_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_nat_dec_lt(v___x_727_, v___x_726_);
return v___x_728_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_730_ = lean_nat_dec_le(v___x_729_, v___x_729_);
return v___x_730_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_731_; size_t v___x_732_; 
v___x_731_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_732_ = lean_usize_of_nat(v___x_731_);
return v___x_732_;
}
}
lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_733_, lean_object* v_act_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
uint16_t v___y_741_; lean_object* v___y_742_; lean_object* v_fileName_743_; lean_object* v_fileMap_744_; lean_object* v_currNamespace_745_; lean_object* v_openDecls_746_; lean_object* v_initHeartbeats_747_; lean_object* v_maxHeartbeats_748_; lean_object* v_quotContext_749_; lean_object* v_currMacroScope_750_; lean_object* v_cancelTk_x3f_751_; lean_object* v_inheritedTraceOptions_752_; lean_object* v_currRecDepth_753_; lean_object* v_ref_754_; uint8_t v_suppressElabErrors_755_; uint8_t v_isRecordingDeps_756_; lean_object* v___y_757_; uint8_t v___y_764_; uint16_t v___y_765_; lean_object* v___y_766_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v_toCold_805_; lean_object* v_currRecDepth_806_; lean_object* v_ref_807_; uint8_t v_suppressElabErrors_808_; uint8_t v_isRecordingDeps_809_; lean_object* v_fileName_810_; lean_object* v_fileMap_811_; lean_object* v_options_812_; lean_object* v_currNamespace_813_; lean_object* v_openDecls_814_; lean_object* v_initHeartbeats_815_; lean_object* v_maxHeartbeats_816_; lean_object* v_quotContext_817_; lean_object* v_currMacroScope_818_; lean_object* v_cancelTk_x3f_819_; lean_object* v_inheritedTraceOptions_820_; lean_object* v___y_822_; 
v___x_803_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_804_ = lean_st_ref_get(v_a_738_);
v_toCold_805_ = lean_ctor_get(v_a_737_, 0);
v_currRecDepth_806_ = lean_ctor_get(v_a_737_, 1);
v_ref_807_ = lean_ctor_get(v_a_737_, 2);
v_suppressElabErrors_808_ = lean_ctor_get_uint8(v_a_737_, sizeof(void*)*3 + 2);
v_isRecordingDeps_809_ = lean_ctor_get_uint8(v_a_737_, sizeof(void*)*3 + 3);
v_fileName_810_ = lean_ctor_get(v_toCold_805_, 0);
v_fileMap_811_ = lean_ctor_get(v_toCold_805_, 1);
v_options_812_ = lean_ctor_get(v_toCold_805_, 2);
v_currNamespace_813_ = lean_ctor_get(v_toCold_805_, 4);
v_openDecls_814_ = lean_ctor_get(v_toCold_805_, 5);
v_initHeartbeats_815_ = lean_ctor_get(v_toCold_805_, 6);
v_maxHeartbeats_816_ = lean_ctor_get(v_toCold_805_, 7);
v_quotContext_817_ = lean_ctor_get(v_toCold_805_, 8);
v_currMacroScope_818_ = lean_ctor_get(v_toCold_805_, 9);
v_cancelTk_x3f_819_ = lean_ctor_get(v_toCold_805_, 10);
v_inheritedTraceOptions_820_ = lean_ctor_get(v_toCold_805_, 11);
if (v_isRecordingDeps_809_ == 0)
{
lean_object* v_env_833_; lean_object* v___x_834_; lean_object* v_toEnvExtension_835_; lean_object* v_asyncMode_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
v_env_833_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_env_833_);
lean_dec(v___x_804_);
v___x_834_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_835_ = lean_ctor_get(v___x_834_, 0);
v_asyncMode_836_ = lean_ctor_get(v_toEnvExtension_835_, 2);
v___x_837_ = 0;
v___x_838_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_803_, v___x_834_, v_env_833_, v_declName_733_, v_asyncMode_836_, v___x_837_);
if (lean_obj_tag(v___x_838_) == 1)
{
lean_object* v_val_839_; lean_object* v___y_841_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_val_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_845_ = l_Lean_Meta_eqnAffectingOptions;
v___x_846_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_846_ == 0)
{
lean_inc_ref(v_options_812_);
v___y_841_ = v_options_812_;
goto v___jp_840_;
}
else
{
uint8_t v___x_847_; 
v___x_847_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_847_ == 0)
{
if (v___x_846_ == 0)
{
lean_inc_ref(v_options_812_);
v___y_841_ = v_options_812_;
goto v___jp_840_;
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = ((size_t)0ULL);
v___x_849_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_812_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_845_, v___x_848_, v___x_849_, v_options_812_);
v___y_841_ = v___x_850_;
goto v___jp_840_;
}
}
else
{
size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v___x_851_ = ((size_t)0ULL);
v___x_852_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_812_);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_845_, v___x_851_, v___x_852_, v_options_812_);
v___y_841_ = v___x_853_;
goto v___jp_840_;
}
}
v___jp_840_:
{
size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_844_; 
v_sz_842_ = lean_array_size(v_val_839_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_839_, v_sz_842_, v___x_843_, v___y_841_);
lean_dec(v_val_839_);
v___y_822_ = v___x_844_;
goto v___jp_821_;
}
}
else
{
lean_object* v___x_854_; uint8_t v___x_855_; 
lean_dec(v___x_838_);
v___x_854_ = l_Lean_Meta_eqnAffectingOptions;
v___x_855_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_855_ == 0)
{
lean_inc_ref(v_options_812_);
v___y_822_ = v_options_812_;
goto v___jp_821_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_856_ == 0)
{
if (v___x_855_ == 0)
{
lean_inc_ref(v_options_812_);
v___y_822_ = v_options_812_;
goto v___jp_821_;
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_812_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_854_, v___x_857_, v___x_858_, v_options_812_);
v___y_822_ = v___x_859_;
goto v___jp_821_;
}
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_812_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_854_, v___x_860_, v___x_861_, v_options_812_);
v___y_822_ = v___x_862_;
goto v___jp_821_;
}
}
}
}
else
{
lean_object* v___x_863_; 
lean_dec(v___x_804_);
lean_dec(v_declName_733_);
lean_inc_ref(v_options_812_);
v___x_863_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_812_);
v___y_822_ = v___x_863_;
goto v___jp_821_;
}
v___jp_740_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_758_ = l_Lean_maxRecDepth;
v___x_759_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_742_, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_760_, 0, v_fileName_743_);
lean_ctor_set(v___x_760_, 1, v_fileMap_744_);
lean_ctor_set(v___x_760_, 2, v___y_742_);
lean_ctor_set(v___x_760_, 3, v___x_759_);
lean_ctor_set(v___x_760_, 4, v_currNamespace_745_);
lean_ctor_set(v___x_760_, 5, v_openDecls_746_);
lean_ctor_set(v___x_760_, 6, v_initHeartbeats_747_);
lean_ctor_set(v___x_760_, 7, v_maxHeartbeats_748_);
lean_ctor_set(v___x_760_, 8, v_quotContext_749_);
lean_ctor_set(v___x_760_, 9, v_currMacroScope_750_);
lean_ctor_set(v___x_760_, 10, v_cancelTk_x3f_751_);
lean_ctor_set(v___x_760_, 11, v_inheritedTraceOptions_752_);
lean_inc(v_ref_754_);
lean_inc(v_currRecDepth_753_);
v___x_761_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v_currRecDepth_753_);
lean_ctor_set(v___x_761_, 2, v_ref_754_);
lean_ctor_set_uint16(v___x_761_, sizeof(void*)*3, v___y_741_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*3 + 2, v_suppressElabErrors_755_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*3 + 3, v_isRecordingDeps_756_);
lean_inc(v___y_757_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
v___x_762_ = lean_apply_5(v_act_734_, v_a_735_, v_a_736_, v___x_761_, v___y_757_, lean_box(0));
return v___x_762_;
}
v___jp_763_:
{
lean_object* v___x_767_; lean_object* v_env_768_; lean_object* v_nextMacroScope_769_; lean_object* v_ngen_770_; lean_object* v_auxDeclNGen_771_; lean_object* v_traceState_772_; lean_object* v_recordedDeps_773_; lean_object* v_messages_774_; lean_object* v_infoState_775_; lean_object* v_snapshotTasks_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_801_; 
v___x_767_ = lean_st_ref_take(v_a_738_);
v_env_768_ = lean_ctor_get(v___x_767_, 0);
v_nextMacroScope_769_ = lean_ctor_get(v___x_767_, 1);
v_ngen_770_ = lean_ctor_get(v___x_767_, 2);
v_auxDeclNGen_771_ = lean_ctor_get(v___x_767_, 3);
v_traceState_772_ = lean_ctor_get(v___x_767_, 4);
v_recordedDeps_773_ = lean_ctor_get(v___x_767_, 6);
v_messages_774_ = lean_ctor_get(v___x_767_, 7);
v_infoState_775_ = lean_ctor_get(v___x_767_, 8);
v_snapshotTasks_776_ = lean_ctor_get(v___x_767_, 9);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v___x_767_, 5);
lean_dec(v_unused_802_);
v___x_778_ = v___x_767_;
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snapshotTasks_776_);
lean_inc(v_infoState_775_);
lean_inc(v_messages_774_);
lean_inc(v_recordedDeps_773_);
lean_inc(v_traceState_772_);
lean_inc(v_auxDeclNGen_771_);
lean_inc(v_ngen_770_);
lean_inc(v_nextMacroScope_769_);
lean_inc(v_env_768_);
lean_dec(v___x_767_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_780_ = l_Lean_Kernel_enableDiag(v_env_768_, v___y_764_);
v___x_781_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 5, v___x_781_);
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_nextMacroScope_769_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_ngen_770_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_auxDeclNGen_771_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_traceState_772_);
lean_ctor_set(v_reuseFailAlloc_800_, 5, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_800_, 6, v_recordedDeps_773_);
lean_ctor_set(v_reuseFailAlloc_800_, 7, v_messages_774_);
lean_ctor_set(v_reuseFailAlloc_800_, 8, v_infoState_775_);
lean_ctor_set(v_reuseFailAlloc_800_, 9, v_snapshotTasks_776_);
v___x_783_ = v_reuseFailAlloc_800_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v_toCold_785_; lean_object* v_currRecDepth_786_; lean_object* v_ref_787_; uint8_t v_suppressElabErrors_788_; uint8_t v_isRecordingDeps_789_; lean_object* v_fileName_790_; lean_object* v_fileMap_791_; lean_object* v_currNamespace_792_; lean_object* v_openDecls_793_; lean_object* v_initHeartbeats_794_; lean_object* v_maxHeartbeats_795_; lean_object* v_quotContext_796_; lean_object* v_currMacroScope_797_; lean_object* v_cancelTk_x3f_798_; lean_object* v_inheritedTraceOptions_799_; 
v___x_784_ = lean_st_ref_put(v_a_738_, v___x_783_);
v_toCold_785_ = lean_ctor_get(v_a_737_, 0);
v_currRecDepth_786_ = lean_ctor_get(v_a_737_, 1);
v_ref_787_ = lean_ctor_get(v_a_737_, 2);
v_suppressElabErrors_788_ = lean_ctor_get_uint8(v_a_737_, sizeof(void*)*3 + 2);
v_isRecordingDeps_789_ = lean_ctor_get_uint8(v_a_737_, sizeof(void*)*3 + 3);
v_fileName_790_ = lean_ctor_get(v_toCold_785_, 0);
v_fileMap_791_ = lean_ctor_get(v_toCold_785_, 1);
v_currNamespace_792_ = lean_ctor_get(v_toCold_785_, 4);
v_openDecls_793_ = lean_ctor_get(v_toCold_785_, 5);
v_initHeartbeats_794_ = lean_ctor_get(v_toCold_785_, 6);
v_maxHeartbeats_795_ = lean_ctor_get(v_toCold_785_, 7);
v_quotContext_796_ = lean_ctor_get(v_toCold_785_, 8);
v_currMacroScope_797_ = lean_ctor_get(v_toCold_785_, 9);
v_cancelTk_x3f_798_ = lean_ctor_get(v_toCold_785_, 10);
v_inheritedTraceOptions_799_ = lean_ctor_get(v_toCold_785_, 11);
lean_inc_ref(v_inheritedTraceOptions_799_);
lean_inc(v_cancelTk_x3f_798_);
lean_inc(v_currMacroScope_797_);
lean_inc(v_quotContext_796_);
lean_inc(v_maxHeartbeats_795_);
lean_inc(v_initHeartbeats_794_);
lean_inc(v_openDecls_793_);
lean_inc(v_currNamespace_792_);
lean_inc_ref(v_fileMap_791_);
lean_inc_ref(v_fileName_790_);
v___y_741_ = v___y_765_;
v___y_742_ = v___y_766_;
v_fileName_743_ = v_fileName_790_;
v_fileMap_744_ = v_fileMap_791_;
v_currNamespace_745_ = v_currNamespace_792_;
v_openDecls_746_ = v_openDecls_793_;
v_initHeartbeats_747_ = v_initHeartbeats_794_;
v_maxHeartbeats_748_ = v_maxHeartbeats_795_;
v_quotContext_749_ = v_quotContext_796_;
v_currMacroScope_750_ = v_currMacroScope_797_;
v_cancelTk_x3f_751_ = v_cancelTk_x3f_798_;
v_inheritedTraceOptions_752_ = v_inheritedTraceOptions_799_;
v_currRecDepth_753_ = v_currRecDepth_786_;
v_ref_754_ = v_ref_787_;
v_suppressElabErrors_755_ = v_suppressElabErrors_788_;
v_isRecordingDeps_756_ = v_isRecordingDeps_789_;
v___y_757_ = v_a_738_;
goto v___jp_740_;
}
}
}
v___jp_821_:
{
uint16_t v___x_823_; lean_object* v___x_824_; lean_object* v_env_825_; uint8_t v___x_826_; uint16_t v___x_827_; uint16_t v___x_828_; uint16_t v___x_829_; uint8_t v___x_830_; 
v___x_823_ = l_Lean_OptionFlags_ofOptions(v___y_822_);
v___x_824_ = lean_st_ref_get(v_a_738_);
v_env_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc_ref(v_env_825_);
lean_dec(v___x_824_);
v___x_826_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_825_);
lean_dec_ref(v_env_825_);
v___x_827_ = 512;
v___x_828_ = lean_uint16_land(v___x_823_, v___x_827_);
v___x_829_ = 0;
v___x_830_ = lean_uint16_dec_eq(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
if (v___x_826_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = 1;
v___y_764_ = v___x_831_;
v___y_765_ = v___x_823_;
v___y_766_ = v___y_822_;
goto v___jp_763_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_820_);
lean_inc(v_cancelTk_x3f_819_);
lean_inc(v_currMacroScope_818_);
lean_inc(v_quotContext_817_);
lean_inc(v_maxHeartbeats_816_);
lean_inc(v_initHeartbeats_815_);
lean_inc(v_openDecls_814_);
lean_inc(v_currNamespace_813_);
lean_inc_ref(v_fileMap_811_);
lean_inc_ref(v_fileName_810_);
v___y_741_ = v___x_823_;
v___y_742_ = v___y_822_;
v_fileName_743_ = v_fileName_810_;
v_fileMap_744_ = v_fileMap_811_;
v_currNamespace_745_ = v_currNamespace_813_;
v_openDecls_746_ = v_openDecls_814_;
v_initHeartbeats_747_ = v_initHeartbeats_815_;
v_maxHeartbeats_748_ = v_maxHeartbeats_816_;
v_quotContext_749_ = v_quotContext_817_;
v_currMacroScope_750_ = v_currMacroScope_818_;
v_cancelTk_x3f_751_ = v_cancelTk_x3f_819_;
v_inheritedTraceOptions_752_ = v_inheritedTraceOptions_820_;
v_currRecDepth_753_ = v_currRecDepth_806_;
v_ref_754_ = v_ref_807_;
v_suppressElabErrors_755_ = v_suppressElabErrors_808_;
v_isRecordingDeps_756_ = v_isRecordingDeps_809_;
v___y_757_ = v_a_738_;
goto v___jp_740_;
}
}
else
{
if (v___x_826_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_820_);
lean_inc(v_cancelTk_x3f_819_);
lean_inc(v_currMacroScope_818_);
lean_inc(v_quotContext_817_);
lean_inc(v_maxHeartbeats_816_);
lean_inc(v_initHeartbeats_815_);
lean_inc(v_openDecls_814_);
lean_inc(v_currNamespace_813_);
lean_inc_ref(v_fileMap_811_);
lean_inc_ref(v_fileName_810_);
v___y_741_ = v___x_823_;
v___y_742_ = v___y_822_;
v_fileName_743_ = v_fileName_810_;
v_fileMap_744_ = v_fileMap_811_;
v_currNamespace_745_ = v_currNamespace_813_;
v_openDecls_746_ = v_openDecls_814_;
v_initHeartbeats_747_ = v_initHeartbeats_815_;
v_maxHeartbeats_748_ = v_maxHeartbeats_816_;
v_quotContext_749_ = v_quotContext_817_;
v_currMacroScope_750_ = v_currMacroScope_818_;
v_cancelTk_x3f_751_ = v_cancelTk_x3f_819_;
v_inheritedTraceOptions_752_ = v_inheritedTraceOptions_820_;
v_currRecDepth_753_ = v_currRecDepth_806_;
v_ref_754_ = v_ref_807_;
v_suppressElabErrors_755_ = v_suppressElabErrors_808_;
v_isRecordingDeps_756_ = v_isRecordingDeps_809_;
v___y_757_ = v_a_738_;
goto v___jp_740_;
}
else
{
uint8_t v___x_832_; 
v___x_832_ = 0;
v___y_764_ = v___x_832_;
v___y_765_ = v___x_823_;
v___y_766_ = v___y_822_;
goto v___jp_763_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withEqnOptions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_733_ = stack[0].m_obj;
lean_object* v_act_734_ = stack[1].m_obj;
lean_object* v_a_735_ = stack[2].m_obj;
lean_object* v_a_736_ = stack[3].m_obj;
lean_object* v_a_737_ = stack[4].m_obj;
lean_object* v_a_738_ = stack[5].m_obj;
lean_object* v_res_864_;
v_res_864_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_733_, v_act_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_865_, lean_object* v_act_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_865_, v_act_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
return v_res_872_;
}
}
lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_873_, lean_object* v_declName_874_, lean_object* v_act_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_874_, v_act_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
return v___x_881_;
}
}
LEAN_EXPORT void l_Lean_Meta_withEqnOptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_874_ = stack[1].m_obj;
lean_object* v_act_875_ = stack[2].m_obj;
lean_object* v_a_876_ = stack[3].m_obj;
lean_object* v_a_877_ = stack[4].m_obj;
lean_object* v_a_878_ = stack[5].m_obj;
lean_object* v_a_879_ = stack[6].m_obj;
lean_object* v_res_882_;
v_res_882_ = l_Lean_Meta_withEqnOptions(lean_box(0), v_declName_874_, v_act_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_883_, lean_object* v_declName_884_, lean_object* v_act_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_883_, v_declName_884_, v_act_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_891_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_env_896_; lean_object* v_toConstantVal_897_; lean_object* v_value_898_; lean_object* v_all_899_; uint8_t v___y_901_; lean_object* v_type_909_; uint8_t v___x_910_; 
v___x_895_ = lean_st_ref_get(v___y_893_);
v_env_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref_n(v_env_896_, 2);
lean_dec(v___x_895_);
v_toConstantVal_897_ = lean_ctor_get(v_thm_892_, 0);
v_value_898_ = lean_ctor_get(v_thm_892_, 1);
v_all_899_ = lean_ctor_get(v_thm_892_, 2);
v_type_909_ = lean_ctor_get(v_toConstantVal_897_, 2);
v___x_910_ = l_Lean_Environment_hasUnsafe(v_env_896_, v_type_909_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_Environment_hasUnsafe(v_env_896_, v_value_898_);
v___y_901_ = v___x_911_;
goto v___jp_900_;
}
else
{
lean_dec_ref(v_env_896_);
v___y_901_ = v___x_910_;
goto v___jp_900_;
}
v___jp_900_:
{
if (v___y_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_902_, 0, v_thm_892_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_inc(v_all_899_);
lean_inc_ref(v_value_898_);
lean_inc_ref(v_toConstantVal_897_);
lean_dec_ref(v_thm_892_);
v___x_904_ = lean_box(0);
v___x_905_ = 0;
v___x_906_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_906_, 0, v_toConstantVal_897_);
lean_ctor_set(v___x_906_, 1, v_value_898_);
lean_ctor_set(v___x_906_, 2, v___x_904_);
lean_ctor_set(v___x_906_, 3, v_all_899_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*4, v___x_905_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_892_ = stack[0].m_obj;
lean_object* v___y_893_ = stack[1].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_892_, v___y_893_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_913_, v___y_914_);
lean_dec(v___y_914_);
return v_res_916_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_917_, v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_917_ = stack[0].m_obj;
lean_object* v___y_918_ = stack[1].m_obj;
lean_object* v___y_919_ = stack[2].m_obj;
lean_object* v___y_920_ = stack[3].m_obj;
lean_object* v___y_921_ = stack[4].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_932_, lean_object* v_b_933_, lean_object* v_c_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
v___x_940_ = lean_apply_7(v_k_932_, v_b_933_, v_c_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, lean_box(0));
return v___x_940_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_932_ = stack[0].m_obj;
lean_object* v_b_933_ = stack[1].m_obj;
lean_object* v_c_934_ = stack[2].m_obj;
lean_object* v___y_935_ = stack[3].m_obj;
lean_object* v___y_936_ = stack[4].m_obj;
lean_object* v___y_937_ = stack[5].m_obj;
lean_object* v___y_938_ = stack[6].m_obj;
lean_object* v_res_941_;
v_res_941_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_932_, v_b_933_, v_c_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_942_, lean_object* v_b_943_, lean_object* v_c_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_942_, v_b_943_, v_c_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_951_, lean_object* v_k_952_, uint8_t v_cleanupAnnotations_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___f_959_; uint8_t v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___f_959_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_959_, 0, v_k_952_);
v___x_960_ = 1;
v___x_961_ = 0;
v___x_962_ = lean_box(0);
v___x_963_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_951_, v___x_960_, v___x_961_, v___x_960_, v___x_961_, v___x_962_, v___f_959_, v_cleanupAnnotations_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_a_972_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_963_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_963_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_951_ = stack[0].m_obj;
lean_object* v_k_952_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_953_ = stack[2].m_num;
lean_object* v___y_954_ = stack[3].m_obj;
lean_object* v___y_955_ = stack[4].m_obj;
lean_object* v___y_956_ = stack[5].m_obj;
lean_object* v___y_957_ = stack[6].m_obj;
lean_object* v_res_980_;
v_res_980_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_951_, v_k_952_, v_cleanupAnnotations_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
stack->m_obj
 = v_res_980_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_981_, lean_object* v_k_982_, lean_object* v_cleanupAnnotations_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_989_; lean_object* v_res_990_; 
v_cleanupAnnotations_boxed_989_ = lean_unbox(v_cleanupAnnotations_983_);
v_res_990_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_981_, v_k_982_, v_cleanupAnnotations_boxed_989_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_990_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_991_, lean_object* v_e_992_, lean_object* v_k_993_, uint8_t v_cleanupAnnotations_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_992_, v_k_993_, v_cleanupAnnotations_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1000_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_992_ = stack[1].m_obj;
lean_object* v_k_993_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_994_ = stack[3].m_num;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v___y_996_ = stack[5].m_obj;
lean_object* v___y_997_ = stack[6].m_obj;
lean_object* v___y_998_ = stack[7].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_box(0), v_e_992_, v_k_993_, v_cleanupAnnotations_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_e_1003_, lean_object* v_k_1004_, lean_object* v_cleanupAnnotations_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1011_; lean_object* v_res_1012_; 
v_cleanupAnnotations_boxed_1011_ = lean_unbox(v_cleanupAnnotations_1005_);
v_res_1012_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_1002_, v_e_1003_, v_k_1004_, v_cleanupAnnotations_boxed_1011_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = l_List_reverse___redArg(v_a_1014_);
return v___x_1015_;
}
else
{
lean_object* v_head_1016_; lean_object* v_tail_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1026_; 
v_head_1016_ = lean_ctor_get(v_a_1013_, 0);
v_tail_1017_ = lean_ctor_get(v_a_1013_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1019_ = v_a_1013_;
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_tail_1017_);
lean_inc(v_head_1016_);
lean_dec(v_a_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = l_Lean_mkLevelParam(v_head_1016_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_1014_);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1023_ = v___x_1019_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_a_1014_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v_a_1013_ = v_tail_1017_;
v_a_1014_ = v___x_1023_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_1027_, lean_object* v_name_1028_, lean_object* v_xs_1029_, lean_object* v_body_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_name_1036_; lean_object* v_levelParams_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1107_; 
v_name_1036_ = lean_ctor_get(v_toConstantVal_1027_, 0);
v_levelParams_1037_ = lean_ctor_get(v_toConstantVal_1027_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_toConstantVal_1027_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_toConstantVal_1027_, 2);
lean_dec(v_unused_1108_);
v___x_1039_ = v_toConstantVal_1027_;
v_isShared_1040_ = v_isSharedCheck_1107_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_levelParams_1037_);
lean_inc(v_name_1036_);
lean_dec(v_toConstantVal_1027_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1107_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_lhs_1044_; lean_object* v___x_1045_; 
v___x_1041_ = lean_box(0);
lean_inc(v_levelParams_1037_);
v___x_1042_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_1037_, v___x_1041_);
v___x_1043_ = l_Lean_mkConst(v_name_1036_, v___x_1042_);
v_lhs_1044_ = l_Lean_mkAppN(v___x_1043_, v_xs_1029_);
lean_inc_ref(v_lhs_1044_);
v___x_1045_ = l_Lean_Meta_mkEq(v_lhs_1044_, v_body_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; uint8_t v___x_1047_; uint8_t v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = 0;
v___x_1048_ = 1;
v___x_1049_ = 1;
v___x_1050_ = l_Lean_Meta_mkForallFVars(v_xs_1029_, v_a_1046_, v___x_1047_, v___x_1048_, v___x_1048_, v___x_1049_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = l_Lean_Meta_letToHave(v_a_1051_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = l_Lean_Meta_mkEqRefl(v_lhs_1044_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = l_Lean_Meta_mkLambdaFVars(v_xs_1029_, v_a_1055_, v___x_1047_, v___x_1048_, v___x_1047_, v___x_1048_, v___x_1049_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
lean_inc(v_name_1028_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 2, v_a_1053_);
lean_ctor_set(v___x_1039_, 0, v_name_1028_);
v___x_1059_ = v___x_1039_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_name_1028_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_levelParams_1037_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_a_1053_);
v___x_1059_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_a_1063_; lean_object* v___x_1064_; 
lean_inc(v_name_1028_);
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_name_1028_);
lean_ctor_set(v___x_1060_, 1, v___x_1041_);
v___x_1061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v_a_1057_);
lean_ctor_set(v___x_1061_, 2, v___x_1060_);
v___x_1062_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_1061_, v___y_1034_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = l_Lean_addDecl(v_a_1063_, v___x_1047_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1065_; 
lean_dec_ref_known(v___x_1064_, 1);
v___x_1065_ = l_Lean_inferDefEqAttr(v_name_1028_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1065_;
}
else
{
lean_dec(v_name_1028_);
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1053_);
lean_del_object(v___x_1039_);
lean_dec(v_levelParams_1037_);
lean_dec(v_name_1028_);
v_a_1067_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1056_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1056_);
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
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_a_1053_);
lean_del_object(v___x_1039_);
lean_dec(v_levelParams_1037_);
lean_dec(v_name_1028_);
v_a_1075_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1054_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1054_);
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
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_lhs_1044_);
lean_del_object(v___x_1039_);
lean_dec(v_levelParams_1037_);
lean_dec(v_name_1028_);
v_a_1083_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1052_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1052_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v_lhs_1044_);
lean_del_object(v___x_1039_);
lean_dec(v_levelParams_1037_);
lean_dec(v_name_1028_);
v_a_1091_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1050_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1050_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
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
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_lhs_1044_);
lean_del_object(v___x_1039_);
lean_dec(v_levelParams_1037_);
lean_dec(v_name_1028_);
v_a_1099_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1045_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1045_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toConstantVal_1027_ = stack[0].m_obj;
lean_object* v_name_1028_ = stack[1].m_obj;
lean_object* v_xs_1029_ = stack[2].m_obj;
lean_object* v_body_1030_ = stack[3].m_obj;
lean_object* v___y_1031_ = stack[4].m_obj;
lean_object* v___y_1032_ = stack[5].m_obj;
lean_object* v___y_1033_ = stack[6].m_obj;
lean_object* v___y_1034_ = stack[7].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1027_, v_name_1028_, v_xs_1029_, v_body_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1110_, lean_object* v_name_1111_, lean_object* v_xs_1112_, lean_object* v_body_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1110_, v_name_1111_, v_xs_1112_, v_body_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_xs_1112_);
return v_res_1119_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1120_, lean_object* v_info_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_toConstantVal_1127_; lean_object* v_value_1128_; lean_object* v___f_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; 
v_toConstantVal_1127_ = lean_ctor_get(v_info_1121_, 0);
lean_inc_ref(v_toConstantVal_1127_);
v_value_1128_ = lean_ctor_get(v_info_1121_, 1);
lean_inc_ref(v_value_1128_);
lean_dec_ref(v_info_1121_);
v___f_1129_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1129_, 0, v_toConstantVal_1127_);
lean_closure_set(v___f_1129_, 1, v_name_1120_);
v___x_1130_ = 1;
v___x_1131_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1128_, v___f_1129_, v___x_1130_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
return v___x_1131_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1120_ = stack[0].m_obj;
lean_object* v_info_1121_ = stack[1].m_obj;
lean_object* v_a_1122_ = stack[2].m_obj;
lean_object* v_a_1123_ = stack[3].m_obj;
lean_object* v_a_1124_ = stack[4].m_obj;
lean_object* v_a_1125_ = stack[5].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1120_, v_info_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1133_, lean_object* v_info_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1133_, v_info_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
return v_res_1140_;
}
}
lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1141_, lean_object* v_name_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1151_; lean_object* v_env_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = lean_st_ref_get(v_a_1146_);
v_env_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_ref(v_env_1152_);
lean_dec(v___x_1151_);
v___x_1153_ = 0;
lean_inc(v_declName_1141_);
v___x_1154_ = l_Lean_Environment_find_x3f(v_env_1152_, v_declName_1141_, v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 1)
{
lean_object* v_val_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1182_; 
v_val_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1182_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_val_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1182_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
if (lean_obj_tag(v_val_1155_) == 1)
{
lean_object* v_val_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_val_1159_ = lean_ctor_get(v_val_1155_, 0);
lean_inc_ref(v_val_1159_);
lean_dec_ref_known(v_val_1155_, 1);
lean_inc_n(v_name_1142_, 2);
v___x_1160_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1160_, 0, v_name_1142_);
lean_closure_set(v___x_1160_, 1, v_val_1159_);
lean_inc(v_declName_1141_);
v___x_1161_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1161_, 0, lean_box(0));
lean_closure_set(v___x_1161_, 1, v_declName_1141_);
lean_closure_set(v___x_1161_, 2, v___x_1160_);
v___x_1162_ = l_Lean_Meta_realizeConst(v_declName_1141_, v_name_1142_, v___x_1161_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1172_; 
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1173_);
v___x_1164_ = v___x_1162_;
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v___x_1162_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_name_1142_);
v___x_1167_ = v___x_1157_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_name_1142_);
v___x_1167_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_del_object(v___x_1157_);
lean_dec(v_name_1142_);
v_a_1174_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1162_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1162_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_del_object(v___x_1157_);
lean_dec(v_val_1155_);
lean_dec(v_name_1142_);
lean_dec(v_declName_1141_);
goto v___jp_1148_;
}
}
}
else
{
lean_dec(v___x_1154_);
lean_dec(v_name_1142_);
lean_dec(v_declName_1141_);
goto v___jp_1148_;
}
v___jp_1148_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkSimpleEqThm_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1141_ = stack[0].m_obj;
lean_object* v_name_1142_ = stack[1].m_obj;
lean_object* v_a_1143_ = stack[2].m_obj;
lean_object* v_a_1144_ = stack[3].m_obj;
lean_object* v_a_1145_ = stack[4].m_obj;
lean_object* v_a_1146_ = stack[5].m_obj;
lean_object* v_res_1183_;
v_res_1183_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1141_, v_name_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
stack->m_obj
 = v_res_1183_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1184_, lean_object* v_name_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1184_, v_name_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1192_, lean_object* v_vals_1193_, lean_object* v_i_1194_, lean_object* v_k_1195_){
_start:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_array_get_size(v_keys_1192_);
v___x_1197_ = lean_nat_dec_lt(v_i_1194_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v_i_1194_);
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
else
{
lean_object* v_k_x27_1199_; uint8_t v___x_1200_; 
v_k_x27_1199_ = lean_array_fget_borrowed(v_keys_1192_, v_i_1194_);
v___x_1200_ = lean_name_eq(v_k_1195_, v_k_x27_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = lean_nat_add(v_i_1194_, v___x_1201_);
lean_dec(v_i_1194_);
v_i_1194_ = v___x_1202_;
goto _start;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_array_fget_borrowed(v_vals_1193_, v_i_1194_);
lean_dec(v_i_1194_);
lean_inc(v___x_1204_);
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1206_, lean_object* v_vals_1207_, lean_object* v_i_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1206_, v_vals_1207_, v_i_1208_, v_k_1209_);
lean_dec(v_k_1209_);
lean_dec_ref(v_vals_1207_);
lean_dec_ref(v_keys_1206_);
return v_res_1210_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1211_, size_t v_x_1212_, lean_object* v_x_1213_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 0)
{
lean_object* v_es_1214_; lean_object* v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; lean_object* v_j_1218_; lean_object* v___x_1219_; 
v_es_1214_ = lean_ctor_get(v_x_1211_, 0);
v___x_1215_ = lean_box(2);
v___x_1216_ = ((size_t)31ULL);
v___x_1217_ = lean_usize_land(v_x_1212_, v___x_1216_);
v_j_1218_ = lean_usize_to_nat(v___x_1217_);
v___x_1219_ = lean_array_get_borrowed(v___x_1215_, v_es_1214_, v_j_1218_);
lean_dec(v_j_1218_);
switch(lean_obj_tag(v___x_1219_))
{
case 0:
{
lean_object* v_key_1220_; lean_object* v_val_1221_; uint8_t v___x_1222_; 
v_key_1220_ = lean_ctor_get(v___x_1219_, 0);
v_val_1221_ = lean_ctor_get(v___x_1219_, 1);
v___x_1222_ = lean_name_eq(v_x_1213_, v_key_1220_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_box(0);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; 
lean_inc(v_val_1221_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_val_1221_);
return v___x_1224_;
}
}
case 1:
{
lean_object* v_node_1225_; size_t v___x_1226_; size_t v___x_1227_; 
v_node_1225_ = lean_ctor_get(v___x_1219_, 0);
v___x_1226_ = ((size_t)5ULL);
v___x_1227_ = lean_usize_shift_right(v_x_1212_, v___x_1226_);
v_x_1211_ = v_node_1225_;
v_x_1212_ = v___x_1227_;
goto _start;
}
default: 
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_box(0);
return v___x_1229_;
}
}
}
else
{
lean_object* v_ks_1230_; lean_object* v_vs_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_ks_1230_ = lean_ctor_get(v_x_1211_, 0);
v_vs_1231_ = lean_ctor_get(v_x_1211_, 1);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1230_, v_vs_1231_, v___x_1232_, v_x_1213_);
return v___x_1233_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1211_ = stack[0].m_obj;
size_t v_x_1212_ = stack[1].m_num;
lean_object* v_x_1213_ = stack[2].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1211_, v_x_1212_, v_x_1213_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
size_t v_x_353__boxed_1238_; lean_object* v_res_1239_; 
v_x_353__boxed_1238_ = lean_unbox_usize(v_x_1236_);
lean_dec(v_x_1236_);
v_res_1239_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1235_, v_x_353__boxed_1238_, v_x_1237_);
lean_dec(v_x_1237_);
lean_dec_ref(v_x_1235_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
uint64_t v___y_1243_; 
if (lean_obj_tag(v_x_1241_) == 0)
{
uint64_t v___x_1246_; 
v___x_1246_ = 1723ULL;
v___y_1243_ = v___x_1246_;
goto v___jp_1242_;
}
else
{
uint64_t v_hash_1247_; 
v_hash_1247_ = lean_ctor_get_uint64(v_x_1241_, sizeof(void*)*2);
v___y_1243_ = v_hash_1247_;
goto v___jp_1242_;
}
v___jp_1242_:
{
size_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_uint64_to_usize(v___y_1243_);
v___x_1245_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1240_, v___x_1244_, v_x_1241_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1248_, v_x_1249_);
lean_dec(v_x_1249_);
lean_dec_ref(v_x_1248_);
return v_res_1250_;
}
}
lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_env_1256_; lean_object* v___x_1257_; lean_object* v_asyncMode_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1254_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1255_ = lean_st_ref_get(v_a_1252_);
v_env_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc_ref(v_env_1256_);
lean_dec(v___x_1255_);
v___x_1257_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1258_ = lean_ctor_get(v___x_1257_, 2);
v___x_1259_ = lean_box(0);
v___x_1260_ = 0;
v___x_1261_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1254_, v___x_1257_, v_env_1256_, v_asyncMode_1258_, v___x_1259_, v___x_1260_);
v___x_1262_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1261_, v_thmName_1251_);
lean_dec(v___x_1261_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT void l_Lean_Meta_isEqnThm_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmName_1251_ = stack[0].m_obj;
lean_object* v_a_1252_ = stack[1].m_obj;
lean_object* v_res_1264_;
v_res_1264_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1251_, v_a_1252_);
stack->m_obj
 = v_res_1264_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec(v_thmName_1265_);
return v_res_1268_;
}
}
lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1269_, v_a_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT void l_Lean_Meta_isEqnThm_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmName_1269_ = stack[0].m_obj;
lean_object* v_a_1270_ = stack[1].m_obj;
lean_object* v_a_1271_ = stack[2].m_obj;
lean_object* v_res_1274_;
v_res_1274_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1269_, v_a_1270_, v_a_1271_);
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_thmName_1275_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1281_, v_x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1284_, v_x_1285_, v_x_1286_);
lean_dec(v_x_1286_);
lean_dec_ref(v_x_1285_);
return v_res_1287_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_, size_t v_x_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1289_, v_x_1290_, v_x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1289_ = stack[1].m_obj;
size_t v_x_1290_ = stack[2].m_num;
lean_object* v_x_1291_ = stack[3].m_obj;
lean_object* v_res_1293_;
v_res_1293_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_box(0), v_x_1289_, v_x_1290_, v_x_1291_);
stack->m_obj
 = v_res_1293_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
size_t v_x_500__boxed_1298_; lean_object* v_res_1299_; 
v_x_500__boxed_1298_ = lean_unbox_usize(v_x_1296_);
lean_dec(v_x_1296_);
v_res_1299_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1294_, v_x_1295_, v_x_500__boxed_1298_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec_ref(v_x_1295_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1300_, lean_object* v_keys_1301_, lean_object* v_vals_1302_, lean_object* v_heq_1303_, lean_object* v_i_1304_, lean_object* v_k_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1301_, v_vals_1302_, v_i_1304_, v_k_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1307_, lean_object* v_keys_1308_, lean_object* v_vals_1309_, lean_object* v_heq_1310_, lean_object* v_i_1311_, lean_object* v_k_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1307_, v_keys_1308_, v_vals_1309_, v_heq_1310_, v_i_1311_, v_k_1312_);
lean_dec(v_k_1312_);
lean_dec_ref(v_vals_1309_);
lean_dec_ref(v_keys_1308_);
return v_res_1313_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1314_, lean_object* v_i_1315_, lean_object* v_k_1316_){
_start:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_array_get_size(v_keys_1314_);
v___x_1318_ = lean_nat_dec_lt(v_i_1315_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec(v_i_1315_);
return v___x_1318_;
}
else
{
lean_object* v_k_x27_1319_; uint8_t v___x_1320_; 
v_k_x27_1319_ = lean_array_fget_borrowed(v_keys_1314_, v_i_1315_);
v___x_1320_ = lean_name_eq(v_k_1316_, v_k_x27_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_add(v_i_1315_, v___x_1321_);
lean_dec(v_i_1315_);
v_i_1315_ = v___x_1322_;
goto _start;
}
else
{
lean_dec(v_i_1315_);
return v___x_1318_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1314_ = stack[0].m_obj;
lean_object* v_i_1315_ = stack[1].m_obj;
lean_object* v_k_1316_ = stack[2].m_obj;
uint8_t v_res_1324_;
v_res_1324_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1314_, v_i_1315_, v_k_1316_);
stack->m_num = v_res_1324_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1325_, lean_object* v_i_1326_, lean_object* v_k_1327_){
_start:
{
uint8_t v_res_1328_; lean_object* v_r_1329_; 
v_res_1328_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1325_, v_i_1326_, v_k_1327_);
lean_dec(v_k_1327_);
lean_dec_ref(v_keys_1325_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1330_, size_t v_x_1331_, lean_object* v_x_1332_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 0)
{
lean_object* v_es_1333_; lean_object* v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; lean_object* v_j_1337_; lean_object* v___x_1338_; 
v_es_1333_ = lean_ctor_get(v_x_1330_, 0);
v___x_1334_ = lean_box(2);
v___x_1335_ = ((size_t)31ULL);
v___x_1336_ = lean_usize_land(v_x_1331_, v___x_1335_);
v_j_1337_ = lean_usize_to_nat(v___x_1336_);
v___x_1338_ = lean_array_get_borrowed(v___x_1334_, v_es_1333_, v_j_1337_);
lean_dec(v_j_1337_);
switch(lean_obj_tag(v___x_1338_))
{
case 0:
{
lean_object* v_key_1339_; uint8_t v___x_1340_; 
v_key_1339_ = lean_ctor_get(v___x_1338_, 0);
v___x_1340_ = lean_name_eq(v_x_1332_, v_key_1339_);
return v___x_1340_;
}
case 1:
{
lean_object* v_node_1341_; size_t v___x_1342_; size_t v___x_1343_; 
v_node_1341_ = lean_ctor_get(v___x_1338_, 0);
v___x_1342_ = ((size_t)5ULL);
v___x_1343_ = lean_usize_shift_right(v_x_1331_, v___x_1342_);
v_x_1330_ = v_node_1341_;
v_x_1331_ = v___x_1343_;
goto _start;
}
default: 
{
uint8_t v___x_1345_; 
v___x_1345_ = 0;
return v___x_1345_;
}
}
}
else
{
lean_object* v_ks_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_ks_1346_ = lean_ctor_get(v_x_1330_, 0);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1346_, v___x_1347_, v_x_1332_);
return v___x_1348_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1330_ = stack[0].m_obj;
size_t v_x_1331_ = stack[1].m_num;
lean_object* v_x_1332_ = stack[2].m_obj;
uint8_t v_res_1349_;
v_res_1349_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1330_, v_x_1331_, v_x_1332_);
stack->m_num = v_res_1349_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
size_t v_x_334__boxed_1353_; uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_x_334__boxed_1353_ = lean_unbox_usize(v_x_1351_);
lean_dec(v_x_1351_);
v_res_1354_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1350_, v_x_334__boxed_1353_, v_x_1352_);
lean_dec(v_x_1352_);
lean_dec_ref(v_x_1350_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
uint64_t v___y_1359_; 
if (lean_obj_tag(v_x_1357_) == 0)
{
uint64_t v___x_1362_; 
v___x_1362_ = 1723ULL;
v___y_1359_ = v___x_1362_;
goto v___jp_1358_;
}
else
{
uint64_t v_hash_1363_; 
v_hash_1363_ = lean_ctor_get_uint64(v_x_1357_, sizeof(void*)*2);
v___y_1359_ = v_hash_1363_;
goto v___jp_1358_;
}
v___jp_1358_:
{
size_t v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = lean_uint64_to_usize(v___y_1359_);
v___x_1361_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1356_, v___x_1360_, v_x_1357_);
return v___x_1361_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1356_ = stack[0].m_obj;
lean_object* v_x_1357_ = stack[1].m_obj;
uint8_t v_res_1364_;
v_res_1364_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1356_, v_x_1357_);
stack->m_num = v_res_1364_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1365_, lean_object* v_x_1366_){
_start:
{
uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_res_1367_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1365_, v_x_1366_);
lean_dec(v_x_1366_);
lean_dec_ref(v_x_1365_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_env_1374_; lean_object* v___x_1375_; lean_object* v_asyncMode_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1372_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1373_ = lean_st_ref_get(v_a_1370_);
v_env_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc_ref(v_env_1374_);
lean_dec(v___x_1373_);
v___x_1375_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1376_ = lean_ctor_get(v___x_1375_, 2);
v___x_1377_ = lean_box(0);
v___x_1378_ = 0;
v___x_1379_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1372_, v___x_1375_, v_env_1374_, v_asyncMode_1376_, v___x_1377_, v___x_1378_);
v___x_1380_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1379_, v_thmName_1369_);
lean_dec(v___x_1379_);
v___x_1381_ = lean_box(v___x_1380_);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT void l_Lean_Meta_isEqnThm___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmName_1369_ = stack[0].m_obj;
lean_object* v_a_1370_ = stack[1].m_obj;
lean_object* v_res_1383_;
v_res_1383_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1369_, v_a_1370_);
stack->m_obj
 = v_res_1383_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec(v_thmName_1384_);
return v_res_1387_;
}
}
lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1388_, v_a_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT void l_Lean_Meta_isEqnThm_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmName_1388_ = stack[0].m_obj;
lean_object* v_a_1389_ = stack[1].m_obj;
lean_object* v_a_1390_ = stack[2].m_obj;
lean_object* v_res_1393_;
v_res_1393_ = l_Lean_Meta_isEqnThm(v_thmName_1388_, v_a_1389_, v_a_1390_);
stack->m_obj
 = v_res_1393_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_isEqnThm(v_thmName_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_thmName_1394_);
return v_res_1398_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1400_, v_x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1400_ = stack[1].m_obj;
lean_object* v_x_1401_ = stack[2].m_obj;
uint8_t v_res_1403_;
v_res_1403_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_box(0), v_x_1400_, v_x_1401_);
stack->m_num = v_res_1403_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_res_1407_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1404_, v_x_1405_, v_x_1406_);
lean_dec(v_x_1406_);
lean_dec_ref(v_x_1405_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1409_, lean_object* v_x_1410_, size_t v_x_1411_, lean_object* v_x_1412_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1410_, v_x_1411_, v_x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1410_ = stack[1].m_obj;
size_t v_x_1411_ = stack[2].m_num;
lean_object* v_x_1412_ = stack[3].m_obj;
uint8_t v_res_1414_;
v_res_1414_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_box(0), v_x_1410_, v_x_1411_, v_x_1412_);
stack->m_num = v_res_1414_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
size_t v_x_474__boxed_1419_; uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_x_474__boxed_1419_ = lean_unbox_usize(v_x_1417_);
lean_dec(v_x_1417_);
v_res_1420_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1415_, v_x_1416_, v_x_474__boxed_1419_, v_x_1418_);
lean_dec(v_x_1418_);
lean_dec_ref(v_x_1416_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1422_, lean_object* v_keys_1423_, lean_object* v_vals_1424_, lean_object* v_heq_1425_, lean_object* v_i_1426_, lean_object* v_k_1427_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1423_, v_i_1426_, v_k_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1423_ = stack[1].m_obj;
lean_object* v_vals_1424_ = stack[2].m_obj;
lean_object* v_i_1426_ = stack[4].m_obj;
lean_object* v_k_1427_ = stack[5].m_obj;
uint8_t v_res_1429_;
v_res_1429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_box(0), v_keys_1423_, v_vals_1424_, lean_box(0), v_i_1426_, v_k_1427_);
stack->m_num = v_res_1429_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_keys_1431_, lean_object* v_vals_1432_, lean_object* v_heq_1433_, lean_object* v_i_1434_, lean_object* v_k_1435_){
_start:
{
uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_res_1436_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1430_, v_keys_1431_, v_vals_1432_, v_heq_1433_, v_i_1434_, v_k_1435_);
lean_dec(v_k_1435_);
lean_dec_ref(v_vals_1432_);
lean_dec_ref(v_keys_1431_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1438_, lean_object* v_msg_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_panic_fn_borrowed(v_x1_1438_, v_msg_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1441_, lean_object* v_msg_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1441_, v_msg_1442_);
lean_dec_ref(v_x1_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
lean_object* v_ks_1448_; lean_object* v_vs_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1473_; 
v_ks_1448_ = lean_ctor_get(v_x_1444_, 0);
v_vs_1449_ = lean_ctor_get(v_x_1444_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_x_1444_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1451_ = v_x_1444_;
v_isShared_1452_ = v_isSharedCheck_1473_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_vs_1449_);
lean_inc(v_ks_1448_);
lean_dec(v_x_1444_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1473_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_array_get_size(v_ks_1448_);
v___x_1454_ = lean_nat_dec_lt(v_x_1445_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_x_1445_);
v___x_1455_ = lean_array_push(v_ks_1448_, v_x_1446_);
v___x_1456_ = lean_array_push(v_vs_1449_, v_x_1447_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1456_);
lean_ctor_set(v___x_1451_, 0, v___x_1455_);
v___x_1458_ = v___x_1451_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v_k_x27_1460_; uint8_t v___x_1461_; 
v_k_x27_1460_ = lean_array_fget_borrowed(v_ks_1448_, v_x_1445_);
v___x_1461_ = lean_name_eq(v_x_1446_, v_k_x27_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1463_; 
if (v_isShared_1452_ == 0)
{
v___x_1463_ = v___x_1451_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_ks_1448_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_vs_1449_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_x_1445_, v___x_1464_);
lean_dec(v_x_1445_);
v_x_1444_ = v___x_1463_;
v_x_1445_ = v___x_1465_;
goto _start;
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1468_ = lean_array_fset(v_ks_1448_, v_x_1445_, v_x_1446_);
v___x_1469_ = lean_array_fset(v_vs_1449_, v_x_1445_, v_x_1447_);
lean_dec(v_x_1445_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1469_);
lean_ctor_set(v___x_1451_, 0, v___x_1468_);
v___x_1471_ = v___x_1451_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1474_, lean_object* v_k_1475_, lean_object* v_v_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1474_, v___x_1477_, v_k_1475_, v_v_1476_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1479_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1480_, size_t v_x_1481_, size_t v_x_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
if (lean_obj_tag(v_x_1480_) == 0)
{
lean_object* v_es_1485_; size_t v___x_1486_; size_t v___x_1487_; lean_object* v_j_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_es_1485_ = lean_ctor_get(v_x_1480_, 0);
v___x_1486_ = ((size_t)31ULL);
v___x_1487_ = lean_usize_land(v_x_1481_, v___x_1486_);
v_j_1488_ = lean_usize_to_nat(v___x_1487_);
v___x_1489_ = lean_array_get_size(v_es_1485_);
v___x_1490_ = lean_nat_dec_lt(v_j_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_dec(v_j_1488_);
lean_dec(v_x_1484_);
lean_dec(v_x_1483_);
return v_x_1480_;
}
else
{
lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1529_; 
lean_inc_ref(v_es_1485_);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_x_1480_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_x_1480_, 0);
lean_dec(v_unused_1530_);
v___x_1492_ = v_x_1480_;
v_isShared_1493_ = v_isSharedCheck_1529_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v_x_1480_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1529_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_v_1494_; lean_object* v___x_1495_; lean_object* v_xs_x27_1496_; lean_object* v___y_1498_; 
v_v_1494_ = lean_array_fget(v_es_1485_, v_j_1488_);
v___x_1495_ = lean_box(0);
v_xs_x27_1496_ = lean_array_fset(v_es_1485_, v_j_1488_, v___x_1495_);
switch(lean_obj_tag(v_v_1494_))
{
case 0:
{
lean_object* v_key_1503_; lean_object* v_val_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
v_key_1503_ = lean_ctor_get(v_v_1494_, 0);
v_val_1504_ = lean_ctor_get(v_v_1494_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_v_1494_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1506_ = v_v_1494_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_val_1504_);
lean_inc(v_key_1503_);
lean_dec(v_v_1494_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_name_eq(v_x_1483_, v_key_1503_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_del_object(v___x_1506_);
v___x_1509_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1503_, v_val_1504_, v_x_1483_, v_x_1484_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
v___y_1498_ = v___x_1510_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1512_; 
lean_dec(v_val_1504_);
lean_dec(v_key_1503_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v_x_1484_);
lean_ctor_set(v___x_1506_, 0, v_x_1483_);
v___x_1512_ = v___x_1506_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_x_1483_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_x_1484_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
v___y_1498_ = v___x_1512_;
goto v___jp_1497_;
}
}
}
}
case 1:
{
lean_object* v_node_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1527_; 
v_node_1515_ = lean_ctor_get(v_v_1494_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_v_1494_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1517_ = v_v_1494_;
v_isShared_1518_ = v_isSharedCheck_1527_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_node_1515_);
lean_dec(v_v_1494_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1527_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
size_t v___x_1519_; size_t v___x_1520_; size_t v___x_1521_; size_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1519_ = ((size_t)5ULL);
v___x_1520_ = lean_usize_shift_right(v_x_1481_, v___x_1519_);
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_x_1482_, v___x_1521_);
v___x_1523_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1515_, v___x_1520_, v___x_1522_, v_x_1483_, v_x_1484_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1523_);
v___x_1525_ = v___x_1517_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
v___y_1498_ = v___x_1525_;
goto v___jp_1497_;
}
}
}
default: 
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_x_1483_);
lean_ctor_set(v___x_1528_, 1, v_x_1484_);
v___y_1498_ = v___x_1528_;
goto v___jp_1497_;
}
}
v___jp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_array_fset(v_xs_x27_1496_, v_j_1488_, v___y_1498_);
lean_dec(v_j_1488_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1499_);
v___x_1501_ = v___x_1492_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
else
{
lean_object* v_ks_1531_; lean_object* v_vs_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1550_; 
v_ks_1531_ = lean_ctor_get(v_x_1480_, 0);
v_vs_1532_ = lean_ctor_get(v_x_1480_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_x_1480_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1534_ = v_x_1480_;
v_isShared_1535_ = v_isSharedCheck_1550_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_vs_1532_);
lean_inc(v_ks_1531_);
lean_dec(v_x_1480_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1550_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_ks_1531_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_vs_1532_);
v___x_1537_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v_newNode_1538_; size_t v___x_1539_; uint8_t v___x_1540_; 
v_newNode_1538_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1537_, v_x_1483_, v_x_1484_);
v___x_1539_ = ((size_t)7ULL);
v___x_1540_ = lean_usize_dec_le(v___x_1539_, v_x_1482_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1541_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1538_);
v___x_1542_ = lean_unsigned_to_nat(4u);
v___x_1543_ = lean_nat_dec_lt(v___x_1541_, v___x_1542_);
lean_dec(v___x_1541_);
if (v___x_1543_ == 0)
{
lean_object* v_ks_1544_; lean_object* v_vs_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_ks_1544_ = lean_ctor_get(v_newNode_1538_, 0);
lean_inc_ref(v_ks_1544_);
v_vs_1545_ = lean_ctor_get(v_newNode_1538_, 1);
lean_inc_ref(v_vs_1545_);
lean_dec_ref(v_newNode_1538_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1482_, v_ks_1544_, v_vs_1545_, v___x_1546_, v___x_1547_);
lean_dec_ref(v_vs_1545_);
lean_dec_ref(v_ks_1544_);
return v___x_1548_;
}
else
{
return v_newNode_1538_;
}
}
else
{
return v_newNode_1538_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1480_ = stack[0].m_obj;
size_t v_x_1481_ = stack[1].m_num;
size_t v_x_1482_ = stack[2].m_num;
lean_object* v_x_1483_ = stack[3].m_obj;
lean_object* v_x_1484_ = stack[4].m_obj;
lean_object* v_res_1551_;
v_res_1551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1480_, v_x_1481_, v_x_1482_, v_x_1483_, v_x_1484_);
stack->m_obj
 = v_res_1551_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1552_, lean_object* v_keys_1553_, lean_object* v_vals_1554_, lean_object* v_i_1555_, lean_object* v_entries_1556_){
_start:
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = lean_array_get_size(v_keys_1553_);
v___x_1558_ = lean_nat_dec_lt(v_i_1555_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec(v_i_1555_);
return v_entries_1556_;
}
else
{
lean_object* v_k_1559_; lean_object* v_v_1560_; uint64_t v___y_1562_; 
v_k_1559_ = lean_array_fget_borrowed(v_keys_1553_, v_i_1555_);
v_v_1560_ = lean_array_fget_borrowed(v_vals_1554_, v_i_1555_);
if (lean_obj_tag(v_k_1559_) == 0)
{
uint64_t v___x_1573_; 
v___x_1573_ = 1723ULL;
v___y_1562_ = v___x_1573_;
goto v___jp_1561_;
}
else
{
uint64_t v_hash_1574_; 
v_hash_1574_ = lean_ctor_get_uint64(v_k_1559_, sizeof(void*)*2);
v___y_1562_ = v_hash_1574_;
goto v___jp_1561_;
}
v___jp_1561_:
{
size_t v_h_1563_; size_t v___x_1564_; lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; size_t v_h_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_h_1563_ = lean_uint64_to_usize(v___y_1562_);
v___x_1564_ = ((size_t)5ULL);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_sub(v_depth_1552_, v___x_1566_);
v___x_1568_ = lean_usize_mul(v___x_1564_, v___x_1567_);
v_h_1569_ = lean_usize_shift_right(v_h_1563_, v___x_1568_);
v___x_1570_ = lean_nat_add(v_i_1555_, v___x_1565_);
lean_dec(v_i_1555_);
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
v___x_1571_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1556_, v_h_1569_, v_depth_1552_, v_k_1559_, v_v_1560_);
v_i_1555_ = v___x_1570_;
v_entries_1556_ = v___x_1571_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1552_ = stack[0].m_num;
lean_object* v_keys_1553_ = stack[1].m_obj;
lean_object* v_vals_1554_ = stack[2].m_obj;
lean_object* v_i_1555_ = stack[3].m_obj;
lean_object* v_entries_1556_ = stack[4].m_obj;
lean_object* v_res_1575_;
v_res_1575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1552_, v_keys_1553_, v_vals_1554_, v_i_1555_, v_entries_1556_);
stack->m_obj
 = v_res_1575_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1576_, lean_object* v_keys_1577_, lean_object* v_vals_1578_, lean_object* v_i_1579_, lean_object* v_entries_1580_){
_start:
{
size_t v_depth_boxed_1581_; lean_object* v_res_1582_; 
v_depth_boxed_1581_ = lean_unbox_usize(v_depth_1576_);
lean_dec(v_depth_1576_);
v_res_1582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1581_, v_keys_1577_, v_vals_1578_, v_i_1579_, v_entries_1580_);
lean_dec_ref(v_vals_1578_);
lean_dec_ref(v_keys_1577_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
size_t v_x_943__boxed_1588_; size_t v_x_944__boxed_1589_; lean_object* v_res_1590_; 
v_x_943__boxed_1588_ = lean_unbox_usize(v_x_1584_);
lean_dec(v_x_1584_);
v_x_944__boxed_1589_ = lean_unbox_usize(v_x_1585_);
lean_dec(v_x_1585_);
v_res_1590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1583_, v_x_943__boxed_1588_, v_x_944__boxed_1589_, v_x_1586_, v_x_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
uint64_t v___y_1595_; 
if (lean_obj_tag(v_x_1592_) == 0)
{
uint64_t v___x_1599_; 
v___x_1599_ = 1723ULL;
v___y_1595_ = v___x_1599_;
goto v___jp_1594_;
}
else
{
uint64_t v_hash_1600_; 
v_hash_1600_ = lean_ctor_get_uint64(v_x_1592_, sizeof(void*)*2);
v___y_1595_ = v_hash_1600_;
goto v___jp_1594_;
}
v___jp_1594_:
{
size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_uint64_to_usize(v___y_1595_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1591_, v___x_1596_, v___x_1597_, v_x_1592_, v_x_1593_);
return v___x_1598_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1606_, lean_object* v_as_1607_, size_t v_i_1608_, size_t v_stop_1609_, lean_object* v_b_1610_){
_start:
{
lean_object* v___y_1612_; uint8_t v___x_1616_; 
v___x_1616_ = lean_usize_dec_eq(v_i_1608_, v_stop_1609_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_array_uget_borrowed(v_as_1607_, v_i_1608_);
v___x_1618_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1610_, v___x_1617_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v___x_1619_; 
lean_inc(v_declName_1606_);
lean_inc(v___x_1617_);
v___x_1619_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1610_, v___x_1617_, v_declName_1606_);
v___y_1612_ = v___x_1619_;
goto v___jp_1611_;
}
else
{
lean_object* v_val_1620_; uint8_t v___x_1621_; 
v_val_1620_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1621_ = lean_name_eq(v_val_1620_, v_declName_1606_);
if (v___x_1621_ == 0)
{
uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1622_ = 1;
v___x_1623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1625_ = lean_unsigned_to_nat(231u);
v___x_1626_ = lean_unsigned_to_nat(10u);
v___x_1627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1617_);
v___x_1628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1617_, v___x_1622_);
v___x_1629_ = lean_string_append(v___x_1627_, v___x_1628_);
lean_dec_ref(v___x_1628_);
v___x_1630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1631_ = lean_string_append(v___x_1629_, v___x_1630_);
v___x_1632_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1620_, v___x_1622_);
v___x_1633_ = lean_string_append(v___x_1631_, v___x_1632_);
lean_dec_ref(v___x_1632_);
v___x_1634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1635_ = lean_string_append(v___x_1633_, v___x_1634_);
v___x_1636_ = l_mkPanicMessageWithDecl(v___x_1623_, v___x_1624_, v___x_1625_, v___x_1626_, v___x_1635_);
lean_dec_ref(v___x_1635_);
v___x_1637_ = lean_panic_fn_borrowed(v_b_1610_, v___x_1636_);
lean_dec_ref(v_b_1610_);
v___y_1612_ = v___x_1637_;
goto v___jp_1611_;
}
else
{
lean_dec(v_val_1620_);
v___y_1612_ = v_b_1610_;
goto v___jp_1611_;
}
}
}
else
{
lean_dec(v_declName_1606_);
return v_b_1610_;
}
v___jp_1611_:
{
size_t v___x_1613_; size_t v___x_1614_; 
v___x_1613_ = ((size_t)1ULL);
v___x_1614_ = lean_usize_add(v_i_1608_, v___x_1613_);
v_i_1608_ = v___x_1614_;
v_b_1610_ = v___y_1612_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1606_ = stack[0].m_obj;
lean_object* v_as_1607_ = stack[1].m_obj;
size_t v_i_1608_ = stack[2].m_num;
size_t v_stop_1609_ = stack[3].m_num;
lean_object* v_b_1610_ = stack[4].m_obj;
lean_object* v_res_1638_;
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1606_, v_as_1607_, v_i_1608_, v_stop_1609_, v_b_1610_);
stack->m_obj
 = v_res_1638_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1639_, lean_object* v_as_1640_, lean_object* v_i_1641_, lean_object* v_stop_1642_, lean_object* v_b_1643_){
_start:
{
size_t v_i_boxed_1644_; size_t v_stop_boxed_1645_; lean_object* v_res_1646_; 
v_i_boxed_1644_ = lean_unbox_usize(v_i_1641_);
lean_dec(v_i_1641_);
v_stop_boxed_1645_ = lean_unbox_usize(v_stop_1642_);
lean_dec(v_stop_1642_);
v_res_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1639_, v_as_1640_, v_i_boxed_1644_, v_stop_boxed_1645_, v_b_1643_);
lean_dec_ref(v_as_1640_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1647_, lean_object* v_declName_1648_, lean_object* v_s_1649_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = lean_array_get_size(v_eqThms_1647_);
v___x_1652_ = lean_nat_dec_lt(v___x_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_dec(v_declName_1648_);
return v_s_1649_;
}
else
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_nat_dec_le(v___x_1651_, v___x_1651_);
if (v___x_1653_ == 0)
{
if (v___x_1652_ == 0)
{
lean_dec(v_declName_1648_);
return v_s_1649_;
}
else
{
size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((size_t)0ULL);
v___x_1655_ = lean_usize_of_nat(v___x_1651_);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1648_, v_eqThms_1647_, v___x_1654_, v___x_1655_, v_s_1649_);
return v___x_1656_;
}
}
else
{
size_t v___x_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = ((size_t)0ULL);
v___x_1658_ = lean_usize_of_nat(v___x_1651_);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1648_, v_eqThms_1647_, v___x_1657_, v___x_1658_, v_s_1649_);
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1660_, lean_object* v_declName_1661_, lean_object* v_s_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1660_, v_declName_1661_, v_s_1662_);
lean_dec_ref(v_eqThms_1660_);
return v_res_1663_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1664_, lean_object* v_eqThms_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v_env_1670_; lean_object* v_nextMacroScope_1671_; lean_object* v_ngen_1672_; lean_object* v_auxDeclNGen_1673_; lean_object* v_traceState_1674_; lean_object* v_recordedDeps_1675_; lean_object* v_messages_1676_; lean_object* v_infoState_1677_; lean_object* v_snapshotTasks_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1694_; 
v___f_1668_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1668_, 0, v_eqThms_1665_);
lean_closure_set(v___f_1668_, 1, v_declName_1664_);
v___x_1669_ = lean_st_ref_take(v_a_1666_);
v_env_1670_ = lean_ctor_get(v___x_1669_, 0);
v_nextMacroScope_1671_ = lean_ctor_get(v___x_1669_, 1);
v_ngen_1672_ = lean_ctor_get(v___x_1669_, 2);
v_auxDeclNGen_1673_ = lean_ctor_get(v___x_1669_, 3);
v_traceState_1674_ = lean_ctor_get(v___x_1669_, 4);
v_recordedDeps_1675_ = lean_ctor_get(v___x_1669_, 6);
v_messages_1676_ = lean_ctor_get(v___x_1669_, 7);
v_infoState_1677_ = lean_ctor_get(v___x_1669_, 8);
v_snapshotTasks_1678_ = lean_ctor_get(v___x_1669_, 9);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1669_, 5);
lean_dec(v_unused_1695_);
v___x_1680_ = v___x_1669_;
v_isShared_1681_ = v_isSharedCheck_1694_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_snapshotTasks_1678_);
lean_inc(v_infoState_1677_);
lean_inc(v_messages_1676_);
lean_inc(v_recordedDeps_1675_);
lean_inc(v_traceState_1674_);
lean_inc(v_auxDeclNGen_1673_);
lean_inc(v_ngen_1672_);
lean_inc(v_nextMacroScope_1671_);
lean_inc(v_env_1670_);
lean_dec(v___x_1669_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1694_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v_asyncMode_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1682_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1683_ = lean_ctor_get(v___x_1682_, 2);
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_box(0);
v___x_1686_ = 1;
v___x_1687_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1682_, v_env_1670_, v___f_1668_, v_asyncMode_1683_, v___x_1685_, v___x_1686_);
v___x_1688_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 5, v___x_1688_);
lean_ctor_set(v___x_1680_, 0, v___x_1687_);
v___x_1690_ = v___x_1680_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_nextMacroScope_1671_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_ngen_1672_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_auxDeclNGen_1673_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_traceState_1674_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_recordedDeps_1675_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_messages_1676_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_infoState_1677_);
lean_ctor_set(v_reuseFailAlloc_1693_, 9, v_snapshotTasks_1678_);
v___x_1690_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_st_ref_put(v_a_1666_, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1684_);
return v___x_1692_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1664_ = stack[0].m_obj;
lean_object* v_eqThms_1665_ = stack[1].m_obj;
lean_object* v_a_1666_ = stack[2].m_obj;
lean_object* v_res_1696_;
v_res_1696_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1664_, v_eqThms_1665_, v_a_1666_);
stack->m_obj
 = v_res_1696_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1697_, lean_object* v_eqThms_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1697_, v_eqThms_1698_, v_a_1699_);
lean_dec(v_a_1699_);
return v_res_1701_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1702_, lean_object* v_eqThms_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1702_, v_eqThms_1703_, v_a_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1702_ = stack[0].m_obj;
lean_object* v_eqThms_1703_ = stack[1].m_obj;
lean_object* v_a_1704_ = stack[2].m_obj;
lean_object* v_a_1705_ = stack[3].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1702_, v_eqThms_1703_, v_a_1704_, v_a_1705_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1709_, lean_object* v_eqThms_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1709_, v_eqThms_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1716_, v_x_1717_, v_x_1718_);
return v___x_1719_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1720_, lean_object* v_x_1721_, size_t v_x_1722_, size_t v_x_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1721_, v_x_1722_, v_x_1723_, v_x_1724_, v_x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1721_ = stack[1].m_obj;
size_t v_x_1722_ = stack[2].m_num;
size_t v_x_1723_ = stack[3].m_num;
lean_object* v_x_1724_ = stack[4].m_obj;
lean_object* v_x_1725_ = stack[5].m_obj;
lean_object* v_res_1727_;
v_res_1727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_box(0), v_x_1721_, v_x_1722_, v_x_1723_, v_x_1724_, v_x_1725_);
stack->m_obj
 = v_res_1727_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
size_t v_x_1429__boxed_1734_; size_t v_x_1430__boxed_1735_; lean_object* v_res_1736_; 
v_x_1429__boxed_1734_ = lean_unbox_usize(v_x_1730_);
lean_dec(v_x_1730_);
v_x_1430__boxed_1735_ = lean_unbox_usize(v_x_1731_);
lean_dec(v_x_1731_);
v_res_1736_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1728_, v_x_1729_, v_x_1429__boxed_1734_, v_x_1430__boxed_1735_, v_x_1732_, v_x_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1737_, lean_object* v_n_1738_, lean_object* v_k_1739_, lean_object* v_v_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1738_, v_k_1739_, v_v_1740_);
return v___x_1741_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1742_, size_t v_depth_1743_, lean_object* v_keys_1744_, lean_object* v_vals_1745_, lean_object* v_heq_1746_, lean_object* v_i_1747_, lean_object* v_entries_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1743_, v_keys_1744_, v_vals_1745_, v_i_1747_, v_entries_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1743_ = stack[1].m_num;
lean_object* v_keys_1744_ = stack[2].m_obj;
lean_object* v_vals_1745_ = stack[3].m_obj;
lean_object* v_i_1747_ = stack[5].m_obj;
lean_object* v_entries_1748_ = stack[6].m_obj;
lean_object* v_res_1750_;
v_res_1750_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_box(0), v_depth_1743_, v_keys_1744_, v_vals_1745_, lean_box(0), v_i_1747_, v_entries_1748_);
stack->m_obj
 = v_res_1750_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1751_, lean_object* v_depth_1752_, lean_object* v_keys_1753_, lean_object* v_vals_1754_, lean_object* v_heq_1755_, lean_object* v_i_1756_, lean_object* v_entries_1757_){
_start:
{
size_t v_depth_boxed_1758_; lean_object* v_res_1759_; 
v_depth_boxed_1758_ = lean_unbox_usize(v_depth_1752_);
lean_dec(v_depth_1752_);
v_res_1759_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1751_, v_depth_boxed_1758_, v_keys_1753_, v_vals_1754_, v_heq_1755_, v_i_1756_, v_entries_1757_);
lean_dec_ref(v_vals_1754_);
lean_dec_ref(v_keys_1753_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1761_, v_x_1762_, v_x_1763_, v_x_1764_);
return v___x_1765_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1766_, lean_object* v_env_1767_, lean_object* v_idx_1768_, lean_object* v_eqs_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_nextEq_1776_; uint8_t v___x_1777_; 
v___x_1771_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_add(v_idx_1768_, v___x_1772_);
lean_dec(v_idx_1768_);
lean_inc(v___x_1773_);
v___x_1774_ = l_Nat_reprFast(v___x_1773_);
v___x_1775_ = lean_string_append(v___x_1771_, v___x_1774_);
lean_dec_ref(v___x_1774_);
lean_inc(v_declName_1766_);
lean_inc_ref(v_env_1767_);
v_nextEq_1776_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1767_, v_declName_1766_, v___x_1775_);
v___x_1777_ = l_Lean_Environment_containsOnBranch(v_env_1767_, v_nextEq_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_dec(v_nextEq_1776_);
lean_dec(v___x_1773_);
lean_dec_ref(v_env_1767_);
lean_dec(v_declName_1766_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_eqs_1769_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_array_push(v_eqs_1769_, v_nextEq_1776_);
v_idx_1768_ = v___x_1773_;
v_eqs_1769_ = v___x_1779_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1766_ = stack[0].m_obj;
lean_object* v_env_1767_ = stack[1].m_obj;
lean_object* v_idx_1768_ = stack[2].m_obj;
lean_object* v_eqs_1769_ = stack[3].m_obj;
lean_object* v_res_1781_;
v_res_1781_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1766_, v_env_1767_, v_idx_1768_, v_eqs_1769_);
stack->m_obj
 = v_res_1781_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1782_, lean_object* v_env_1783_, lean_object* v_idx_1784_, lean_object* v_eqs_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1782_, v_env_1783_, v_idx_1784_, v_eqs_1785_);
return v_res_1787_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1788_, lean_object* v_env_1789_, lean_object* v_idx_1790_, lean_object* v_eqs_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1788_, v_env_1789_, v_idx_1790_, v_eqs_1791_);
return v___x_1797_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1788_ = stack[0].m_obj;
lean_object* v_env_1789_ = stack[1].m_obj;
lean_object* v_idx_1790_ = stack[2].m_obj;
lean_object* v_eqs_1791_ = stack[3].m_obj;
lean_object* v_a_1792_ = stack[4].m_obj;
lean_object* v_a_1793_ = stack[5].m_obj;
lean_object* v_a_1794_ = stack[6].m_obj;
lean_object* v_a_1795_ = stack[7].m_obj;
lean_object* v_res_1798_;
v_res_1798_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1788_, v_env_1789_, v_idx_1790_, v_eqs_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
stack->m_obj
 = v_res_1798_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1799_, lean_object* v_env_1800_, lean_object* v_idx_1801_, lean_object* v_eqs_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1799_, v_env_1800_, v_idx_1801_, v_eqs_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
return v_res_1808_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v_env_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1812_ = lean_st_ref_get(v_a_1810_);
v_env_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc_ref_n(v_env_1813_, 3);
lean_dec(v___x_1812_);
v___x_1814_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1809_);
v___x_1815_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1813_, v_declName_1809_, v___x_1814_);
v___x_1816_ = 1;
lean_inc(v___x_1815_);
v___x_1817_ = l_Lean_Environment_contains(v_env_1813_, v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v___x_1815_);
lean_dec_ref(v_env_1813_);
lean_dec(v_declName_1809_);
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_mk_empty_array_with_capacity(v___x_1820_);
v___x_1822_ = lean_array_push(v___x_1821_, v___x_1815_);
lean_inc(v_declName_1809_);
v___x_1823_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1809_, v_env_1813_, v___x_1820_, v___x_1822_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1833_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_n(v_a_1824_, 2);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1825_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1809_, v_a_1824_, v_a_1810_);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v___x_1825_, 0);
lean_dec(v_unused_1834_);
v___x_1827_ = v___x_1825_;
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v___x_1825_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_a_1824_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1829_);
v___x_1831_ = v___x_1827_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_declName_1809_);
v_a_1835_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1823_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1823_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1809_ = stack[0].m_obj;
lean_object* v_a_1810_ = stack[1].m_obj;
lean_object* v_res_1843_;
v_res_1843_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1809_, v_a_1810_);
stack->m_obj
 = v_res_1843_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1844_, v_a_1845_);
lean_dec(v_a_1845_);
return v_res_1847_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1848_, v_a_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1848_ = stack[0].m_obj;
lean_object* v_a_1849_ = stack[1].m_obj;
lean_object* v_a_1850_ = stack[2].m_obj;
lean_object* v_a_1851_ = stack[3].m_obj;
lean_object* v_a_1852_ = stack[4].m_obj;
lean_object* v_res_1855_;
v_res_1855_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
stack->m_obj
 = v_res_1855_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
return v_res_1862_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1863_, lean_object* v_localInsts_1864_, lean_object* v_x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1863_, v_localInsts_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1871_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1871_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1863_ = stack[0].m_obj;
lean_object* v_localInsts_1864_ = stack[1].m_obj;
lean_object* v_x_1865_ = stack[2].m_obj;
lean_object* v___y_1866_ = stack[3].m_obj;
lean_object* v___y_1867_ = stack[4].m_obj;
lean_object* v___y_1868_ = stack[5].m_obj;
lean_object* v___y_1869_ = stack[6].m_obj;
lean_object* v_res_1888_;
v_res_1888_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1863_, v_localInsts_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
stack->m_obj
 = v_res_1888_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1889_, lean_object* v_localInsts_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1889_, v_localInsts_1890_, v_x_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1898_, lean_object* v_lctx_1899_, lean_object* v_localInsts_1900_, lean_object* v_x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1899_, v_localInsts_1900_, v_x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1899_ = stack[1].m_obj;
lean_object* v_localInsts_1900_ = stack[2].m_obj;
lean_object* v_x_1901_ = stack[3].m_obj;
lean_object* v___y_1902_ = stack[4].m_obj;
lean_object* v___y_1903_ = stack[5].m_obj;
lean_object* v___y_1904_ = stack[6].m_obj;
lean_object* v___y_1905_ = stack[7].m_obj;
lean_object* v_res_1908_;
v_res_1908_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_box(0), v_lctx_1899_, v_localInsts_1900_, v_x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
stack->m_obj
 = v_res_1908_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1909_, lean_object* v_lctx_1910_, lean_object* v_localInsts_1911_, lean_object* v_x_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1909_, v_lctx_1910_, v_localInsts_1911_, v_x_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1918_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1922_, lean_object* v_as_x27_1923_, lean_object* v_b_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
if (lean_obj_tag(v_as_x27_1923_) == 0)
{
lean_object* v___x_1930_; 
lean_dec(v_declName_1922_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_b_1924_);
return v___x_1930_;
}
else
{
lean_object* v_head_1931_; lean_object* v_tail_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec_ref(v_b_1924_);
v_head_1931_ = lean_ctor_get(v_as_x27_1923_, 0);
v_tail_1932_ = lean_ctor_get(v_as_x27_1923_, 1);
v___x_1933_ = lean_box(0);
v___x_1934_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1931_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v_declName_1922_);
v___x_1935_ = lean_apply_6(v_head_1931_, v_declName_1922_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, lean_box(0));
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
if (lean_obj_tag(v_a_1936_) == 1)
{
lean_object* v_val_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1947_; 
v_val_1937_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_val_1937_);
v___x_1938_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1922_, v_val_1937_, v___y_1928_);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v___x_1938_, 0);
lean_dec(v_unused_1948_);
v___x_1940_ = v___x_1938_;
v_isShared_1941_ = v_isSharedCheck_1947_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v___x_1938_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1947_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_a_1936_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1933_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1943_);
v___x_1945_ = v___x_1940_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_dec(v_a_1936_);
v_as_x27_1923_ = v_tail_1932_;
v_b_1924_ = v___x_1934_;
goto _start;
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_declName_1922_);
v_a_1950_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1935_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1935_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1922_ = stack[0].m_obj;
lean_object* v_as_x27_1923_ = stack[1].m_obj;
lean_object* v_b_1924_ = stack[2].m_obj;
lean_object* v___y_1925_ = stack[3].m_obj;
lean_object* v___y_1926_ = stack[4].m_obj;
lean_object* v___y_1927_ = stack[5].m_obj;
lean_object* v___y_1928_ = stack[6].m_obj;
lean_object* v_res_1958_;
v_res_1958_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1922_, v_as_x27_1923_, v_b_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
stack->m_obj
 = v_res_1958_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1959_, lean_object* v_as_x27_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1959_, v_as_x27_1960_, v_b_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_as_x27_1960_);
return v_res_1967_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
lean_inc(v_declName_1968_);
v___x_1974_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2012_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2012_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2012_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
lean_dec(v_declName_1968_);
v___x_1980_ = lean_box(0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1980_);
v___x_1982_ = v___x_1977_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
else
{
lean_object* v___x_1984_; 
lean_del_object(v___x_1977_);
lean_inc(v_declName_1968_);
v___x_1984_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1968_, v___y_1972_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
if (lean_obj_tag(v_a_1985_) == 1)
{
lean_dec(v_declName_1968_);
return v___x_1984_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1987_ = lean_st_ref_get(v___x_1986_);
v___x_1988_ = lean_box(0);
v___x_1989_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1990_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1968_, v___x_1987_, v___x_1989_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___x_1987_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2003_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2003_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2003_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_fst_1995_; 
v_fst_1995_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_fst_1995_);
lean_dec(v_a_1991_);
if (lean_obj_tag(v_fst_1995_) == 0)
{
lean_object* v___x_1997_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1988_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1988_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
else
{
lean_object* v_val_1999_; lean_object* v___x_2001_; 
v_val_1999_ = lean_ctor_get(v_fst_1995_, 0);
lean_inc(v_val_1999_);
lean_dec_ref_known(v_fst_1995_, 1);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v_val_1999_);
v___x_2001_ = v___x_1993_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_val_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_a_2004_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1990_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1990_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
else
{
lean_dec(v_declName_1968_);
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_declName_1968_);
v_a_2013_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1974_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1974_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1968_ = stack[0].m_obj;
lean_object* v___y_1969_ = stack[1].m_obj;
lean_object* v___y_1970_ = stack[2].m_obj;
lean_object* v___y_1971_ = stack[3].m_obj;
lean_object* v___y_1972_ = stack[4].m_obj;
lean_object* v_res_2021_;
v_res_2021_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
stack->m_obj
 = v_res_2021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2031_ = lean_box(1);
v___x_2032_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_2033_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_2034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v___x_2032_);
lean_ctor_set(v___x_2034_, 2, v___x_2031_);
return v___x_2034_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___f_2043_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2043_, 0, v_declName_2037_);
v___x_2044_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2045_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2046_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2044_, v___x_2045_, v___f_2043_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2046_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2037_ = stack[0].m_obj;
lean_object* v_a_2038_ = stack[1].m_obj;
lean_object* v_a_2039_ = stack[2].m_obj;
lean_object* v_a_2040_ = stack[3].m_obj;
lean_object* v_a_2041_ = stack[4].m_obj;
lean_object* v_res_2047_;
v_res_2047_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
stack->m_obj
 = v_res_2047_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
return v_res_2054_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_2055_, lean_object* v_as_2056_, lean_object* v_as_x27_2057_, lean_object* v_b_2058_, lean_object* v_a_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_2055_, v_as_x27_2057_, v_b_2058_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2055_ = stack[0].m_obj;
lean_object* v_as_2056_ = stack[1].m_obj;
lean_object* v_as_x27_2057_ = stack[2].m_obj;
lean_object* v_b_2058_ = stack[3].m_obj;
lean_object* v___y_2060_ = stack[5].m_obj;
lean_object* v___y_2061_ = stack[6].m_obj;
lean_object* v___y_2062_ = stack[7].m_obj;
lean_object* v___y_2063_ = stack[8].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_2055_, v_as_2056_, v_as_x27_2057_, v_b_2058_, lean_box(0), v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_2067_, lean_object* v_as_2068_, lean_object* v_as_x27_2069_, lean_object* v_b_2070_, lean_object* v_a_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_2067_, v_as_2068_, v_as_x27_2069_, v_b_2070_, v_a_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v_as_x27_2069_);
lean_dec(v_as_2068_);
return v_res_2077_;
}
}
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2084_ = lean_unsigned_to_nat(32u);
v___x_2085_ = lean_mk_empty_array_with_capacity(v___x_2084_);
lean_dec_ref(v___x_2085_);
v___x_2086_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_2078_);
v___x_2088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_2088_, 0, v_declName_2078_);
v___x_2089_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_2089_, 0, lean_box(0));
lean_closure_set(v___x_2089_, 1, v_declName_2078_);
lean_closure_set(v___x_2089_, 2, v___x_2088_);
v___x_2090_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2086_, v___x_2087_, v___x_2089_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2090_;
}
}
LEAN_EXPORT void l_Lean_Meta_getEqnsFor_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2078_ = stack[0].m_obj;
lean_object* v_a_2079_ = stack[1].m_obj;
lean_object* v_a_2080_ = stack[2].m_obj;
lean_object* v_a_2081_ = stack[3].m_obj;
lean_object* v_a_2082_ = stack[4].m_obj;
lean_object* v_res_2091_;
v_res_2091_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
stack->m_obj
 = v_res_2091_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
return v_res_2098_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_2099_, lean_object* v_opt_2100_){
_start:
{
lean_object* v_name_2101_; lean_object* v_defValue_2102_; lean_object* v_map_2103_; lean_object* v___x_2104_; 
v_name_2101_ = lean_ctor_get(v_opt_2100_, 0);
v_defValue_2102_ = lean_ctor_get(v_opt_2100_, 1);
v_map_2103_ = lean_ctor_get(v_opts_2099_, 0);
v___x_2104_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2103_, v_name_2101_);
if (lean_obj_tag(v___x_2104_) == 0)
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_unbox(v_defValue_2102_);
return v___x_2105_;
}
else
{
lean_object* v_val_2106_; 
v_val_2106_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_val_2106_);
lean_dec_ref_known(v___x_2104_, 1);
if (lean_obj_tag(v_val_2106_) == 1)
{
uint8_t v_v_2107_; 
v_v_2107_ = lean_ctor_get_uint8(v_val_2106_, 0);
lean_dec_ref_known(v_val_2106_, 0);
return v_v_2107_;
}
else
{
uint8_t v___x_2108_; 
lean_dec(v_val_2106_);
v___x_2108_ = lean_unbox(v_defValue_2102_);
return v___x_2108_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2099_ = stack[0].m_obj;
lean_object* v_opt_2100_ = stack[1].m_obj;
uint8_t v_res_2109_;
v_res_2109_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2099_, v_opt_2100_);
stack->m_num = v_res_2109_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_2110_, lean_object* v_opt_2111_){
_start:
{
uint8_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2110_, v_opt_2111_);
lean_dec_ref(v_opt_2111_);
lean_dec_ref(v_opts_2110_);
v_r_2113_ = lean_box(v_res_2112_);
return v_r_2113_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2114_, lean_object* v_as_2115_, size_t v_sz_2116_, size_t v_i_2117_, lean_object* v_b_2118_){
_start:
{
lean_object* v_a_2121_; uint8_t v___x_2125_; 
v___x_2125_ = lean_usize_dec_lt(v_i_2117_, v_sz_2116_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_b_2118_);
return v___x_2126_;
}
else
{
lean_object* v_a_2127_; lean_object* v_defValue_2128_; uint8_t v___x_2129_; uint8_t v___y_2143_; uint8_t v___x_2144_; 
v_a_2127_ = lean_array_uget(v_as_2115_, v_i_2117_);
v_defValue_2128_ = lean_ctor_get(v_a_2127_, 1);
v___x_2129_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2114_, v_a_2127_);
v___x_2144_ = lean_unbox(v_defValue_2128_);
if (v___x_2144_ == 0)
{
if (v___x_2129_ == 0)
{
v___y_2143_ = v___x_2125_;
goto v___jp_2142_;
}
else
{
goto v___jp_2130_;
}
}
else
{
v___y_2143_ = v___x_2129_;
goto v___jp_2142_;
}
v___jp_2130_:
{
lean_object* v_name_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2140_; 
v_name_2131_ = lean_ctor_get(v_a_2127_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v_a_2127_, 1);
lean_dec(v_unused_2141_);
v___x_2133_ = v_a_2127_;
v_isShared_2134_ = v_isSharedCheck_2140_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_name_2131_);
lean_dec(v_a_2127_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2140_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2135_, 0, v___x_2129_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2135_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_name_2131_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_array_push(v_b_2118_, v___x_2137_);
v_a_2121_ = v___x_2138_;
goto v___jp_2120_;
}
}
}
v___jp_2142_:
{
if (v___y_2143_ == 0)
{
goto v___jp_2130_;
}
else
{
lean_dec(v_a_2127_);
v_a_2121_ = v_b_2118_;
goto v___jp_2120_;
}
}
}
v___jp_2120_:
{
size_t v___x_2122_; size_t v___x_2123_; 
v___x_2122_ = ((size_t)1ULL);
v___x_2123_ = lean_usize_add(v_i_2117_, v___x_2122_);
v_i_2117_ = v___x_2123_;
v_b_2118_ = v_a_2121_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2114_ = stack[0].m_obj;
lean_object* v_as_2115_ = stack[1].m_obj;
size_t v_sz_2116_ = stack[2].m_num;
size_t v_i_2117_ = stack[3].m_num;
lean_object* v_b_2118_ = stack[4].m_obj;
lean_object* v_res_2145_;
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2114_, v_as_2115_, v_sz_2116_, v_i_2117_, v_b_2118_);
stack->m_obj
 = v_res_2145_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2146_, lean_object* v_as_2147_, lean_object* v_sz_2148_, lean_object* v_i_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_){
_start:
{
size_t v_sz_boxed_2152_; size_t v_i_boxed_2153_; lean_object* v_res_2154_; 
v_sz_boxed_2152_ = lean_unbox_usize(v_sz_2148_);
lean_dec(v_sz_2148_);
v_i_boxed_2153_ = lean_unbox_usize(v_i_2149_);
lean_dec(v_i_2149_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2146_, v_as_2147_, v_sz_boxed_2152_, v_i_boxed_2153_, v_b_2150_);
lean_dec_ref(v_as_2147_);
lean_dec_ref(v___x_2146_);
return v_res_2154_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; lean_object* v_env_2162_; uint8_t v___x_2163_; lean_object* v_env_2164_; lean_object* v___x_2165_; lean_object* v_toCold_2166_; lean_object* v_mctx_2167_; lean_object* v_lctx_2168_; lean_object* v_options_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2161_ = lean_st_ref_get(v___y_2159_);
v_env_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc_ref(v_env_2162_);
lean_dec(v___x_2161_);
v___x_2163_ = 0;
v_env_2164_ = l_Lean_Environment_setRecordingDeps(v_env_2162_, v___x_2163_);
v___x_2165_ = lean_st_ref_get(v___y_2157_);
v_toCold_2166_ = lean_ctor_get(v___y_2158_, 0);
v_mctx_2167_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_ref(v_mctx_2167_);
lean_dec(v___x_2165_);
v_lctx_2168_ = lean_ctor_get(v___y_2156_, 2);
v_options_2169_ = lean_ctor_get(v_toCold_2166_, 2);
lean_inc_ref(v_options_2169_);
lean_inc_ref(v_lctx_2168_);
v___x_2170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2170_, 0, v_env_2164_);
lean_ctor_set(v___x_2170_, 1, v_mctx_2167_);
lean_ctor_set(v___x_2170_, 2, v_lctx_2168_);
lean_ctor_set(v___x_2170_, 3, v_options_2169_);
v___x_2171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v_msgData_2155_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2155_ = stack[0].m_obj;
lean_object* v___y_2156_ = stack[1].m_obj;
lean_object* v___y_2157_ = stack[2].m_obj;
lean_object* v___y_2158_ = stack[3].m_obj;
lean_object* v___y_2159_ = stack[4].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2180_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2181_; double v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_float_of_nat(v___x_2181_);
return v___x_2182_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_ref_2193_; lean_object* v___x_2194_; lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2240_; 
v_ref_2193_ = lean_ctor_get(v___y_2190_, 2);
v___x_2194_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2240_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2240_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v_traceState_2200_; lean_object* v_env_2201_; lean_object* v_nextMacroScope_2202_; lean_object* v_ngen_2203_; lean_object* v_auxDeclNGen_2204_; lean_object* v_cache_2205_; lean_object* v_recordedDeps_2206_; lean_object* v_messages_2207_; lean_object* v_infoState_2208_; lean_object* v_snapshotTasks_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2239_; 
v___x_2199_ = lean_st_ref_take(v___y_2191_);
v_traceState_2200_ = lean_ctor_get(v___x_2199_, 4);
v_env_2201_ = lean_ctor_get(v___x_2199_, 0);
v_nextMacroScope_2202_ = lean_ctor_get(v___x_2199_, 1);
v_ngen_2203_ = lean_ctor_get(v___x_2199_, 2);
v_auxDeclNGen_2204_ = lean_ctor_get(v___x_2199_, 3);
v_cache_2205_ = lean_ctor_get(v___x_2199_, 5);
v_recordedDeps_2206_ = lean_ctor_get(v___x_2199_, 6);
v_messages_2207_ = lean_ctor_get(v___x_2199_, 7);
v_infoState_2208_ = lean_ctor_get(v___x_2199_, 8);
v_snapshotTasks_2209_ = lean_ctor_get(v___x_2199_, 9);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2211_ = v___x_2199_;
v_isShared_2212_ = v_isSharedCheck_2239_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_snapshotTasks_2209_);
lean_inc(v_infoState_2208_);
lean_inc(v_messages_2207_);
lean_inc(v_recordedDeps_2206_);
lean_inc(v_cache_2205_);
lean_inc(v_traceState_2200_);
lean_inc(v_auxDeclNGen_2204_);
lean_inc(v_ngen_2203_);
lean_inc(v_nextMacroScope_2202_);
lean_inc(v_env_2201_);
lean_dec(v___x_2199_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2239_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
uint64_t v_tid_2213_; lean_object* v_traces_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2238_; 
v_tid_2213_ = lean_ctor_get_uint64(v_traceState_2200_, sizeof(void*)*1);
v_traces_2214_ = lean_ctor_get(v_traceState_2200_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_traceState_2200_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2216_ = v_traceState_2200_;
v_isShared_2217_ = v_isSharedCheck_2238_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_traces_2214_);
lean_dec(v_traceState_2200_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2238_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; double v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2221_ = 0;
v___x_2222_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2223_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2223_, 0, v_cls_2186_);
lean_ctor_set(v___x_2223_, 1, v___x_2219_);
lean_ctor_set(v___x_2223_, 2, v___x_2222_);
lean_ctor_set_float(v___x_2223_, sizeof(void*)*3, v___x_2220_);
lean_ctor_set_float(v___x_2223_, sizeof(void*)*3 + 8, v___x_2220_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*3 + 16, v___x_2221_);
v___x_2224_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2225_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v_a_2195_);
lean_ctor_set(v___x_2225_, 2, v___x_2224_);
lean_inc(v_ref_2193_);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_ref_2193_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_PersistentArray_push___redArg(v_traces_2214_, v___x_2226_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2227_);
v___x_2229_ = v___x_2216_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2227_);
lean_ctor_set_uint64(v_reuseFailAlloc_2237_, sizeof(void*)*1, v_tid_2213_);
v___x_2229_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2231_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 4, v___x_2229_);
v___x_2231_ = v___x_2211_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_env_2201_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_nextMacroScope_2202_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_ngen_2203_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_auxDeclNGen_2204_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2236_, 5, v_cache_2205_);
lean_ctor_set(v_reuseFailAlloc_2236_, 6, v_recordedDeps_2206_);
lean_ctor_set(v_reuseFailAlloc_2236_, 7, v_messages_2207_);
lean_ctor_set(v_reuseFailAlloc_2236_, 8, v_infoState_2208_);
lean_ctor_set(v_reuseFailAlloc_2236_, 9, v_snapshotTasks_2209_);
v___x_2231_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_st_ref_put(v___y_2191_, v___x_2231_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2218_);
v___x_2234_ = v___x_2197_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2218_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2186_ = stack[0].m_obj;
lean_object* v_msg_2187_ = stack[1].m_obj;
lean_object* v___y_2188_ = stack[2].m_obj;
lean_object* v___y_2189_ = stack[3].m_obj;
lean_object* v___y_2190_ = stack[4].m_obj;
lean_object* v___y_2191_ = stack[5].m_obj;
lean_object* v_res_2241_;
v_res_2241_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2186_, v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
stack->m_obj
 = v_res_2241_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2242_, lean_object* v_msg_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2242_, v_msg_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2249_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2252_; size_t v_sz_2253_; 
v___x_2252_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2253_ = lean_array_size(v___x_2252_);
return v_sz_2253_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
lean_ctor_set(v___x_2255_, 2, v___x_2254_);
lean_ctor_set(v___x_2255_, 3, v___x_2254_);
lean_ctor_set(v___x_2255_, 4, v___x_2254_);
lean_ctor_set(v___x_2255_, 5, v___x_2254_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2264_ = l_Lean_Name_append(v___x_2263_, v___x_2262_);
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; size_t v_sz_2278_; size_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2274_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2271_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2277_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2278_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2279_ = ((size_t)0ULL);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2274_, v___x_2277_, v_sz_2278_, v___x_2279_, v___x_2276_);
lean_dec_ref(v___x_2274_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2344_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2344_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2344_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___y_2288_; lean_object* v___y_2289_; 
v___x_2285_ = lean_array_get_size(v_a_2281_);
v___x_2286_ = lean_nat_dec_eq(v___x_2285_, v___x_2275_);
if (v___x_2286_ == 0)
{
lean_object* v_toCold_2331_; lean_object* v_options_2332_; uint8_t v_hasTrace_2333_; 
v_toCold_2331_ = lean_ctor_get(v_a_2271_, 0);
v_options_2332_ = lean_ctor_get(v_toCold_2331_, 2);
v_hasTrace_2333_ = lean_ctor_get_uint8(v_options_2332_, sizeof(void*)*1);
if (v_hasTrace_2333_ == 0)
{
v___y_2288_ = v_a_2270_;
v___y_2289_ = v_a_2272_;
goto v___jp_2287_;
}
else
{
lean_object* v_inheritedTraceOptions_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_inheritedTraceOptions_2334_ = lean_ctor_get(v_toCold_2331_, 11);
v___x_2335_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2336_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2334_, v_options_2332_, v___x_2336_);
if (v___x_2337_ == 0)
{
v___y_2288_ = v_a_2270_;
v___y_2289_ = v_a_2272_;
goto v___jp_2287_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2268_);
v___x_2339_ = l_Lean_MessageData_ofName(v_declName_2268_);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2335_, v___x_2340_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_dec_ref_known(v___x_2341_, 1);
v___y_2288_ = v_a_2270_;
v___y_2289_ = v_a_2272_;
goto v___jp_2287_;
}
else
{
lean_del_object(v___x_2283_);
lean_dec(v_a_2281_);
lean_dec(v_declName_2268_);
return v___x_2341_;
}
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_del_object(v___x_2283_);
lean_dec(v_a_2281_);
lean_dec(v_declName_2268_);
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
v___jp_2287_:
{
lean_object* v___x_2290_; lean_object* v_env_2291_; lean_object* v_nextMacroScope_2292_; lean_object* v_ngen_2293_; lean_object* v_auxDeclNGen_2294_; lean_object* v_traceState_2295_; lean_object* v_recordedDeps_2296_; lean_object* v_messages_2297_; lean_object* v_infoState_2298_; lean_object* v_snapshotTasks_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2329_; 
v___x_2290_ = lean_st_ref_take(v___y_2289_);
v_env_2291_ = lean_ctor_get(v___x_2290_, 0);
v_nextMacroScope_2292_ = lean_ctor_get(v___x_2290_, 1);
v_ngen_2293_ = lean_ctor_get(v___x_2290_, 2);
v_auxDeclNGen_2294_ = lean_ctor_get(v___x_2290_, 3);
v_traceState_2295_ = lean_ctor_get(v___x_2290_, 4);
v_recordedDeps_2296_ = lean_ctor_get(v___x_2290_, 6);
v_messages_2297_ = lean_ctor_get(v___x_2290_, 7);
v_infoState_2298_ = lean_ctor_get(v___x_2290_, 8);
v_snapshotTasks_2299_ = lean_ctor_get(v___x_2290_, 9);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2290_, 5);
lean_dec(v_unused_2330_);
v___x_2301_ = v___x_2290_;
v_isShared_2302_ = v_isSharedCheck_2329_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_snapshotTasks_2299_);
lean_inc(v_infoState_2298_);
lean_inc(v_messages_2297_);
lean_inc(v_recordedDeps_2296_);
lean_inc(v_traceState_2295_);
lean_inc(v_auxDeclNGen_2294_);
lean_inc(v_ngen_2293_);
lean_inc(v_nextMacroScope_2292_);
lean_inc(v_env_2291_);
lean_dec(v___x_2290_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2329_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2303_ = l_Lean_Meta_eqnOptionsExt;
v___x_2304_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2303_, v_env_2291_, v_declName_2268_, v_a_2281_, v___x_2286_);
v___x_2305_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 5, v___x_2305_);
lean_ctor_set(v___x_2301_, 0, v___x_2304_);
v___x_2307_ = v___x_2301_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_nextMacroScope_2292_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_ngen_2293_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_auxDeclNGen_2294_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_traceState_2295_);
lean_ctor_set(v_reuseFailAlloc_2328_, 5, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2328_, 6, v_recordedDeps_2296_);
lean_ctor_set(v_reuseFailAlloc_2328_, 7, v_messages_2297_);
lean_ctor_set(v_reuseFailAlloc_2328_, 8, v_infoState_2298_);
lean_ctor_set(v_reuseFailAlloc_2328_, 9, v_snapshotTasks_2299_);
v___x_2307_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_mctx_2310_; lean_object* v_zetaDeltaFVarIds_2311_; lean_object* v_postponed_2312_; lean_object* v_diag_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2326_; 
v___x_2308_ = lean_st_ref_put(v___y_2289_, v___x_2307_);
v___x_2309_ = lean_st_ref_take(v___y_2288_);
v_mctx_2310_ = lean_ctor_get(v___x_2309_, 0);
v_zetaDeltaFVarIds_2311_ = lean_ctor_get(v___x_2309_, 2);
v_postponed_2312_ = lean_ctor_get(v___x_2309_, 3);
v_diag_2313_ = lean_ctor_get(v___x_2309_, 4);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v___x_2309_, 1);
lean_dec(v_unused_2327_);
v___x_2315_ = v___x_2309_;
v_isShared_2316_ = v_isSharedCheck_2326_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_diag_2313_);
lean_inc(v_postponed_2312_);
lean_inc(v_zetaDeltaFVarIds_2311_);
lean_inc(v_mctx_2310_);
lean_dec(v___x_2309_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2326_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v___x_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_mctx_2310_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_zetaDeltaFVarIds_2311_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_postponed_2312_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_diag_2313_);
v___x_2320_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_st_ref_put(v___y_2288_, v___x_2320_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2317_);
v___x_2323_ = v___x_2283_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2317_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
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
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_declName_2268_);
v_a_2345_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2280_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2280_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
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
}
LEAN_EXPORT void l_Lean_Meta_saveEqnAffectingOptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2268_ = stack[0].m_obj;
lean_object* v_a_2269_ = stack[1].m_obj;
lean_object* v_a_2270_ = stack[2].m_obj;
lean_object* v_a_2271_ = stack[3].m_obj;
lean_object* v_a_2272_ = stack[4].m_obj;
lean_object* v_res_2353_;
v_res_2353_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
stack->m_obj
 = v_res_2353_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
return v_res_2360_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2361_, lean_object* v_as_2362_, size_t v_sz_2363_, size_t v_i_2364_, lean_object* v_b_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2361_, v_as_2362_, v_sz_2363_, v_i_2364_, v_b_2365_);
return v___x_2371_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2361_ = stack[0].m_obj;
lean_object* v_as_2362_ = stack[1].m_obj;
size_t v_sz_2363_ = stack[2].m_num;
size_t v_i_2364_ = stack[3].m_num;
lean_object* v_b_2365_ = stack[4].m_obj;
lean_object* v___y_2366_ = stack[5].m_obj;
lean_object* v___y_2367_ = stack[6].m_obj;
lean_object* v___y_2368_ = stack[7].m_obj;
lean_object* v___y_2369_ = stack[8].m_obj;
lean_object* v_res_2372_;
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2361_, v_as_2362_, v_sz_2363_, v_i_2364_, v_b_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
stack->m_obj
 = v_res_2372_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2373_, lean_object* v_as_2374_, lean_object* v_sz_2375_, lean_object* v_i_2376_, lean_object* v_b_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
size_t v_sz_boxed_2383_; size_t v_i_boxed_2384_; lean_object* v_res_2385_; 
v_sz_boxed_2383_ = lean_unbox_usize(v_sz_2375_);
lean_dec(v_sz_2375_);
v_i_boxed_2384_ = lean_unbox_usize(v_i_2376_);
lean_dec(v_i_2376_);
v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2373_, v_as_2374_, v_sz_boxed_2383_, v_i_boxed_2384_, v_b_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v_as_2374_);
lean_dec_ref(v___x_2373_);
return v_res_2385_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_st_mk_ref(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2390_;
v_res_2390_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2390_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2392_;
}
}
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2393_){
_start:
{
uint8_t v___x_2395_; 
v___x_2395_ = l_Lean_initializing();
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_dec_ref(v_f_2393_);
v___x_2396_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2398_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2399_ = lean_st_ref_take(v___x_2398_);
v___x_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2400_, 0, v_f_2393_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = lean_st_ref_put(v___x_2398_, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_registerGetUnfoldEqnFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2393_ = stack[0].m_obj;
lean_object* v_res_2403_;
v_res_2403_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2393_);
stack->m_obj
 = v_res_2403_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2404_);
return v_res_2406_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2410_, lean_object* v_as_x27_2411_, lean_object* v_b_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
if (lean_obj_tag(v_as_x27_2411_) == 0)
{
lean_object* v___x_2418_; 
lean_dec(v_declName_2410_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_b_2412_);
return v___x_2418_;
}
else
{
lean_object* v_head_2419_; lean_object* v_tail_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref(v_b_2412_);
v_head_2419_ = lean_ctor_get(v_as_x27_2411_, 0);
v_tail_2420_ = lean_ctor_get(v_as_x27_2411_, 1);
v___x_2421_ = lean_box(0);
v___x_2422_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2419_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc(v_declName_2410_);
v___x_2423_ = lean_apply_6(v_head_2419_, v_declName_2410_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, lean_box(0));
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2434_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2434_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2434_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
if (lean_obj_tag(v_a_2424_) == 1)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
lean_dec(v_declName_2410_);
v___x_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_a_2424_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2421_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2429_);
v___x_2431_ = v___x_2426_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
else
{
lean_del_object(v___x_2426_);
lean_dec(v_a_2424_);
v_as_x27_2411_ = v_tail_2420_;
v_b_2412_ = v___x_2422_;
goto _start;
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_declName_2410_);
v_a_2435_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2423_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2423_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2410_ = stack[0].m_obj;
lean_object* v_as_x27_2411_ = stack[1].m_obj;
lean_object* v_b_2412_ = stack[2].m_obj;
lean_object* v___y_2413_ = stack[3].m_obj;
lean_object* v___y_2414_ = stack[4].m_obj;
lean_object* v___y_2415_ = stack[5].m_obj;
lean_object* v___y_2416_ = stack[6].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2410_, v_as_x27_2411_, v_b_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2444_, lean_object* v_as_x27_2445_, lean_object* v_b_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2444_, v_as_x27_2445_, v_b_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v_as_x27_2445_);
return v_res_2452_;
}
}
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2453_, lean_object* v_declName_2454_, uint8_t v_nonRec_2455_, lean_object* v___x_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2465_; lean_object* v_env_2466_; uint8_t v___x_2467_; uint8_t v___x_2468_; 
v___x_2465_ = lean_st_ref_get(v___y_2460_);
v_env_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc_ref(v_env_2466_);
lean_dec(v___x_2465_);
v___x_2467_ = 1;
lean_inc(v___x_2453_);
v___x_2468_ = l_Lean_Environment_contains(v_env_2466_, v___x_2453_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
lean_dec(v___x_2453_);
lean_inc(v_declName_2454_);
v___x_2469_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2454_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; uint8_t v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = lean_unbox(v_a_2470_);
lean_dec(v_a_2470_);
if (v___x_2471_ == 0)
{
lean_dec_ref(v___x_2456_);
lean_dec(v_declName_2454_);
goto v___jp_2462_;
}
else
{
lean_object* v___x_2472_; 
lean_inc(v_declName_2454_);
v___x_2472_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2454_, v___y_2460_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; uint8_t v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = lean_unbox(v_a_2473_);
lean_dec(v_a_2473_);
if (v___x_2474_ == 0)
{
if (v_nonRec_2455_ == 0)
{
lean_dec_ref(v___x_2456_);
lean_dec(v_declName_2454_);
goto v___jp_2462_;
}
else
{
lean_object* v___x_2475_; lean_object* v_env_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2475_ = lean_st_ref_get(v___y_2460_);
v_env_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc_ref(v_env_2476_);
lean_dec(v___x_2475_);
lean_inc(v_declName_2454_);
v___x_2477_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2476_, v_declName_2454_, v___x_2456_);
v___x_2478_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2454_, v___x_2477_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v___x_2478_;
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec_ref(v___x_2456_);
v___x_2479_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2480_ = lean_st_ref_get(v___x_2479_);
v___x_2481_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2482_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2454_, v___x_2480_, v___x_2481_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___x_2480_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2492_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_fst_2487_; 
v_fst_2487_ = lean_ctor_get(v_a_2483_, 0);
lean_inc(v_fst_2487_);
lean_dec(v_a_2483_);
if (lean_obj_tag(v_fst_2487_) == 0)
{
lean_del_object(v___x_2485_);
goto v___jp_2462_;
}
else
{
lean_object* v_val_2488_; lean_object* v___x_2490_; 
v_val_2488_ = lean_ctor_get(v_fst_2487_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v_fst_2487_, 1);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v_val_2488_);
v___x_2490_ = v___x_2485_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_val_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v_a_2493_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2482_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2482_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v___x_2456_);
lean_dec(v_declName_2454_);
v_a_2501_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2472_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2472_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v___x_2456_);
lean_dec(v_declName_2454_);
v_a_2509_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2469_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2469_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec_ref(v___x_2456_);
lean_dec(v_declName_2454_);
v___x_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2453_);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
v___jp_2462_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2453_ = stack[0].m_obj;
lean_object* v_declName_2454_ = stack[1].m_obj;
uint8_t v_nonRec_2455_ = stack[2].m_num;
lean_object* v___x_2456_ = stack[3].m_obj;
lean_object* v___y_2457_ = stack[4].m_obj;
lean_object* v___y_2458_ = stack[5].m_obj;
lean_object* v___y_2459_ = stack[6].m_obj;
lean_object* v___y_2460_ = stack[7].m_obj;
lean_object* v_res_2519_;
v_res_2519_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2453_, v_declName_2454_, v_nonRec_2455_, v___x_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
stack->m_obj
 = v_res_2519_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2520_, lean_object* v_declName_2521_, lean_object* v_nonRec_2522_, lean_object* v___x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
uint8_t v_nonRec_boxed_2529_; lean_object* v_res_2530_; 
v_nonRec_boxed_2529_ = lean_unbox(v_nonRec_2522_);
v_res_2530_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2520_, v_declName_2521_, v_nonRec_boxed_2529_, v___x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2530_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_ref_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2547_; 
v_ref_2537_ = lean_ctor_get(v___y_2534_, 2);
v___x_2538_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_inc(v_ref_2537_);
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_ref_2537_);
lean_ctor_set(v___x_2543_, 1, v_a_2539_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2531_ = stack[0].m_obj;
lean_object* v___y_2532_ = stack[1].m_obj;
lean_object* v___y_2533_ = stack[2].m_obj;
lean_object* v___y_2534_ = stack[3].m_obj;
lean_object* v___y_2535_ = stack[4].m_obj;
lean_object* v_res_2548_;
v_res_2548_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
stack->m_obj
 = v_res_2548_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2555_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2556_, uint8_t v_isExporting_2557_, lean_object* v___x_2558_, lean_object* v___y_2559_, lean_object* v___x_2560_, lean_object* v_a_x3f_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v_env_2564_; lean_object* v_nextMacroScope_2565_; lean_object* v_ngen_2566_; lean_object* v_auxDeclNGen_2567_; lean_object* v_traceState_2568_; lean_object* v_recordedDeps_2569_; lean_object* v_messages_2570_; lean_object* v_infoState_2571_; lean_object* v_snapshotTasks_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2597_; 
v___x_2563_ = lean_st_ref_take(v___y_2556_);
v_env_2564_ = lean_ctor_get(v___x_2563_, 0);
v_nextMacroScope_2565_ = lean_ctor_get(v___x_2563_, 1);
v_ngen_2566_ = lean_ctor_get(v___x_2563_, 2);
v_auxDeclNGen_2567_ = lean_ctor_get(v___x_2563_, 3);
v_traceState_2568_ = lean_ctor_get(v___x_2563_, 4);
v_recordedDeps_2569_ = lean_ctor_get(v___x_2563_, 6);
v_messages_2570_ = lean_ctor_get(v___x_2563_, 7);
v_infoState_2571_ = lean_ctor_get(v___x_2563_, 8);
v_snapshotTasks_2572_ = lean_ctor_get(v___x_2563_, 9);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2563_, 5);
lean_dec(v_unused_2598_);
v___x_2574_ = v___x_2563_;
v_isShared_2575_ = v_isSharedCheck_2597_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snapshotTasks_2572_);
lean_inc(v_infoState_2571_);
lean_inc(v_messages_2570_);
lean_inc(v_recordedDeps_2569_);
lean_inc(v_traceState_2568_);
lean_inc(v_auxDeclNGen_2567_);
lean_inc(v_ngen_2566_);
lean_inc(v_nextMacroScope_2565_);
lean_inc(v_env_2564_);
lean_dec(v___x_2563_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2597_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = l_Lean_Environment_setExporting(v_env_2564_, v_isExporting_2557_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 5, v___x_2558_);
lean_ctor_set(v___x_2574_, 0, v___x_2576_);
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_nextMacroScope_2565_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_ngen_2566_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_auxDeclNGen_2567_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_traceState_2568_);
lean_ctor_set(v_reuseFailAlloc_2596_, 5, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2596_, 6, v_recordedDeps_2569_);
lean_ctor_set(v_reuseFailAlloc_2596_, 7, v_messages_2570_);
lean_ctor_set(v_reuseFailAlloc_2596_, 8, v_infoState_2571_);
lean_ctor_set(v_reuseFailAlloc_2596_, 9, v_snapshotTasks_2572_);
v___x_2578_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v_mctx_2581_; lean_object* v_zetaDeltaFVarIds_2582_; lean_object* v_postponed_2583_; lean_object* v_diag_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2594_; 
v___x_2579_ = lean_st_ref_put(v___y_2556_, v___x_2578_);
v___x_2580_ = lean_st_ref_take(v___y_2559_);
v_mctx_2581_ = lean_ctor_get(v___x_2580_, 0);
v_zetaDeltaFVarIds_2582_ = lean_ctor_get(v___x_2580_, 2);
v_postponed_2583_ = lean_ctor_get(v___x_2580_, 3);
v_diag_2584_ = lean_ctor_get(v___x_2580_, 4);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2580_, 1);
lean_dec(v_unused_2595_);
v___x_2586_ = v___x_2580_;
v_isShared_2587_ = v_isSharedCheck_2594_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_diag_2584_);
lean_inc(v_postponed_2583_);
lean_inc(v_zetaDeltaFVarIds_2582_);
lean_inc(v_mctx_2581_);
lean_dec(v___x_2580_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2594_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_box(0);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 1, v___x_2560_);
v___x_2590_ = v___x_2586_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_mctx_2581_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v_zetaDeltaFVarIds_2582_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v_postponed_2583_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v_diag_2584_);
v___x_2590_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_st_ref_put(v___y_2559_, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2588_);
return v___x_2592_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2556_ = stack[0].m_obj;
uint8_t v_isExporting_2557_ = stack[1].m_num;
lean_object* v___x_2558_ = stack[2].m_obj;
lean_object* v___y_2559_ = stack[3].m_obj;
lean_object* v___x_2560_ = stack[4].m_obj;
lean_object* v_a_x3f_2561_ = stack[5].m_obj;
lean_object* v_res_2599_;
v_res_2599_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2556_, v_isExporting_2557_, v___x_2558_, v___y_2559_, v___x_2560_, v_a_x3f_2561_);
stack->m_obj
 = v_res_2599_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2600_, lean_object* v_isExporting_2601_, lean_object* v___x_2602_, lean_object* v___y_2603_, lean_object* v___x_2604_, lean_object* v_a_x3f_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v_isExporting_boxed_2607_; lean_object* v_res_2608_; 
v_isExporting_boxed_2607_ = lean_unbox(v_isExporting_2601_);
v_res_2608_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2600_, v_isExporting_boxed_2607_, v___x_2602_, v___y_2603_, v___x_2604_, v_a_x3f_2605_);
lean_dec(v_a_x3f_2605_);
lean_dec(v___y_2603_);
lean_dec(v___y_2600_);
return v_res_2608_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2609_, uint8_t v_isExporting_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; lean_object* v_env_2617_; lean_object* v___x_2618_; uint8_t v_isModule_2619_; 
v___x_2616_ = lean_st_ref_get(v___y_2614_);
v_env_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_ref(v_env_2617_);
lean_dec(v___x_2616_);
v___x_2618_ = l_Lean_Environment_header(v_env_2617_);
v_isModule_2619_ = lean_ctor_get_uint8(v___x_2618_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2618_);
if (v_isModule_2619_ == 0)
{
lean_object* v___x_2620_; 
lean_dec_ref(v_env_2617_);
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
v___x_2620_ = lean_apply_5(v_x_2609_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, lean_box(0));
return v___x_2620_;
}
else
{
uint8_t v_isExporting_2621_; 
v_isExporting_2621_ = lean_ctor_get_uint8(v_env_2617_, sizeof(void*)*13);
lean_dec_ref(v_env_2617_);
if (v_isExporting_2610_ == 0)
{
if (v_isExporting_2621_ == 0)
{
lean_object* v___x_2688_; 
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
v___x_2688_ = lean_apply_5(v_x_2609_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, lean_box(0));
return v___x_2688_;
}
else
{
goto v___jp_2622_;
}
}
else
{
if (v_isExporting_2621_ == 0)
{
goto v___jp_2622_;
}
else
{
lean_object* v___x_2689_; 
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
v___x_2689_ = lean_apply_5(v_x_2609_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, lean_box(0));
return v___x_2689_;
}
}
v___jp_2622_:
{
lean_object* v___x_2623_; lean_object* v_env_2624_; lean_object* v_nextMacroScope_2625_; lean_object* v_ngen_2626_; lean_object* v_auxDeclNGen_2627_; lean_object* v_traceState_2628_; lean_object* v_recordedDeps_2629_; lean_object* v_messages_2630_; lean_object* v_infoState_2631_; lean_object* v_snapshotTasks_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2686_; 
v___x_2623_ = lean_st_ref_take(v___y_2614_);
v_env_2624_ = lean_ctor_get(v___x_2623_, 0);
v_nextMacroScope_2625_ = lean_ctor_get(v___x_2623_, 1);
v_ngen_2626_ = lean_ctor_get(v___x_2623_, 2);
v_auxDeclNGen_2627_ = lean_ctor_get(v___x_2623_, 3);
v_traceState_2628_ = lean_ctor_get(v___x_2623_, 4);
v_recordedDeps_2629_ = lean_ctor_get(v___x_2623_, 6);
v_messages_2630_ = lean_ctor_get(v___x_2623_, 7);
v_infoState_2631_ = lean_ctor_get(v___x_2623_, 8);
v_snapshotTasks_2632_ = lean_ctor_get(v___x_2623_, 9);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2623_, 5);
lean_dec(v_unused_2687_);
v___x_2634_ = v___x_2623_;
v_isShared_2635_ = v_isSharedCheck_2686_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snapshotTasks_2632_);
lean_inc(v_infoState_2631_);
lean_inc(v_messages_2630_);
lean_inc(v_recordedDeps_2629_);
lean_inc(v_traceState_2628_);
lean_inc(v_auxDeclNGen_2627_);
lean_inc(v_ngen_2626_);
lean_inc(v_nextMacroScope_2625_);
lean_inc(v_env_2624_);
lean_dec(v___x_2623_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2686_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2636_ = l_Lean_Environment_setExporting(v_env_2624_, v_isExporting_2610_);
v___x_2637_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 5, v___x_2637_);
lean_ctor_set(v___x_2634_, 0, v___x_2636_);
v___x_2639_ = v___x_2634_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_nextMacroScope_2625_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_ngen_2626_);
lean_ctor_set(v_reuseFailAlloc_2685_, 3, v_auxDeclNGen_2627_);
lean_ctor_set(v_reuseFailAlloc_2685_, 4, v_traceState_2628_);
lean_ctor_set(v_reuseFailAlloc_2685_, 5, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2685_, 6, v_recordedDeps_2629_);
lean_ctor_set(v_reuseFailAlloc_2685_, 7, v_messages_2630_);
lean_ctor_set(v_reuseFailAlloc_2685_, 8, v_infoState_2631_);
lean_ctor_set(v_reuseFailAlloc_2685_, 9, v_snapshotTasks_2632_);
v___x_2639_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_mctx_2642_; lean_object* v_zetaDeltaFVarIds_2643_; lean_object* v_postponed_2644_; lean_object* v_diag_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2683_; 
v___x_2640_ = lean_st_ref_put(v___y_2614_, v___x_2639_);
v___x_2641_ = lean_st_ref_take(v___y_2612_);
v_mctx_2642_ = lean_ctor_get(v___x_2641_, 0);
v_zetaDeltaFVarIds_2643_ = lean_ctor_get(v___x_2641_, 2);
v_postponed_2644_ = lean_ctor_get(v___x_2641_, 3);
v_diag_2645_ = lean_ctor_get(v___x_2641_, 4);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2641_, 1);
lean_dec(v_unused_2684_);
v___x_2647_ = v___x_2641_;
v_isShared_2648_ = v_isSharedCheck_2683_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_diag_2645_);
lean_inc(v_postponed_2644_);
lean_inc(v_zetaDeltaFVarIds_2643_);
lean_inc(v_mctx_2642_);
lean_dec(v___x_2641_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2683_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_mctx_2642_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_zetaDeltaFVarIds_2643_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_postponed_2644_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_diag_2645_);
v___x_2651_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v_r_2653_; 
v___x_2652_ = lean_st_ref_put(v___y_2612_, v___x_2651_);
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
v_r_2653_ = lean_apply_5(v_x_2609_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, lean_box(0));
if (lean_obj_tag(v_r_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2670_; 
v_a_2654_ = lean_ctor_get(v_r_2653_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_r_2653_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2656_ = v_r_2653_;
v_isShared_2657_ = v_isSharedCheck_2670_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v_r_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2670_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
lean_inc(v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set_tag(v___x_2656_, 1);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v___x_2660_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2614_, v_isExporting_2621_, v___x_2637_, v___y_2612_, v___x_2649_, v___x_2659_);
lean_dec_ref(v___x_2659_);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v___x_2660_, 0);
lean_dec(v_unused_2668_);
v___x_2662_ = v___x_2660_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v___x_2660_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_a_2654_);
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2654_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
v_a_2671_ = lean_ctor_get(v_r_2653_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v_r_2653_, 1);
v___x_2672_ = lean_box(0);
v___x_2673_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2614_, v_isExporting_2621_, v___x_2637_, v___y_2612_, v___x_2649_, v___x_2672_);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2673_, 0);
lean_dec(v_unused_2681_);
v___x_2675_ = v___x_2673_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_dec(v___x_2673_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 1);
lean_ctor_set(v___x_2675_, 0, v_a_2671_);
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2671_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2609_ = stack[0].m_obj;
uint8_t v_isExporting_2610_ = stack[1].m_num;
lean_object* v___y_2611_ = stack[2].m_obj;
lean_object* v___y_2612_ = stack[3].m_obj;
lean_object* v___y_2613_ = stack[4].m_obj;
lean_object* v___y_2614_ = stack[5].m_obj;
lean_object* v_res_2690_;
v_res_2690_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2609_, v_isExporting_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
stack->m_obj
 = v_res_2690_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2691_, lean_object* v_isExporting_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v_isExporting_boxed_2698_; lean_object* v_res_2699_; 
v_isExporting_boxed_2698_ = lean_unbox(v_isExporting_2692_);
v_res_2699_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2691_, v_isExporting_boxed_2698_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
return v_res_2699_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2700_, uint8_t v_when_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
if (v_when_2701_ == 0)
{
lean_object* v___x_2707_; 
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
v___x_2707_ = lean_apply_5(v_x_2700_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, lean_box(0));
return v___x_2707_;
}
else
{
uint8_t v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = 0;
v___x_2709_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2700_, v___x_2708_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2709_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2700_ = stack[0].m_obj;
uint8_t v_when_2701_ = stack[1].m_num;
lean_object* v___y_2702_ = stack[2].m_obj;
lean_object* v___y_2703_ = stack[3].m_obj;
lean_object* v___y_2704_ = stack[4].m_obj;
lean_object* v___y_2705_ = stack[5].m_obj;
lean_object* v_res_2710_;
v_res_2710_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2700_, v_when_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
stack->m_obj
 = v_res_2710_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2711_, lean_object* v_when_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
uint8_t v_when_boxed_2718_; lean_object* v_res_2719_; 
v_when_boxed_2718_ = lean_unbox(v_when_2712_);
v_res_2719_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2711_, v_when_boxed_2718_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2719_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2722_ = l_Lean_stringToMessageData(v___x_2721_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2727_ = l_Lean_stringToMessageData(v___x_2726_);
return v___x_2727_;
}
}
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2728_, uint8_t v_nonRec_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v_env_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___f_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2735_ = lean_st_ref_get(v___y_2733_);
v_env_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_env_2736_);
lean_dec(v___x_2735_);
v___x_2737_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2728_);
v___x_2738_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2736_, v_declName_2728_, v___x_2737_);
v___x_2739_ = lean_box(v_nonRec_2729_);
lean_inc(v___x_2738_);
v___f_2740_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2740_, 0, v___x_2738_);
lean_closure_set(v___f_2740_, 1, v_declName_2728_);
lean_closure_set(v___f_2740_, 2, v___x_2739_);
lean_closure_set(v___f_2740_, 3, v___x_2737_);
v___x_2741_ = 1;
v___x_2742_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2740_, v___x_2741_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
if (lean_obj_tag(v_a_2743_) == 1)
{
lean_object* v_val_2744_; uint8_t v___x_2745_; 
v_val_2744_ = lean_ctor_get(v_a_2743_, 0);
v___x_2745_ = lean_name_eq(v_val_2744_, v___x_2738_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_inc(v_val_2744_);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2746_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2747_ = l_Lean_MessageData_ofName(v_val_2744_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = l_Lean_MessageData_ofName(v___x_2738_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2754_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
else
{
lean_dec(v___x_2738_);
return v___x_2742_;
}
}
else
{
lean_dec(v___x_2738_);
return v___x_2742_;
}
}
else
{
lean_dec(v___x_2738_);
return v___x_2742_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2728_ = stack[0].m_obj;
uint8_t v_nonRec_2729_ = stack[1].m_num;
lean_object* v___y_2730_ = stack[2].m_obj;
lean_object* v___y_2731_ = stack[3].m_obj;
lean_object* v___y_2732_ = stack[4].m_obj;
lean_object* v___y_2733_ = stack[5].m_obj;
lean_object* v_res_2764_;
v_res_2764_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2728_, v_nonRec_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
stack->m_obj
 = v_res_2764_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2765_, lean_object* v_nonRec_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
uint8_t v_nonRec_boxed_2772_; lean_object* v_res_2773_; 
v_nonRec_boxed_2772_ = lean_unbox(v_nonRec_2766_);
v_res_2773_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2765_, v_nonRec_boxed_2772_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
return v_res_2773_;
}
}
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2774_, uint8_t v_nonRec_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2781_ = lean_box(v_nonRec_2775_);
v___f_2782_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2782_, 0, v_declName_2774_);
lean_closure_set(v___f_2782_, 1, v___x_2781_);
v___x_2783_ = lean_unsigned_to_nat(32u);
v___x_2784_ = lean_mk_empty_array_with_capacity(v___x_2783_);
lean_dec_ref(v___x_2784_);
v___x_2785_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2786_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2787_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2785_, v___x_2786_, v___f_2782_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2787_;
}
}
LEAN_EXPORT void l_Lean_Meta_getUnfoldEqnFor_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2774_ = stack[0].m_obj;
uint8_t v_nonRec_2775_ = stack[1].m_num;
lean_object* v_a_2776_ = stack[2].m_obj;
lean_object* v_a_2777_ = stack[3].m_obj;
lean_object* v_a_2778_ = stack[4].m_obj;
lean_object* v_a_2779_ = stack[5].m_obj;
lean_object* v_res_2788_;
v_res_2788_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2774_, v_nonRec_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
stack->m_obj
 = v_res_2788_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2789_, lean_object* v_nonRec_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
uint8_t v_nonRec_boxed_2796_; lean_object* v_res_2797_; 
v_nonRec_boxed_2796_ = lean_unbox(v_nonRec_2790_);
v_res_2797_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2789_, v_nonRec_boxed_2796_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
return v_res_2797_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2798_, lean_object* v_as_2799_, lean_object* v_as_x27_2800_, lean_object* v_b_2801_, lean_object* v_a_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2798_, v_as_x27_2800_, v_b_2801_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2798_ = stack[0].m_obj;
lean_object* v_as_2799_ = stack[1].m_obj;
lean_object* v_as_x27_2800_ = stack[2].m_obj;
lean_object* v_b_2801_ = stack[3].m_obj;
lean_object* v___y_2803_ = stack[5].m_obj;
lean_object* v___y_2804_ = stack[6].m_obj;
lean_object* v___y_2805_ = stack[7].m_obj;
lean_object* v___y_2806_ = stack[8].m_obj;
lean_object* v_res_2809_;
v_res_2809_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2798_, v_as_2799_, v_as_x27_2800_, v_b_2801_, lean_box(0), v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
stack->m_obj
 = v_res_2809_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2810_, lean_object* v_as_2811_, lean_object* v_as_x27_2812_, lean_object* v_b_2813_, lean_object* v_a_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2810_, v_as_2811_, v_as_x27_2812_, v_b_2813_, v_a_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v_as_x27_2812_);
lean_dec(v_as_2811_);
return v_res_2820_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2821_, lean_object* v_x_2822_, uint8_t v_isExporting_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2822_, v_isExporting_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2829_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2822_ = stack[1].m_obj;
uint8_t v_isExporting_2823_ = stack[2].m_num;
lean_object* v___y_2824_ = stack[3].m_obj;
lean_object* v___y_2825_ = stack[4].m_obj;
lean_object* v___y_2826_ = stack[5].m_obj;
lean_object* v___y_2827_ = stack[6].m_obj;
lean_object* v_res_2830_;
v_res_2830_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_box(0), v_x_2822_, v_isExporting_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
stack->m_obj
 = v_res_2830_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2831_, lean_object* v_x_2832_, lean_object* v_isExporting_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
uint8_t v_isExporting_boxed_2839_; lean_object* v_res_2840_; 
v_isExporting_boxed_2839_ = lean_unbox(v_isExporting_2833_);
v_res_2840_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2831_, v_x_2832_, v_isExporting_boxed_2839_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2840_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2841_, lean_object* v_x_2842_, uint8_t v_when_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2842_, v_when_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2842_ = stack[1].m_obj;
uint8_t v_when_2843_ = stack[2].m_num;
lean_object* v___y_2844_ = stack[3].m_obj;
lean_object* v___y_2845_ = stack[4].m_obj;
lean_object* v___y_2846_ = stack[5].m_obj;
lean_object* v___y_2847_ = stack[6].m_obj;
lean_object* v_res_2850_;
v_res_2850_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_box(0), v_x_2842_, v_when_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
stack->m_obj
 = v_res_2850_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_x_2852_, lean_object* v_when_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
uint8_t v_when_boxed_2859_; lean_object* v_res_2860_; 
v_when_boxed_2859_ = lean_unbox(v_when_2853_);
v_res_2860_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2851_, v_x_2852_, v_when_boxed_2859_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2860_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2861_, lean_object* v_msg_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2862_ = stack[1].m_obj;
lean_object* v___y_2863_ = stack[2].m_obj;
lean_object* v___y_2864_ = stack[3].m_obj;
lean_object* v___y_2865_ = stack[4].m_obj;
lean_object* v___y_2866_ = stack[5].m_obj;
lean_object* v_res_2869_;
v_res_2869_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_box(0), v_msg_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
stack->m_obj
 = v_res_2869_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2870_, lean_object* v_msg_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2870_, v_msg_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2877_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_unsigned_to_nat(32u);
v___x_2879_ = lean_mk_empty_array_with_capacity(v___x_2878_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2881_ = ((size_t)5ULL);
v___x_2882_ = lean_unsigned_to_nat(0u);
v___x_2883_ = lean_unsigned_to_nat(32u);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2885_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2886_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v___x_2884_);
lean_ctor_set(v___x_2886_, 2, v___x_2882_);
lean_ctor_set(v___x_2886_, 3, v___x_2882_);
lean_ctor_set_usize(v___x_2886_, 4, v___x_2881_);
return v___x_2886_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v_traceState_2890_; lean_object* v_traces_2891_; lean_object* v___x_2892_; lean_object* v_traceState_2893_; lean_object* v_env_2894_; lean_object* v_nextMacroScope_2895_; lean_object* v_ngen_2896_; lean_object* v_auxDeclNGen_2897_; lean_object* v_cache_2898_; lean_object* v_recordedDeps_2899_; lean_object* v_messages_2900_; lean_object* v_infoState_2901_; lean_object* v_snapshotTasks_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2921_; 
v___x_2889_ = lean_st_ref_get(v___y_2887_);
v_traceState_2890_ = lean_ctor_get(v___x_2889_, 4);
lean_inc_ref(v_traceState_2890_);
lean_dec(v___x_2889_);
v_traces_2891_ = lean_ctor_get(v_traceState_2890_, 0);
lean_inc_ref(v_traces_2891_);
lean_dec_ref(v_traceState_2890_);
v___x_2892_ = lean_st_ref_take(v___y_2887_);
v_traceState_2893_ = lean_ctor_get(v___x_2892_, 4);
v_env_2894_ = lean_ctor_get(v___x_2892_, 0);
v_nextMacroScope_2895_ = lean_ctor_get(v___x_2892_, 1);
v_ngen_2896_ = lean_ctor_get(v___x_2892_, 2);
v_auxDeclNGen_2897_ = lean_ctor_get(v___x_2892_, 3);
v_cache_2898_ = lean_ctor_get(v___x_2892_, 5);
v_recordedDeps_2899_ = lean_ctor_get(v___x_2892_, 6);
v_messages_2900_ = lean_ctor_get(v___x_2892_, 7);
v_infoState_2901_ = lean_ctor_get(v___x_2892_, 8);
v_snapshotTasks_2902_ = lean_ctor_get(v___x_2892_, 9);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2904_ = v___x_2892_;
v_isShared_2905_ = v_isSharedCheck_2921_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snapshotTasks_2902_);
lean_inc(v_infoState_2901_);
lean_inc(v_messages_2900_);
lean_inc(v_recordedDeps_2899_);
lean_inc(v_cache_2898_);
lean_inc(v_traceState_2893_);
lean_inc(v_auxDeclNGen_2897_);
lean_inc(v_ngen_2896_);
lean_inc(v_nextMacroScope_2895_);
lean_inc(v_env_2894_);
lean_dec(v___x_2892_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2921_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
uint64_t v_tid_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2919_; 
v_tid_2906_ = lean_ctor_get_uint64(v_traceState_2893_, sizeof(void*)*1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_traceState_2893_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v_traceState_2893_, 0);
lean_dec(v_unused_2920_);
v___x_2908_ = v_traceState_2893_;
v_isShared_2909_ = v_isSharedCheck_2919_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v_traceState_2893_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2919_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2910_);
lean_ctor_set_uint64(v_reuseFailAlloc_2918_, sizeof(void*)*1, v_tid_2906_);
v___x_2912_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 4, v___x_2912_);
v___x_2914_ = v___x_2904_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_env_2894_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_nextMacroScope_2895_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_ngen_2896_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v_auxDeclNGen_2897_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v_cache_2898_);
lean_ctor_set(v_reuseFailAlloc_2917_, 6, v_recordedDeps_2899_);
lean_ctor_set(v_reuseFailAlloc_2917_, 7, v_messages_2900_);
lean_ctor_set(v_reuseFailAlloc_2917_, 8, v_infoState_2901_);
lean_ctor_set(v_reuseFailAlloc_2917_, 9, v_snapshotTasks_2902_);
v___x_2914_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_st_ref_put(v___y_2887_, v___x_2914_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_traces_2891_);
return v___x_2916_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2887_ = stack[0].m_obj;
lean_object* v_res_2922_;
v_res_2922_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2887_);
stack->m_obj
 = v_res_2922_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2923_);
lean_dec(v___y_2923_);
return v_res_2925_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2926_ = stack[0].m_obj;
lean_object* v___y_2927_ = stack[1].m_obj;
lean_object* v_res_2930_;
v_res_2930_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2926_, v___y_2927_);
stack->m_obj
 = v_res_2930_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
return v_res_2934_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = 0;
v___x_2940_ = lean_box(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_2935_ = stack[0].m_obj;
lean_object* v___y_2936_ = stack[1].m_obj;
lean_object* v___y_2937_ = stack[2].m_obj;
lean_object* v_res_2942_;
v_res_2942_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2935_, v___y_2936_, v___y_2937_);
stack->m_obj
 = v_res_2942_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
return v_res_2947_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2951_, lean_object* v_x_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2956_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2957_ = l_Lean_MessageData_ofName(v_name_2951_);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2951_ = stack[0].m_obj;
lean_object* v_x_2952_ = stack[1].m_obj;
lean_object* v___y_2953_ = stack[2].m_obj;
lean_object* v___y_2954_ = stack[3].m_obj;
lean_object* v_res_2960_;
v_res_2960_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2951_, v_x_2952_, v___y_2953_, v___y_2954_);
stack->m_obj
 = v_res_2960_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2961_, lean_object* v_x_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2961_, v_x_2962_, v___y_2963_, v___y_2964_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v_x_2962_);
return v_res_2966_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2967_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
v_a_2969_ = lean_ctor_get(v_x_2967_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_x_2967_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v_x_2967_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v_x_2967_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
lean_ctor_set_tag(v___x_2971_, 1);
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
v_a_2977_ = lean_ctor_get(v_x_2967_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_x_2967_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v_x_2967_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v_x_2967_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set_tag(v___x_2979_, 0);
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2967_ = stack[0].m_obj;
lean_object* v_res_2985_;
v_res_2985_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2967_);
stack->m_obj
 = v_res_2985_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2986_);
return v_res_2988_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2989_){
_start:
{
if (lean_obj_tag(v_e_2989_) == 0)
{
uint8_t v___x_2990_; 
v___x_2990_ = 2;
return v___x_2990_;
}
else
{
lean_object* v_a_2991_; uint8_t v___x_2992_; 
v_a_2991_ = lean_ctor_get(v_e_2989_, 0);
v___x_2992_ = lean_unbox(v_a_2991_);
if (v___x_2992_ == 0)
{
uint8_t v___x_2993_; 
v___x_2993_ = 1;
return v___x_2993_;
}
else
{
uint8_t v___x_2994_; 
v___x_2994_ = 0;
return v___x_2994_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2989_ = stack[0].m_obj;
uint8_t v_res_2995_;
v_res_2995_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2989_);
stack->m_num = v_res_2995_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2996_){
_start:
{
uint8_t v_res_2997_; lean_object* v_r_2998_; 
v_res_2997_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2996_);
lean_dec_ref(v_e_2996_);
v_r_2998_ = lean_box(v_res_2997_);
return v_r_2998_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2999_, size_t v_i_3000_, lean_object* v_bs_3001_){
_start:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_usize_dec_lt(v_i_3000_, v_sz_2999_);
if (v___x_3002_ == 0)
{
return v_bs_3001_;
}
else
{
lean_object* v_v_3003_; lean_object* v_msg_3004_; lean_object* v___x_3005_; lean_object* v_bs_x27_3006_; size_t v___x_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v_v_3003_ = lean_array_uget_borrowed(v_bs_3001_, v_i_3000_);
v_msg_3004_ = lean_ctor_get(v_v_3003_, 1);
lean_inc_ref(v_msg_3004_);
v___x_3005_ = lean_unsigned_to_nat(0u);
v_bs_x27_3006_ = lean_array_uset(v_bs_3001_, v_i_3000_, v___x_3005_);
v___x_3007_ = ((size_t)1ULL);
v___x_3008_ = lean_usize_add(v_i_3000_, v___x_3007_);
v___x_3009_ = lean_array_uset(v_bs_x27_3006_, v_i_3000_, v_msg_3004_);
v_i_3000_ = v___x_3008_;
v_bs_3001_ = v___x_3009_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2999_ = stack[0].m_num;
size_t v_i_3000_ = stack[1].m_num;
lean_object* v_bs_3001_ = stack[2].m_obj;
lean_object* v_res_3011_;
v_res_3011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2999_, v_i_3000_, v_bs_3001_);
stack->m_obj
 = v_res_3011_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3012_, lean_object* v_i_3013_, lean_object* v_bs_3014_){
_start:
{
size_t v_sz_boxed_3015_; size_t v_i_boxed_3016_; lean_object* v_res_3017_; 
v_sz_boxed_3015_ = lean_unbox_usize(v_sz_3012_);
lean_dec(v_sz_3012_);
v_i_boxed_3016_ = lean_unbox_usize(v_i_3013_);
lean_dec(v_i_3013_);
v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_3015_, v_i_boxed_3016_, v_bs_3014_);
return v_res_3017_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_3018_, lean_object* v_data_3019_, lean_object* v_ref_3020_, lean_object* v_msg_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_toCold_3025_; lean_object* v_currRecDepth_3026_; lean_object* v_ref_3027_; uint16_t v_optionFlags_3028_; uint8_t v_suppressElabErrors_3029_; uint8_t v_isRecordingDeps_3030_; lean_object* v_ref_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v_traceState_3034_; lean_object* v_traces_3035_; lean_object* v___x_3036_; size_t v_sz_3037_; size_t v___x_3038_; lean_object* v___x_3039_; lean_object* v_msg_3040_; lean_object* v___x_3041_; lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3080_; 
v_toCold_3025_ = lean_ctor_get(v___y_3022_, 0);
v_currRecDepth_3026_ = lean_ctor_get(v___y_3022_, 1);
v_ref_3027_ = lean_ctor_get(v___y_3022_, 2);
v_optionFlags_3028_ = lean_ctor_get_uint16(v___y_3022_, sizeof(void*)*3);
v_suppressElabErrors_3029_ = lean_ctor_get_uint8(v___y_3022_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3030_ = lean_ctor_get_uint8(v___y_3022_, sizeof(void*)*3 + 3);
v_ref_3031_ = l_Lean_replaceRef(v_ref_3020_, v_ref_3027_);
lean_inc(v_currRecDepth_3026_);
lean_inc_ref(v_toCold_3025_);
v___x_3032_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3032_, 0, v_toCold_3025_);
lean_ctor_set(v___x_3032_, 1, v_currRecDepth_3026_);
lean_ctor_set(v___x_3032_, 2, v_ref_3031_);
lean_ctor_set_uint16(v___x_3032_, sizeof(void*)*3, v_optionFlags_3028_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*3 + 2, v_suppressElabErrors_3029_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*3 + 3, v_isRecordingDeps_3030_);
v___x_3033_ = lean_st_ref_get(v___y_3023_);
v_traceState_3034_ = lean_ctor_get(v___x_3033_, 4);
lean_inc_ref(v_traceState_3034_);
lean_dec(v___x_3033_);
v_traces_3035_ = lean_ctor_get(v_traceState_3034_, 0);
lean_inc_ref(v_traces_3035_);
lean_dec_ref(v_traceState_3034_);
v___x_3036_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3035_);
lean_dec_ref(v_traces_3035_);
v_sz_3037_ = lean_array_size(v___x_3036_);
v___x_3038_ = ((size_t)0ULL);
v___x_3039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_3037_, v___x_3038_, v___x_3036_);
v_msg_3040_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3040_, 0, v_data_3019_);
lean_ctor_set(v_msg_3040_, 1, v_msg_3021_);
lean_ctor_set(v_msg_3040_, 2, v___x_3039_);
v___x_3041_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_3040_, v___x_3032_, v___y_3023_);
lean_dec_ref_known(v___x_3032_, 3);
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3080_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3080_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v_traceState_3047_; lean_object* v_env_3048_; lean_object* v_nextMacroScope_3049_; lean_object* v_ngen_3050_; lean_object* v_auxDeclNGen_3051_; lean_object* v_cache_3052_; lean_object* v_recordedDeps_3053_; lean_object* v_messages_3054_; lean_object* v_infoState_3055_; lean_object* v_snapshotTasks_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3079_; 
v___x_3046_ = lean_st_ref_take(v___y_3023_);
v_traceState_3047_ = lean_ctor_get(v___x_3046_, 4);
v_env_3048_ = lean_ctor_get(v___x_3046_, 0);
v_nextMacroScope_3049_ = lean_ctor_get(v___x_3046_, 1);
v_ngen_3050_ = lean_ctor_get(v___x_3046_, 2);
v_auxDeclNGen_3051_ = lean_ctor_get(v___x_3046_, 3);
v_cache_3052_ = lean_ctor_get(v___x_3046_, 5);
v_recordedDeps_3053_ = lean_ctor_get(v___x_3046_, 6);
v_messages_3054_ = lean_ctor_get(v___x_3046_, 7);
v_infoState_3055_ = lean_ctor_get(v___x_3046_, 8);
v_snapshotTasks_3056_ = lean_ctor_get(v___x_3046_, 9);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3058_ = v___x_3046_;
v_isShared_3059_ = v_isSharedCheck_3079_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_snapshotTasks_3056_);
lean_inc(v_infoState_3055_);
lean_inc(v_messages_3054_);
lean_inc(v_recordedDeps_3053_);
lean_inc(v_cache_3052_);
lean_inc(v_traceState_3047_);
lean_inc(v_auxDeclNGen_3051_);
lean_inc(v_ngen_3050_);
lean_inc(v_nextMacroScope_3049_);
lean_inc(v_env_3048_);
lean_dec(v___x_3046_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3079_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
uint64_t v_tid_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3077_; 
v_tid_3060_ = lean_ctor_get_uint64(v_traceState_3047_, sizeof(void*)*1);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_traceState_3047_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v_traceState_3047_, 0);
lean_dec(v_unused_3078_);
v___x_3062_ = v_traceState_3047_;
v_isShared_3063_ = v_isSharedCheck_3077_;
goto v_resetjp_3061_;
}
else
{
lean_dec(v_traceState_3047_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3077_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_ref_3020_);
lean_ctor_set(v___x_3065_, 1, v_a_3042_);
v___x_3066_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3018_, v___x_3065_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3066_);
v___x_3068_ = v___x_3062_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3066_);
lean_ctor_set_uint64(v_reuseFailAlloc_3076_, sizeof(void*)*1, v_tid_3060_);
v___x_3068_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3070_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 4, v___x_3068_);
v___x_3070_ = v___x_3058_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_env_3048_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_nextMacroScope_3049_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_ngen_3050_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_auxDeclNGen_3051_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3075_, 5, v_cache_3052_);
lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_recordedDeps_3053_);
lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_messages_3054_);
lean_ctor_set(v_reuseFailAlloc_3075_, 8, v_infoState_3055_);
lean_ctor_set(v_reuseFailAlloc_3075_, 9, v_snapshotTasks_3056_);
v___x_3070_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_st_ref_put(v___y_3023_, v___x_3070_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3064_);
v___x_3073_ = v___x_3044_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3064_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_3018_ = stack[0].m_obj;
lean_object* v_data_3019_ = stack[1].m_obj;
lean_object* v_ref_3020_ = stack[2].m_obj;
lean_object* v_msg_3021_ = stack[3].m_obj;
lean_object* v___y_3022_ = stack[4].m_obj;
lean_object* v___y_3023_ = stack[5].m_obj;
lean_object* v_res_3081_;
v_res_3081_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_3018_, v_data_3019_, v_ref_3020_, v_msg_3021_, v___y_3022_, v___y_3023_);
stack->m_obj
 = v_res_3081_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_3082_, lean_object* v_data_3083_, lean_object* v_ref_3084_, lean_object* v_msg_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_3082_, v_data_3083_, v_ref_3084_, v_msg_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
return v_res_3089_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_3092_ = l_Lean_stringToMessageData(v___x_3091_);
return v___x_3092_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_3093_; double v___x_3094_; 
v___x_3093_ = lean_unsigned_to_nat(1000u);
v___x_3094_ = lean_float_of_nat(v___x_3093_);
return v___x_3094_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_3095_, uint8_t v_collapsed_3096_, lean_object* v_tag_3097_, lean_object* v_opts_3098_, uint8_t v_clsEnabled_3099_, lean_object* v_oldTraces_3100_, lean_object* v_msg_3101_, lean_object* v_resStartStop_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v_data_3111_; lean_object* v_fst_3122_; lean_object* v_snd_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___y_3127_; lean_object* v_a_3128_; uint8_t v___y_3143_; double v___y_3175_; 
v_fst_3106_ = lean_ctor_get(v_resStartStop_3102_, 0);
lean_inc(v_fst_3106_);
v_snd_3107_ = lean_ctor_get(v_resStartStop_3102_, 1);
lean_inc(v_snd_3107_);
lean_dec_ref(v_resStartStop_3102_);
v_fst_3122_ = lean_ctor_get(v_snd_3107_, 0);
lean_inc(v_fst_3122_);
v_snd_3123_ = lean_ctor_get(v_snd_3107_, 1);
lean_inc(v_snd_3123_);
lean_dec(v_snd_3107_);
v___x_3124_ = l_Lean_trace_profiler;
v___x_3125_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_3098_, v___x_3124_);
if (v___x_3125_ == 0)
{
v___y_3143_ = v___x_3125_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3181_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_3098_, v___x_3180_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; double v___x_3184_; double v___x_3185_; double v___x_3186_; 
v___x_3182_ = l_Lean_trace_profiler_threshold;
v___x_3183_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_3098_, v___x_3182_);
v___x_3184_ = lean_float_of_nat(v___x_3183_);
v___x_3185_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3186_ = lean_float_div(v___x_3184_, v___x_3185_);
v___y_3175_ = v___x_3186_;
goto v___jp_3174_;
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; double v___x_3189_; 
v___x_3187_ = l_Lean_trace_profiler_threshold;
v___x_3188_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_3098_, v___x_3187_);
v___x_3189_ = lean_float_of_nat(v___x_3188_);
v___y_3175_ = v___x_3189_;
goto v___jp_3174_;
}
}
v___jp_3108_:
{
lean_object* v___x_3112_; 
lean_inc(v___y_3110_);
v___x_3112_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_3100_, v_data_3111_, v___y_3110_, v___y_3109_, v___y_3103_, v___y_3104_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v___x_3113_; 
lean_dec_ref_known(v___x_3112_, 1);
v___x_3113_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_3106_);
return v___x_3113_;
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_fst_3106_);
v_a_3114_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3112_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3112_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
v___jp_3126_:
{
uint8_t v_result_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; double v___x_3132_; lean_object* v_data_3133_; 
v_result_3129_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_3106_);
v___x_3130_ = lean_box(v_result_3129_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
v___x_3132_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_3097_);
lean_inc_ref(v___x_3131_);
lean_inc(v_cls_3095_);
v_data_3133_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3133_, 0, v_cls_3095_);
lean_ctor_set(v_data_3133_, 1, v___x_3131_);
lean_ctor_set(v_data_3133_, 2, v_tag_3097_);
lean_ctor_set_float(v_data_3133_, sizeof(void*)*3, v___x_3132_);
lean_ctor_set_float(v_data_3133_, sizeof(void*)*3 + 8, v___x_3132_);
lean_ctor_set_uint8(v_data_3133_, sizeof(void*)*3 + 16, v_collapsed_3096_);
if (v___x_3125_ == 0)
{
lean_dec_ref_known(v___x_3131_, 1);
lean_dec(v_snd_3123_);
lean_dec(v_fst_3122_);
lean_dec_ref(v_tag_3097_);
lean_dec(v_cls_3095_);
v___y_3109_ = v_a_3128_;
v___y_3110_ = v___y_3127_;
v_data_3111_ = v_data_3133_;
goto v___jp_3108_;
}
else
{
lean_object* v_data_3134_; double v___x_3135_; double v___x_3136_; 
lean_dec_ref_known(v_data_3133_, 3);
v_data_3134_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3134_, 0, v_cls_3095_);
lean_ctor_set(v_data_3134_, 1, v___x_3131_);
lean_ctor_set(v_data_3134_, 2, v_tag_3097_);
v___x_3135_ = lean_unbox_float(v_fst_3122_);
lean_dec(v_fst_3122_);
lean_ctor_set_float(v_data_3134_, sizeof(void*)*3, v___x_3135_);
v___x_3136_ = lean_unbox_float(v_snd_3123_);
lean_dec(v_snd_3123_);
lean_ctor_set_float(v_data_3134_, sizeof(void*)*3 + 8, v___x_3136_);
lean_ctor_set_uint8(v_data_3134_, sizeof(void*)*3 + 16, v_collapsed_3096_);
v___y_3109_ = v_a_3128_;
v___y_3110_ = v___y_3127_;
v_data_3111_ = v_data_3134_;
goto v___jp_3108_;
}
}
v___jp_3137_:
{
lean_object* v_ref_3138_; lean_object* v___x_3139_; 
v_ref_3138_ = lean_ctor_get(v___y_3103_, 2);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
lean_inc(v_fst_3106_);
v___x_3139_ = lean_apply_4(v_msg_3101_, v_fst_3106_, v___y_3103_, v___y_3104_, lean_box(0));
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___y_3127_ = v_ref_3138_;
v_a_3128_ = v_a_3140_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3141_; 
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_3127_ = v_ref_3138_;
v_a_3128_ = v___x_3141_;
goto v___jp_3126_;
}
}
v___jp_3142_:
{
if (v_clsEnabled_3099_ == 0)
{
if (v___y_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v_traceState_3145_; lean_object* v_env_3146_; lean_object* v_nextMacroScope_3147_; lean_object* v_ngen_3148_; lean_object* v_auxDeclNGen_3149_; lean_object* v_cache_3150_; lean_object* v_recordedDeps_3151_; lean_object* v_messages_3152_; lean_object* v_infoState_3153_; lean_object* v_snapshotTasks_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_snd_3123_);
lean_dec(v_fst_3122_);
lean_dec_ref(v_msg_3101_);
lean_dec_ref(v_tag_3097_);
lean_dec(v_cls_3095_);
v___x_3144_ = lean_st_ref_take(v___y_3104_);
v_traceState_3145_ = lean_ctor_get(v___x_3144_, 4);
v_env_3146_ = lean_ctor_get(v___x_3144_, 0);
v_nextMacroScope_3147_ = lean_ctor_get(v___x_3144_, 1);
v_ngen_3148_ = lean_ctor_get(v___x_3144_, 2);
v_auxDeclNGen_3149_ = lean_ctor_get(v___x_3144_, 3);
v_cache_3150_ = lean_ctor_get(v___x_3144_, 5);
v_recordedDeps_3151_ = lean_ctor_get(v___x_3144_, 6);
v_messages_3152_ = lean_ctor_get(v___x_3144_, 7);
v_infoState_3153_ = lean_ctor_get(v___x_3144_, 8);
v_snapshotTasks_3154_ = lean_ctor_get(v___x_3144_, 9);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3156_ = v___x_3144_;
v_isShared_3157_ = v_isSharedCheck_3173_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_snapshotTasks_3154_);
lean_inc(v_infoState_3153_);
lean_inc(v_messages_3152_);
lean_inc(v_recordedDeps_3151_);
lean_inc(v_cache_3150_);
lean_inc(v_traceState_3145_);
lean_inc(v_auxDeclNGen_3149_);
lean_inc(v_ngen_3148_);
lean_inc(v_nextMacroScope_3147_);
lean_inc(v_env_3146_);
lean_dec(v___x_3144_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3173_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
uint64_t v_tid_3158_; lean_object* v_traces_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3172_; 
v_tid_3158_ = lean_ctor_get_uint64(v_traceState_3145_, sizeof(void*)*1);
v_traces_3159_ = lean_ctor_get(v_traceState_3145_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_traceState_3145_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3161_ = v_traceState_3145_;
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_traces_3159_);
lean_dec(v_traceState_3145_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3163_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3100_, v_traces_3159_);
lean_dec_ref(v_traces_3159_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3163_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3163_);
lean_ctor_set_uint64(v_reuseFailAlloc_3171_, sizeof(void*)*1, v_tid_3158_);
v___x_3165_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3167_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 4, v___x_3165_);
v___x_3167_ = v___x_3156_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_env_3146_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_nextMacroScope_3147_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_ngen_3148_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_auxDeclNGen_3149_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3170_, 5, v_cache_3150_);
lean_ctor_set(v_reuseFailAlloc_3170_, 6, v_recordedDeps_3151_);
lean_ctor_set(v_reuseFailAlloc_3170_, 7, v_messages_3152_);
lean_ctor_set(v_reuseFailAlloc_3170_, 8, v_infoState_3153_);
lean_ctor_set(v_reuseFailAlloc_3170_, 9, v_snapshotTasks_3154_);
v___x_3167_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = lean_st_ref_put(v___y_3104_, v___x_3167_);
v___x_3169_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_3106_);
return v___x_3169_;
}
}
}
}
}
else
{
goto v___jp_3137_;
}
}
else
{
goto v___jp_3137_;
}
}
v___jp_3174_:
{
double v___x_3176_; double v___x_3177_; double v___x_3178_; uint8_t v___x_3179_; 
v___x_3176_ = lean_unbox_float(v_snd_3123_);
v___x_3177_ = lean_unbox_float(v_fst_3122_);
v___x_3178_ = lean_float_sub(v___x_3176_, v___x_3177_);
v___x_3179_ = lean_float_decLt(v___y_3175_, v___x_3178_);
v___y_3143_ = v___x_3179_;
goto v___jp_3142_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3095_ = stack[0].m_obj;
uint8_t v_collapsed_3096_ = stack[1].m_num;
lean_object* v_tag_3097_ = stack[2].m_obj;
lean_object* v_opts_3098_ = stack[3].m_obj;
uint8_t v_clsEnabled_3099_ = stack[4].m_num;
lean_object* v_oldTraces_3100_ = stack[5].m_obj;
lean_object* v_msg_3101_ = stack[6].m_obj;
lean_object* v_resStartStop_3102_ = stack[7].m_obj;
lean_object* v___y_3103_ = stack[8].m_obj;
lean_object* v___y_3104_ = stack[9].m_obj;
lean_object* v_res_3190_;
v_res_3190_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3095_, v_collapsed_3096_, v_tag_3097_, v_opts_3098_, v_clsEnabled_3099_, v_oldTraces_3100_, v_msg_3101_, v_resStartStop_3102_, v___y_3103_, v___y_3104_);
stack->m_obj
 = v_res_3190_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3191_, lean_object* v_collapsed_3192_, lean_object* v_tag_3193_, lean_object* v_opts_3194_, lean_object* v_clsEnabled_3195_, lean_object* v_oldTraces_3196_, lean_object* v_msg_3197_, lean_object* v_resStartStop_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v_collapsed_boxed_3202_; uint8_t v_clsEnabled_boxed_3203_; lean_object* v_res_3204_; 
v_collapsed_boxed_3202_ = lean_unbox(v_collapsed_3192_);
v_clsEnabled_boxed_3203_ = lean_unbox(v_clsEnabled_3195_);
v_res_3204_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3191_, v_collapsed_boxed_3202_, v_tag_3193_, v_opts_3194_, v_clsEnabled_boxed_3203_, v_oldTraces_3196_, v_msg_3197_, v_resStartStop_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec_ref(v_opts_3194_);
return v_res_3204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3207_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3208_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
lean_ctor_set(v___x_3210_, 2, v___x_3209_);
lean_ctor_set(v___x_3210_, 3, v___x_3209_);
lean_ctor_set(v___x_3210_, 4, v___x_3208_);
lean_ctor_set(v___x_3210_, 5, v___x_3208_);
lean_ctor_set(v___x_3210_, 6, v___x_3208_);
lean_ctor_set(v___x_3210_, 7, v___x_3208_);
lean_ctor_set(v___x_3210_, 8, v___x_3208_);
lean_ctor_set(v___x_3210_, 9, v___x_3208_);
lean_ctor_set(v___x_3210_, 10, v___x_3208_);
lean_ctor_set(v___x_3210_, 11, v___x_3207_);
return v___x_3210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3212_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
lean_ctor_set(v___x_3212_, 2, v___x_3211_);
lean_ctor_set(v___x_3212_, 3, v___x_3211_);
lean_ctor_set(v___x_3212_, 4, v___x_3211_);
lean_ctor_set(v___x_3212_, 5, v___x_3211_);
return v___x_3212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
lean_ctor_set(v___x_3214_, 2, v___x_3213_);
lean_ctor_set(v___x_3214_, 3, v___x_3213_);
lean_ctor_set(v___x_3214_, 4, v___x_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3220_ = l_Lean_Name_append(v___x_3219_, v___x_3218_);
return v___x_3220_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3221_; double v___x_3222_; 
v___x_3221_ = lean_unsigned_to_nat(1000000000u);
v___x_3222_ = lean_float_of_nat(v___x_3221_);
return v___x_3222_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3223_, lean_object* v___f_3224_, lean_object* v_name_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_toCold_3229_; lean_object* v_options_3230_; uint8_t v_hasTrace_3231_; 
v_toCold_3229_ = lean_ctor_get(v___y_3226_, 0);
v_options_3230_ = lean_ctor_get(v_toCold_3229_, 2);
v_hasTrace_3231_ = lean_ctor_get_uint8(v_options_3230_, sizeof(void*)*1);
if (v_hasTrace_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v_env_3233_; lean_object* v___x_3234_; 
lean_dec_ref(v___f_3224_);
v___x_3232_ = lean_st_ref_get(v___y_3227_);
v_env_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc_ref(v_env_3233_);
lean_dec(v___x_3232_);
lean_inc(v_name_3225_);
v___x_3234_ = l_Lean_Meta_declFromEqLikeName(v_env_3233_, v_name_3225_);
if (lean_obj_tag(v___x_3234_) == 1)
{
lean_object* v_val_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3340_; 
v_val_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3340_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_val_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3340_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v_fst_3239_; lean_object* v_snd_3240_; lean_object* v___x_3241_; lean_object* v_env_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_fst_3239_ = lean_ctor_get(v_val_3235_, 0);
lean_inc_n(v_fst_3239_, 2);
v_snd_3240_ = lean_ctor_get(v_val_3235_, 1);
lean_inc_n(v_snd_3240_, 2);
lean_dec(v_val_3235_);
v___x_3241_ = lean_st_ref_get(v___y_3227_);
v_env_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc_ref(v_env_3242_);
lean_dec(v___x_3241_);
v___x_3243_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3242_, v_fst_3239_, v_snd_3240_);
v___x_3244_ = lean_name_eq(v_name_3225_, v___x_3243_);
lean_dec(v___x_3243_);
lean_dec(v_name_3225_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_dec(v_snd_3240_);
lean_dec(v_fst_3239_);
lean_dec(v___x_3223_);
v___x_3245_ = lean_box(v_hasTrace_3231_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set_tag(v___x_3237_, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3245_);
v___x_3247_ = v___x_3237_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
else
{
uint8_t v___x_3249_; lean_object* v_a_3251_; 
lean_inc(v_snd_3240_);
v___x_3249_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3240_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3265_; uint8_t v___x_3266_; lean_object* v_a_3268_; 
lean_del_object(v___x_3237_);
v___x_3265_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3266_ = lean_string_dec_eq(v_snd_3240_, v___x_3265_);
lean_dec(v_snd_3240_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec(v_fst_3239_);
lean_dec(v___x_3223_);
v___x_3280_ = lean_box(v_hasTrace_3231_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
else
{
uint8_t v___x_3282_; uint8_t v___x_3283_; uint8_t v___x_3284_; lean_object* v___x_3285_; uint64_t v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3282_ = 1;
v___x_3283_ = 0;
v___x_3284_ = 2;
v___x_3285_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3285_, 0, v___x_3249_);
lean_ctor_set_uint8(v___x_3285_, 1, v___x_3249_);
lean_ctor_set_uint8(v___x_3285_, 2, v___x_3249_);
lean_ctor_set_uint8(v___x_3285_, 3, v___x_3249_);
lean_ctor_set_uint8(v___x_3285_, 4, v___x_3249_);
lean_ctor_set_uint8(v___x_3285_, 5, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 6, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 7, v___x_3249_);
lean_ctor_set_uint8(v___x_3285_, 8, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 9, v___x_3282_);
lean_ctor_set_uint8(v___x_3285_, 10, v___x_3283_);
lean_ctor_set_uint8(v___x_3285_, 11, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 12, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 13, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 14, v___x_3284_);
lean_ctor_set_uint8(v___x_3285_, 15, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 16, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 17, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 18, v___x_3266_);
lean_ctor_set_uint8(v___x_3285_, 19, v___x_3249_);
v___x_3286_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set_uint64(v___x_3287_, sizeof(void*)*1, v___x_3286_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3290_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3291_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3292_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3293_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3293_, 0, v___x_3287_);
lean_ctor_set(v___x_3293_, 1, v___x_3223_);
lean_ctor_set(v___x_3293_, 2, v___x_3290_);
lean_ctor_set(v___x_3293_, 3, v___x_3291_);
lean_ctor_set(v___x_3293_, 4, v___x_3292_);
lean_ctor_set(v___x_3293_, 5, v___x_3288_);
lean_ctor_set(v___x_3293_, 6, v___x_3292_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7, v___x_3249_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 1, v___x_3249_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 2, v___x_3249_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 3, v___x_3244_);
v___x_3294_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3294_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
lean_ctor_set(v___x_3297_, 2, v___x_3223_);
lean_ctor_set(v___x_3297_, 3, v___x_3289_);
lean_ctor_set(v___x_3297_, 4, v___x_3296_);
v___x_3298_ = lean_st_mk_ref(v___x_3297_);
v___x_3299_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3239_, v___x_3244_, v___x_3293_, v___x_3298_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3293_, 7);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = lean_st_ref_get(v___x_3298_);
lean_dec(v___x_3298_);
lean_dec(v___x_3301_);
v_a_3268_ = v_a_3300_;
goto v___jp_3267_;
}
else
{
lean_dec(v___x_3298_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3302_; 
v_a_3302_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3299_, 1);
v_a_3268_ = v_a_3302_;
goto v___jp_3267_;
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
v_a_3303_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3299_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3299_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
v___jp_3267_:
{
if (lean_obj_tag(v_a_3268_) == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_box(v___x_3249_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
else
{
lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3278_; 
v_isSharedCheck_3278_ = !lean_is_exclusive(v_a_3268_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; 
v_unused_3279_ = lean_ctor_get(v_a_3268_, 0);
lean_dec(v_unused_3279_);
v___x_3272_ = v_a_3268_;
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
else
{
lean_dec(v_a_3268_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_box(v___x_3266_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set_tag(v___x_3272_, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3274_);
v___x_3276_ = v___x_3272_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
else
{
uint8_t v___x_3311_; uint8_t v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; uint64_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec(v_snd_3240_);
v___x_3311_ = 1;
v___x_3312_ = 0;
v___x_3313_ = 2;
v___x_3314_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3314_, 0, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3314_, 1, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3314_, 2, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3314_, 3, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3314_, 4, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3314_, 5, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 6, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 7, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3314_, 8, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 9, v___x_3311_);
lean_ctor_set_uint8(v___x_3314_, 10, v___x_3312_);
lean_ctor_set_uint8(v___x_3314_, 11, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 12, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 13, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 14, v___x_3313_);
lean_ctor_set_uint8(v___x_3314_, 15, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 16, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 17, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 18, v___x_3249_);
lean_ctor_set_uint8(v___x_3314_, 19, v_hasTrace_3231_);
v___x_3315_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set_uint64(v___x_3316_, sizeof(void*)*1, v___x_3315_);
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3319_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3320_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3321_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3322_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3322_, 0, v___x_3316_);
lean_ctor_set(v___x_3322_, 1, v___x_3223_);
lean_ctor_set(v___x_3322_, 2, v___x_3319_);
lean_ctor_set(v___x_3322_, 3, v___x_3320_);
lean_ctor_set(v___x_3322_, 4, v___x_3321_);
lean_ctor_set(v___x_3322_, 5, v___x_3317_);
lean_ctor_set(v___x_3322_, 6, v___x_3321_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*7, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*7 + 1, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*7 + 2, v_hasTrace_3231_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*7 + 3, v___x_3244_);
v___x_3323_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3324_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3325_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3323_);
lean_ctor_set(v___x_3326_, 1, v___x_3324_);
lean_ctor_set(v___x_3326_, 2, v___x_3223_);
lean_ctor_set(v___x_3326_, 3, v___x_3318_);
lean_ctor_set(v___x_3326_, 4, v___x_3325_);
v___x_3327_ = lean_st_mk_ref(v___x_3326_);
v___x_3328_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3239_, v___x_3322_, v___x_3327_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3322_, 7);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3330_ = lean_st_ref_get(v___x_3327_);
lean_dec(v___x_3327_);
lean_dec(v___x_3330_);
v_a_3251_ = v_a_3329_;
goto v___jp_3250_;
}
else
{
lean_dec(v___x_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3331_; 
v_a_3331_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3328_, 1);
v_a_3251_ = v_a_3331_;
goto v___jp_3250_;
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_del_object(v___x_3237_);
v_a_3332_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3328_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3328_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
v___jp_3250_:
{
if (lean_obj_tag(v_a_3251_) == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3252_ = lean_box(v_hasTrace_3231_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set_tag(v___x_3237_, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3252_);
v___x_3254_ = v___x_3237_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
else
{
lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3263_; 
lean_del_object(v___x_3237_);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_a_3251_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; 
v_unused_3264_ = lean_ctor_get(v_a_3251_, 0);
lean_dec(v_unused_3264_);
v___x_3257_ = v_a_3251_;
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
else
{
lean_dec(v_a_3251_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = lean_box(v___x_3249_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set_tag(v___x_3257_, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3259_);
v___x_3261_ = v___x_3257_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_dec(v___x_3234_);
lean_dec(v_name_3225_);
lean_dec(v___x_3223_);
v___x_3341_ = lean_box(v_hasTrace_3231_);
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
return v___x_3342_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v_a_3352_; lean_object* v___y_3365_; lean_object* v___y_3366_; uint8_t v_a_3367_; lean_object* v___y_3371_; uint8_t v___y_3372_; lean_object* v___y_3373_; uint8_t v___y_3374_; lean_object* v_a_3375_; uint8_t v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; uint8_t v___y_3380_; lean_object* v_a_3381_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v_a_3385_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v_a_3390_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v_a_3402_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v_a_3407_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3418_; uint8_t v___y_3419_; lean_object* v___y_3420_; lean_object* v_a_3421_; lean_object* v___y_3424_; uint8_t v___y_3425_; lean_object* v___y_3426_; uint8_t v___y_3427_; lean_object* v_a_3428_; 
v_inheritedTraceOptions_3343_ = lean_ctor_get(v_toCold_3229_, 11);
lean_inc(v_name_3225_);
v___f_3344_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3344_, 0, v_name_3225_);
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3346_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3347_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3343_, v_options_3230_, v___x_3347_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3557_ = l_Lean_trace_profiler;
v___x_3558_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3230_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v_env_3560_; lean_object* v___x_3561_; 
lean_dec_ref(v___f_3344_);
lean_dec_ref(v___f_3224_);
v___x_3559_ = lean_st_ref_get(v___y_3227_);
v_env_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc_ref(v_env_3560_);
lean_dec(v___x_3559_);
lean_inc(v_name_3225_);
v___x_3561_ = l_Lean_Meta_declFromEqLikeName(v_env_3560_, v_name_3225_);
if (lean_obj_tag(v___x_3561_) == 1)
{
lean_object* v_val_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3667_; 
v_val_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3667_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_val_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3667_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_fst_3566_; lean_object* v_snd_3567_; lean_object* v___x_3568_; lean_object* v_env_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_fst_3566_ = lean_ctor_get(v_val_3562_, 0);
lean_inc_n(v_fst_3566_, 2);
v_snd_3567_ = lean_ctor_get(v_val_3562_, 1);
lean_inc_n(v_snd_3567_, 2);
lean_dec(v_val_3562_);
v___x_3568_ = lean_st_ref_get(v___y_3227_);
v_env_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc_ref(v_env_3569_);
lean_dec(v___x_3568_);
v___x_3570_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3569_, v_fst_3566_, v_snd_3567_);
v___x_3571_ = lean_name_eq(v_name_3225_, v___x_3570_);
lean_dec(v___x_3570_);
lean_dec(v_name_3225_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
lean_dec(v_snd_3567_);
lean_dec(v_fst_3566_);
lean_dec(v___x_3223_);
v___x_3572_ = lean_box(v___x_3558_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set_tag(v___x_3564_, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3572_);
v___x_3574_ = v___x_3564_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
else
{
uint8_t v___x_3576_; lean_object* v_a_3578_; 
lean_inc(v_snd_3567_);
v___x_3576_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3567_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3592_; uint8_t v___x_3593_; lean_object* v_a_3595_; 
lean_del_object(v___x_3564_);
v___x_3592_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3593_ = lean_string_dec_eq(v_snd_3567_, v___x_3592_);
lean_dec(v_snd_3567_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec(v_fst_3566_);
lean_dec(v___x_3223_);
v___x_3607_ = lean_box(v___x_3558_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
else
{
uint8_t v___x_3609_; uint8_t v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; uint64_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3609_ = 1;
v___x_3610_ = 0;
v___x_3611_ = 2;
v___x_3612_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3612_, 0, v___x_3576_);
lean_ctor_set_uint8(v___x_3612_, 1, v___x_3576_);
lean_ctor_set_uint8(v___x_3612_, 2, v___x_3576_);
lean_ctor_set_uint8(v___x_3612_, 3, v___x_3576_);
lean_ctor_set_uint8(v___x_3612_, 4, v___x_3576_);
lean_ctor_set_uint8(v___x_3612_, 5, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 6, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 7, v___x_3576_);
lean_ctor_set_uint8(v___x_3612_, 8, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 9, v___x_3609_);
lean_ctor_set_uint8(v___x_3612_, 10, v___x_3610_);
lean_ctor_set_uint8(v___x_3612_, 11, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 12, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 13, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 14, v___x_3611_);
lean_ctor_set_uint8(v___x_3612_, 15, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 16, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 17, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 18, v___x_3593_);
lean_ctor_set_uint8(v___x_3612_, 19, v___x_3576_);
v___x_3613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3612_);
v___x_3614_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set_uint64(v___x_3614_, sizeof(void*)*1, v___x_3613_);
v___x_3615_ = lean_unsigned_to_nat(0u);
v___x_3616_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3617_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3618_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3619_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3620_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3620_, 0, v___x_3614_);
lean_ctor_set(v___x_3620_, 1, v___x_3223_);
lean_ctor_set(v___x_3620_, 2, v___x_3617_);
lean_ctor_set(v___x_3620_, 3, v___x_3618_);
lean_ctor_set(v___x_3620_, 4, v___x_3619_);
lean_ctor_set(v___x_3620_, 5, v___x_3615_);
lean_ctor_set(v___x_3620_, 6, v___x_3619_);
lean_ctor_set_uint8(v___x_3620_, sizeof(void*)*7, v___x_3576_);
lean_ctor_set_uint8(v___x_3620_, sizeof(void*)*7 + 1, v___x_3576_);
lean_ctor_set_uint8(v___x_3620_, sizeof(void*)*7 + 2, v___x_3576_);
lean_ctor_set_uint8(v___x_3620_, sizeof(void*)*7 + 3, v_hasTrace_3231_);
v___x_3621_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3622_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3623_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3621_);
lean_ctor_set(v___x_3624_, 1, v___x_3622_);
lean_ctor_set(v___x_3624_, 2, v___x_3223_);
lean_ctor_set(v___x_3624_, 3, v___x_3616_);
lean_ctor_set(v___x_3624_, 4, v___x_3623_);
v___x_3625_ = lean_st_mk_ref(v___x_3624_);
v___x_3626_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3566_, v_hasTrace_3231_, v___x_3620_, v___x_3625_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3620_, 7);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3628_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3626_, 1);
v___x_3628_ = lean_st_ref_get(v___x_3625_);
lean_dec(v___x_3625_);
lean_dec(v___x_3628_);
v_a_3595_ = v_a_3627_;
goto v___jp_3594_;
}
else
{
lean_dec(v___x_3625_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3629_; 
v_a_3629_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3626_, 1);
v_a_3595_ = v_a_3629_;
goto v___jp_3594_;
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
v_a_3630_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3626_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3626_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
v___jp_3594_:
{
if (lean_obj_tag(v_a_3595_) == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lean_box(v___x_3576_);
v___x_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
return v___x_3597_;
}
else
{
lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3605_; 
v_isSharedCheck_3605_ = !lean_is_exclusive(v_a_3595_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v_a_3595_, 0);
lean_dec(v_unused_3606_);
v___x_3599_ = v_a_3595_;
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
else
{
lean_dec(v_a_3595_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = lean_box(v___x_3593_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3601_);
v___x_3603_ = v___x_3599_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
}
else
{
uint8_t v___x_3638_; uint8_t v___x_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; uint64_t v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_snd_3567_);
v___x_3638_ = 1;
v___x_3639_ = 0;
v___x_3640_ = 2;
v___x_3641_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3641_, 0, v___x_3558_);
lean_ctor_set_uint8(v___x_3641_, 1, v___x_3558_);
lean_ctor_set_uint8(v___x_3641_, 2, v___x_3558_);
lean_ctor_set_uint8(v___x_3641_, 3, v___x_3558_);
lean_ctor_set_uint8(v___x_3641_, 4, v___x_3558_);
lean_ctor_set_uint8(v___x_3641_, 5, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 6, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 7, v___x_3558_);
lean_ctor_set_uint8(v___x_3641_, 8, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 9, v___x_3638_);
lean_ctor_set_uint8(v___x_3641_, 10, v___x_3639_);
lean_ctor_set_uint8(v___x_3641_, 11, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 12, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 13, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 14, v___x_3640_);
lean_ctor_set_uint8(v___x_3641_, 15, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 16, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 17, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 18, v___x_3576_);
lean_ctor_set_uint8(v___x_3641_, 19, v___x_3558_);
v___x_3642_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3641_);
v___x_3643_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3643_, 0, v___x_3641_);
lean_ctor_set_uint64(v___x_3643_, sizeof(void*)*1, v___x_3642_);
v___x_3644_ = lean_unsigned_to_nat(0u);
v___x_3645_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3646_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3647_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3648_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3649_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3649_, 0, v___x_3643_);
lean_ctor_set(v___x_3649_, 1, v___x_3223_);
lean_ctor_set(v___x_3649_, 2, v___x_3646_);
lean_ctor_set(v___x_3649_, 3, v___x_3647_);
lean_ctor_set(v___x_3649_, 4, v___x_3648_);
lean_ctor_set(v___x_3649_, 5, v___x_3644_);
lean_ctor_set(v___x_3649_, 6, v___x_3648_);
lean_ctor_set_uint8(v___x_3649_, sizeof(void*)*7, v___x_3558_);
lean_ctor_set_uint8(v___x_3649_, sizeof(void*)*7 + 1, v___x_3558_);
lean_ctor_set_uint8(v___x_3649_, sizeof(void*)*7 + 2, v___x_3558_);
lean_ctor_set_uint8(v___x_3649_, sizeof(void*)*7 + 3, v_hasTrace_3231_);
v___x_3650_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3651_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3652_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3650_);
lean_ctor_set(v___x_3653_, 1, v___x_3651_);
lean_ctor_set(v___x_3653_, 2, v___x_3223_);
lean_ctor_set(v___x_3653_, 3, v___x_3645_);
lean_ctor_set(v___x_3653_, 4, v___x_3652_);
v___x_3654_ = lean_st_mk_ref(v___x_3653_);
v___x_3655_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3566_, v___x_3649_, v___x_3654_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3649_, 7);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3657_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
v___x_3657_ = lean_st_ref_get(v___x_3654_);
lean_dec(v___x_3654_);
lean_dec(v___x_3657_);
v_a_3578_ = v_a_3656_;
goto v___jp_3577_;
}
else
{
lean_dec(v___x_3654_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3658_; 
v_a_3658_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3655_, 1);
v_a_3578_ = v_a_3658_;
goto v___jp_3577_;
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_del_object(v___x_3564_);
v_a_3659_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3655_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3655_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
v___jp_3577_:
{
if (lean_obj_tag(v_a_3578_) == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3579_ = lean_box(v___x_3558_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set_tag(v___x_3564_, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3579_);
v___x_3581_ = v___x_3564_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
else
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3590_; 
lean_del_object(v___x_3564_);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_a_3578_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; 
v_unused_3591_ = lean_ctor_get(v_a_3578_, 0);
lean_dec(v_unused_3591_);
v___x_3584_ = v_a_3578_;
v_isShared_3585_ = v_isSharedCheck_3590_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v_a_3578_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3590_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = lean_box(v___x_3576_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3586_);
v___x_3588_ = v___x_3584_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_dec(v___x_3561_);
lean_dec(v_name_3225_);
lean_dec(v___x_3223_);
v___x_3668_ = lean_box(v___x_3558_);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
return v___x_3669_;
}
}
else
{
goto v___jp_3429_;
}
}
else
{
goto v___jp_3429_;
}
v___jp_3349_:
{
lean_object* v___x_3353_; double v___x_3354_; double v___x_3355_; double v___x_3356_; double v___x_3357_; double v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3353_ = lean_io_mono_nanos_now();
v___x_3354_ = lean_float_of_nat(v___y_3351_);
v___x_3355_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3356_ = lean_float_div(v___x_3354_, v___x_3355_);
v___x_3357_ = lean_float_of_nat(v___x_3353_);
v___x_3358_ = lean_float_div(v___x_3357_, v___x_3355_);
v___x_3359_ = lean_box_float(v___x_3356_);
v___x_3360_ = lean_box_float(v___x_3358_);
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v_a_3352_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3345_, v_hasTrace_3231_, v___x_3346_, v_options_3230_, v___x_3348_, v___y_3350_, v___f_3344_, v___x_3362_, v___y_3226_, v___y_3227_);
return v___x_3363_;
}
v___jp_3364_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = lean_box(v_a_3367_);
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
v___y_3350_ = v___y_3365_;
v___y_3351_ = v___y_3366_;
v_a_3352_ = v___x_3369_;
goto v___jp_3349_;
}
v___jp_3370_:
{
if (lean_obj_tag(v_a_3375_) == 0)
{
v___y_3365_ = v___y_3371_;
v___y_3366_ = v___y_3373_;
v_a_3367_ = v___y_3374_;
goto v___jp_3364_;
}
else
{
lean_dec_ref_known(v_a_3375_, 1);
v___y_3365_ = v___y_3371_;
v___y_3366_ = v___y_3373_;
v_a_3367_ = v___y_3372_;
goto v___jp_3364_;
}
}
v___jp_3376_:
{
if (lean_obj_tag(v_a_3381_) == 0)
{
v___y_3365_ = v___y_3378_;
v___y_3366_ = v___y_3379_;
v_a_3367_ = v___y_3377_;
goto v___jp_3364_;
}
else
{
lean_dec_ref_known(v_a_3381_, 1);
v___y_3365_ = v___y_3378_;
v___y_3366_ = v___y_3379_;
v_a_3367_ = v___y_3380_;
goto v___jp_3364_;
}
}
v___jp_3382_:
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3385_);
v___y_3350_ = v___y_3383_;
v___y_3351_ = v___y_3384_;
v_a_3352_ = v___x_3386_;
goto v___jp_3349_;
}
v___jp_3387_:
{
lean_object* v___x_3391_; double v___x_3392_; double v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3391_ = lean_io_get_num_heartbeats();
v___x_3392_ = lean_float_of_nat(v___y_3388_);
v___x_3393_ = lean_float_of_nat(v___x_3391_);
v___x_3394_ = lean_box_float(v___x_3392_);
v___x_3395_ = lean_box_float(v___x_3393_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3397_, 0, v_a_3390_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3345_, v_hasTrace_3231_, v___x_3346_, v_options_3230_, v___x_3348_, v___y_3389_, v___f_3344_, v___x_3397_, v___y_3226_, v___y_3227_);
return v___x_3398_;
}
v___jp_3399_:
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v_a_3402_);
v___y_3388_ = v___y_3400_;
v___y_3389_ = v___y_3401_;
v_a_3390_ = v___x_3403_;
goto v___jp_3387_;
}
v___jp_3404_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_box(v_a_3407_);
v___x_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
v___y_3388_ = v___y_3405_;
v___y_3389_ = v___y_3406_;
v_a_3390_ = v___x_3409_;
goto v___jp_3387_;
}
v___jp_3410_:
{
if (lean_obj_tag(v___y_3413_) == 0)
{
lean_object* v_a_3414_; uint8_t v___x_3415_; 
v_a_3414_ = lean_ctor_get(v___y_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___y_3413_, 1);
v___x_3415_ = lean_unbox(v_a_3414_);
lean_dec(v_a_3414_);
v___y_3405_ = v___y_3411_;
v___y_3406_ = v___y_3412_;
v_a_3407_ = v___x_3415_;
goto v___jp_3404_;
}
else
{
lean_object* v_a_3416_; 
v_a_3416_ = lean_ctor_get(v___y_3413_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___y_3413_, 1);
v___y_3400_ = v___y_3411_;
v___y_3401_ = v___y_3412_;
v_a_3402_ = v_a_3416_;
goto v___jp_3399_;
}
}
v___jp_3417_:
{
if (lean_obj_tag(v_a_3421_) == 0)
{
uint8_t v___x_3422_; 
v___x_3422_ = 0;
v___y_3405_ = v___y_3418_;
v___y_3406_ = v___y_3420_;
v_a_3407_ = v___x_3422_;
goto v___jp_3404_;
}
else
{
lean_dec_ref_known(v_a_3421_, 1);
v___y_3405_ = v___y_3418_;
v___y_3406_ = v___y_3420_;
v_a_3407_ = v___y_3419_;
goto v___jp_3404_;
}
}
v___jp_3423_:
{
if (lean_obj_tag(v_a_3428_) == 0)
{
v___y_3405_ = v___y_3424_;
v___y_3406_ = v___y_3426_;
v_a_3407_ = v___y_3427_;
goto v___jp_3404_;
}
else
{
lean_dec_ref_known(v_a_3428_, 1);
v___y_3405_ = v___y_3424_;
v___y_3406_ = v___y_3426_;
v_a_3407_ = v___y_3425_;
goto v___jp_3404_;
}
}
v___jp_3429_:
{
lean_object* v___x_3430_; lean_object* v_a_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3430_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3227_);
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___x_3430_);
v___x_3432_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3433_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3230_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v_env_3436_; lean_object* v___x_3437_; 
lean_dec_ref(v___f_3224_);
v___x_3434_ = lean_io_mono_nanos_now();
v___x_3435_ = lean_st_ref_get(v___y_3227_);
v_env_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc_ref(v_env_3436_);
lean_dec(v___x_3435_);
lean_inc(v_name_3225_);
v___x_3437_ = l_Lean_Meta_declFromEqLikeName(v_env_3436_, v_name_3225_);
if (lean_obj_tag(v___x_3437_) == 1)
{
lean_object* v_val_3438_; lean_object* v_fst_3439_; lean_object* v_snd_3440_; lean_object* v___x_3441_; lean_object* v_env_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v_val_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_val_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v_fst_3439_ = lean_ctor_get(v_val_3438_, 0);
lean_inc_n(v_fst_3439_, 2);
v_snd_3440_ = lean_ctor_get(v_val_3438_, 1);
lean_inc_n(v_snd_3440_, 2);
lean_dec(v_val_3438_);
v___x_3441_ = lean_st_ref_get(v___y_3227_);
v_env_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc_ref(v_env_3442_);
lean_dec(v___x_3441_);
v___x_3443_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3442_, v_fst_3439_, v_snd_3440_);
v___x_3444_ = lean_name_eq(v_name_3225_, v___x_3443_);
lean_dec(v___x_3443_);
lean_dec(v_name_3225_);
if (v___x_3444_ == 0)
{
lean_dec(v_snd_3440_);
lean_dec(v_fst_3439_);
lean_dec(v___x_3223_);
v___y_3365_ = v_a_3431_;
v___y_3366_ = v___x_3434_;
v_a_3367_ = v___x_3433_;
goto v___jp_3364_;
}
else
{
uint8_t v___x_3445_; 
lean_inc(v_snd_3440_);
v___x_3445_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3440_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3446_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3447_ = lean_string_dec_eq(v_snd_3440_, v___x_3446_);
lean_dec(v_snd_3440_);
if (v___x_3447_ == 0)
{
lean_dec(v_fst_3439_);
lean_dec(v___x_3223_);
v___y_3365_ = v_a_3431_;
v___y_3366_ = v___x_3434_;
v_a_3367_ = v___x_3433_;
goto v___jp_3364_;
}
else
{
uint8_t v___x_3448_; uint8_t v___x_3449_; uint8_t v___x_3450_; lean_object* v___x_3451_; uint64_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3448_ = 1;
v___x_3449_ = 0;
v___x_3450_ = 2;
v___x_3451_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3451_, 0, v___x_3445_);
lean_ctor_set_uint8(v___x_3451_, 1, v___x_3445_);
lean_ctor_set_uint8(v___x_3451_, 2, v___x_3445_);
lean_ctor_set_uint8(v___x_3451_, 3, v___x_3445_);
lean_ctor_set_uint8(v___x_3451_, 4, v___x_3445_);
lean_ctor_set_uint8(v___x_3451_, 5, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 6, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 7, v___x_3445_);
lean_ctor_set_uint8(v___x_3451_, 8, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 9, v___x_3448_);
lean_ctor_set_uint8(v___x_3451_, 10, v___x_3449_);
lean_ctor_set_uint8(v___x_3451_, 11, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 12, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 13, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 14, v___x_3450_);
lean_ctor_set_uint8(v___x_3451_, 15, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 16, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 17, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 18, v___x_3447_);
lean_ctor_set_uint8(v___x_3451_, 19, v___x_3445_);
v___x_3452_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3451_);
v___x_3453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set_uint64(v___x_3453_, sizeof(void*)*1, v___x_3452_);
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3458_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3459_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3459_, 0, v___x_3453_);
lean_ctor_set(v___x_3459_, 1, v___x_3223_);
lean_ctor_set(v___x_3459_, 2, v___x_3456_);
lean_ctor_set(v___x_3459_, 3, v___x_3457_);
lean_ctor_set(v___x_3459_, 4, v___x_3458_);
lean_ctor_set(v___x_3459_, 5, v___x_3454_);
lean_ctor_set(v___x_3459_, 6, v___x_3458_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7, v___x_3445_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7 + 1, v___x_3445_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7 + 2, v___x_3445_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*7 + 3, v_hasTrace_3231_);
v___x_3460_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3461_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3462_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3460_);
lean_ctor_set(v___x_3463_, 1, v___x_3461_);
lean_ctor_set(v___x_3463_, 2, v___x_3223_);
lean_ctor_set(v___x_3463_, 3, v___x_3455_);
lean_ctor_set(v___x_3463_, 4, v___x_3462_);
v___x_3464_ = lean_st_mk_ref(v___x_3463_);
v___x_3465_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3439_, v_hasTrace_3231_, v___x_3459_, v___x_3464_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3459_, 7);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = lean_st_ref_get(v___x_3464_);
lean_dec(v___x_3464_);
lean_dec(v___x_3467_);
v___y_3371_ = v_a_3431_;
v___y_3372_ = v___x_3447_;
v___y_3373_ = v___x_3434_;
v___y_3374_ = v___x_3445_;
v_a_3375_ = v_a_3466_;
goto v___jp_3370_;
}
else
{
lean_dec(v___x_3464_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3468_; 
v_a_3468_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3465_, 1);
v___y_3371_ = v_a_3431_;
v___y_3372_ = v___x_3447_;
v___y_3373_ = v___x_3434_;
v___y_3374_ = v___x_3445_;
v_a_3375_ = v_a_3468_;
goto v___jp_3370_;
}
else
{
lean_object* v_a_3469_; 
v_a_3469_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3469_);
lean_dec_ref_known(v___x_3465_, 1);
v___y_3383_ = v_a_3431_;
v___y_3384_ = v___x_3434_;
v_a_3385_ = v_a_3469_;
goto v___jp_3382_;
}
}
}
}
else
{
uint8_t v___x_3470_; uint8_t v___x_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; uint64_t v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v_snd_3440_);
v___x_3470_ = 1;
v___x_3471_ = 0;
v___x_3472_ = 2;
v___x_3473_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3473_, 0, v___x_3433_);
lean_ctor_set_uint8(v___x_3473_, 1, v___x_3433_);
lean_ctor_set_uint8(v___x_3473_, 2, v___x_3433_);
lean_ctor_set_uint8(v___x_3473_, 3, v___x_3433_);
lean_ctor_set_uint8(v___x_3473_, 4, v___x_3433_);
lean_ctor_set_uint8(v___x_3473_, 5, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 6, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 7, v___x_3433_);
lean_ctor_set_uint8(v___x_3473_, 8, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 9, v___x_3470_);
lean_ctor_set_uint8(v___x_3473_, 10, v___x_3471_);
lean_ctor_set_uint8(v___x_3473_, 11, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 12, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 13, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 14, v___x_3472_);
lean_ctor_set_uint8(v___x_3473_, 15, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 16, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 17, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 18, v___x_3445_);
lean_ctor_set_uint8(v___x_3473_, 19, v___x_3433_);
v___x_3474_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3473_);
v___x_3475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set_uint64(v___x_3475_, sizeof(void*)*1, v___x_3474_);
v___x_3476_ = lean_unsigned_to_nat(0u);
v___x_3477_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3478_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3479_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3480_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3481_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3481_, 0, v___x_3475_);
lean_ctor_set(v___x_3481_, 1, v___x_3223_);
lean_ctor_set(v___x_3481_, 2, v___x_3478_);
lean_ctor_set(v___x_3481_, 3, v___x_3479_);
lean_ctor_set(v___x_3481_, 4, v___x_3480_);
lean_ctor_set(v___x_3481_, 5, v___x_3476_);
lean_ctor_set(v___x_3481_, 6, v___x_3480_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7, v___x_3433_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7 + 1, v___x_3433_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7 + 2, v___x_3433_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7 + 3, v_hasTrace_3231_);
v___x_3482_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3483_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3482_);
lean_ctor_set(v___x_3485_, 1, v___x_3483_);
lean_ctor_set(v___x_3485_, 2, v___x_3223_);
lean_ctor_set(v___x_3485_, 3, v___x_3477_);
lean_ctor_set(v___x_3485_, 4, v___x_3484_);
v___x_3486_ = lean_st_mk_ref(v___x_3485_);
v___x_3487_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3439_, v___x_3481_, v___x_3486_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3481_, 7);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = lean_st_ref_get(v___x_3486_);
lean_dec(v___x_3486_);
lean_dec(v___x_3489_);
v___y_3377_ = v___x_3433_;
v___y_3378_ = v_a_3431_;
v___y_3379_ = v___x_3434_;
v___y_3380_ = v___x_3445_;
v_a_3381_ = v_a_3488_;
goto v___jp_3376_;
}
else
{
lean_dec(v___x_3486_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3490_; 
v_a_3490_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3487_, 1);
v___y_3377_ = v___x_3433_;
v___y_3378_ = v_a_3431_;
v___y_3379_ = v___x_3434_;
v___y_3380_ = v___x_3445_;
v_a_3381_ = v_a_3490_;
goto v___jp_3376_;
}
else
{
lean_object* v_a_3491_; 
v_a_3491_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3487_, 1);
v___y_3383_ = v_a_3431_;
v___y_3384_ = v___x_3434_;
v_a_3385_ = v_a_3491_;
goto v___jp_3382_;
}
}
}
}
}
else
{
lean_dec(v___x_3437_);
lean_dec(v_name_3225_);
lean_dec(v___x_3223_);
v___y_3365_ = v_a_3431_;
v___y_3366_ = v___x_3434_;
v_a_3367_ = v___x_3433_;
goto v___jp_3364_;
}
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v_env_3494_; lean_object* v___x_3495_; 
v___x_3492_ = lean_io_get_num_heartbeats();
v___x_3493_ = lean_st_ref_get(v___y_3227_);
v_env_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc_ref(v_env_3494_);
lean_dec(v___x_3493_);
lean_inc(v_name_3225_);
v___x_3495_ = l_Lean_Meta_declFromEqLikeName(v_env_3494_, v_name_3225_);
if (lean_obj_tag(v___x_3495_) == 1)
{
lean_object* v_val_3496_; lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3499_; lean_object* v_env_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v_val_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_val_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v_fst_3497_ = lean_ctor_get(v_val_3496_, 0);
lean_inc_n(v_fst_3497_, 2);
v_snd_3498_ = lean_ctor_get(v_val_3496_, 1);
lean_inc_n(v_snd_3498_, 2);
lean_dec(v_val_3496_);
v___x_3499_ = lean_st_ref_get(v___y_3227_);
v_env_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc_ref(v_env_3500_);
lean_dec(v___x_3499_);
v___x_3501_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3500_, v_fst_3497_, v_snd_3498_);
v___x_3502_ = lean_name_eq(v_name_3225_, v___x_3501_);
lean_dec(v___x_3501_);
lean_dec(v_name_3225_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v___x_3223_);
v___x_3503_ = lean_box(0);
lean_inc(v___y_3227_);
lean_inc_ref(v___y_3226_);
v___x_3504_ = lean_apply_4(v___f_3224_, v___x_3503_, v___y_3226_, v___y_3227_, lean_box(0));
v___y_3411_ = v___x_3492_;
v___y_3412_ = v_a_3431_;
v___y_3413_ = v___x_3504_;
goto v___jp_3410_;
}
else
{
uint8_t v___x_3505_; 
lean_inc(v_snd_3498_);
v___x_3505_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3498_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3506_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3507_ = lean_string_dec_eq(v_snd_3498_, v___x_3506_);
lean_dec(v_snd_3498_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
lean_dec(v_fst_3497_);
lean_dec(v___x_3223_);
v___x_3508_ = lean_box(0);
lean_inc(v___y_3227_);
lean_inc_ref(v___y_3226_);
v___x_3509_ = lean_apply_4(v___f_3224_, v___x_3508_, v___y_3226_, v___y_3227_, lean_box(0));
v___y_3411_ = v___x_3492_;
v___y_3412_ = v_a_3431_;
v___y_3413_ = v___x_3509_;
goto v___jp_3410_;
}
else
{
uint8_t v___x_3510_; uint8_t v___x_3511_; uint8_t v___x_3512_; lean_object* v___x_3513_; uint64_t v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_dec_ref(v___f_3224_);
v___x_3510_ = 1;
v___x_3511_ = 0;
v___x_3512_ = 2;
v___x_3513_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3513_, 0, v___x_3505_);
lean_ctor_set_uint8(v___x_3513_, 1, v___x_3505_);
lean_ctor_set_uint8(v___x_3513_, 2, v___x_3505_);
lean_ctor_set_uint8(v___x_3513_, 3, v___x_3505_);
lean_ctor_set_uint8(v___x_3513_, 4, v___x_3505_);
lean_ctor_set_uint8(v___x_3513_, 5, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 6, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 7, v___x_3505_);
lean_ctor_set_uint8(v___x_3513_, 8, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 9, v___x_3510_);
lean_ctor_set_uint8(v___x_3513_, 10, v___x_3511_);
lean_ctor_set_uint8(v___x_3513_, 11, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 12, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 13, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 14, v___x_3512_);
lean_ctor_set_uint8(v___x_3513_, 15, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 16, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 17, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 18, v___x_3507_);
lean_ctor_set_uint8(v___x_3513_, 19, v___x_3505_);
v___x_3514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3513_);
v___x_3515_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3515_, 0, v___x_3513_);
lean_ctor_set_uint64(v___x_3515_, sizeof(void*)*1, v___x_3514_);
v___x_3516_ = lean_unsigned_to_nat(0u);
v___x_3517_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3518_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3519_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3520_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3521_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3521_, 0, v___x_3515_);
lean_ctor_set(v___x_3521_, 1, v___x_3223_);
lean_ctor_set(v___x_3521_, 2, v___x_3518_);
lean_ctor_set(v___x_3521_, 3, v___x_3519_);
lean_ctor_set(v___x_3521_, 4, v___x_3520_);
lean_ctor_set(v___x_3521_, 5, v___x_3516_);
lean_ctor_set(v___x_3521_, 6, v___x_3520_);
lean_ctor_set_uint8(v___x_3521_, sizeof(void*)*7, v___x_3505_);
lean_ctor_set_uint8(v___x_3521_, sizeof(void*)*7 + 1, v___x_3505_);
lean_ctor_set_uint8(v___x_3521_, sizeof(void*)*7 + 2, v___x_3505_);
lean_ctor_set_uint8(v___x_3521_, sizeof(void*)*7 + 3, v___x_3433_);
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3523_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3524_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3522_);
lean_ctor_set(v___x_3525_, 1, v___x_3523_);
lean_ctor_set(v___x_3525_, 2, v___x_3223_);
lean_ctor_set(v___x_3525_, 3, v___x_3517_);
lean_ctor_set(v___x_3525_, 4, v___x_3524_);
v___x_3526_ = lean_st_mk_ref(v___x_3525_);
v___x_3527_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3497_, v___x_3433_, v___x_3521_, v___x_3526_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3521_, 7);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3529_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___x_3527_, 1);
v___x_3529_ = lean_st_ref_get(v___x_3526_);
lean_dec(v___x_3526_);
lean_dec(v___x_3529_);
v___y_3424_ = v___x_3492_;
v___y_3425_ = v___x_3507_;
v___y_3426_ = v_a_3431_;
v___y_3427_ = v___x_3505_;
v_a_3428_ = v_a_3528_;
goto v___jp_3423_;
}
else
{
lean_dec(v___x_3526_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3530_; 
v_a_3530_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3527_, 1);
v___y_3424_ = v___x_3492_;
v___y_3425_ = v___x_3507_;
v___y_3426_ = v_a_3431_;
v___y_3427_ = v___x_3505_;
v_a_3428_ = v_a_3530_;
goto v___jp_3423_;
}
else
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3527_, 1);
v___y_3400_ = v___x_3492_;
v___y_3401_ = v_a_3431_;
v_a_3402_ = v_a_3531_;
goto v___jp_3399_;
}
}
}
}
else
{
uint8_t v___x_3532_; uint8_t v___x_3533_; uint8_t v___x_3534_; uint8_t v___x_3535_; lean_object* v___x_3536_; uint64_t v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec(v_snd_3498_);
lean_dec_ref(v___f_3224_);
v___x_3532_ = 0;
v___x_3533_ = 1;
v___x_3534_ = 0;
v___x_3535_ = 2;
v___x_3536_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3536_, 0, v___x_3532_);
lean_ctor_set_uint8(v___x_3536_, 1, v___x_3532_);
lean_ctor_set_uint8(v___x_3536_, 2, v___x_3532_);
lean_ctor_set_uint8(v___x_3536_, 3, v___x_3532_);
lean_ctor_set_uint8(v___x_3536_, 4, v___x_3532_);
lean_ctor_set_uint8(v___x_3536_, 5, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 6, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 7, v___x_3532_);
lean_ctor_set_uint8(v___x_3536_, 8, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 9, v___x_3533_);
lean_ctor_set_uint8(v___x_3536_, 10, v___x_3534_);
lean_ctor_set_uint8(v___x_3536_, 11, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 12, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 13, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 14, v___x_3535_);
lean_ctor_set_uint8(v___x_3536_, 15, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 16, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 17, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 18, v___x_3505_);
lean_ctor_set_uint8(v___x_3536_, 19, v___x_3532_);
v___x_3537_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3536_);
v___x_3538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set_uint64(v___x_3538_, sizeof(void*)*1, v___x_3537_);
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3541_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3542_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3543_ = lean_box(0);
lean_inc(v___x_3223_);
v___x_3544_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3544_, 0, v___x_3538_);
lean_ctor_set(v___x_3544_, 1, v___x_3223_);
lean_ctor_set(v___x_3544_, 2, v___x_3541_);
lean_ctor_set(v___x_3544_, 3, v___x_3542_);
lean_ctor_set(v___x_3544_, 4, v___x_3543_);
lean_ctor_set(v___x_3544_, 5, v___x_3539_);
lean_ctor_set(v___x_3544_, 6, v___x_3543_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*7, v___x_3532_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*7 + 1, v___x_3532_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*7 + 2, v___x_3532_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*7 + 3, v___x_3433_);
v___x_3545_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3546_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3545_);
lean_ctor_set(v___x_3548_, 1, v___x_3546_);
lean_ctor_set(v___x_3548_, 2, v___x_3223_);
lean_ctor_set(v___x_3548_, 3, v___x_3540_);
lean_ctor_set(v___x_3548_, 4, v___x_3547_);
v___x_3549_ = lean_st_mk_ref(v___x_3548_);
v___x_3550_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3497_, v___x_3544_, v___x_3549_, v___y_3226_, v___y_3227_);
lean_dec_ref_known(v___x_3544_, 7);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3552_ = lean_st_ref_get(v___x_3549_);
lean_dec(v___x_3549_);
lean_dec(v___x_3552_);
v___y_3418_ = v___x_3492_;
v___y_3419_ = v___x_3505_;
v___y_3420_ = v_a_3431_;
v_a_3421_ = v_a_3551_;
goto v___jp_3417_;
}
else
{
lean_dec(v___x_3549_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3550_, 1);
v___y_3418_ = v___x_3492_;
v___y_3419_ = v___x_3505_;
v___y_3420_ = v_a_3431_;
v_a_3421_ = v_a_3553_;
goto v___jp_3417_;
}
else
{
lean_object* v_a_3554_; 
v_a_3554_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3550_, 1);
v___y_3400_ = v___x_3492_;
v___y_3401_ = v_a_3431_;
v_a_3402_ = v_a_3554_;
goto v___jp_3399_;
}
}
}
}
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec(v___x_3495_);
lean_dec(v_name_3225_);
lean_dec(v___x_3223_);
v___x_3555_ = lean_box(0);
lean_inc(v___y_3227_);
lean_inc_ref(v___y_3226_);
v___x_3556_ = lean_apply_4(v___f_3224_, v___x_3555_, v___y_3226_, v___y_3227_, lean_box(0));
v___y_3411_ = v___x_3492_;
v___y_3412_ = v_a_3431_;
v___y_3413_ = v___x_3556_;
goto v___jp_3410_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3223_ = stack[0].m_obj;
lean_object* v___f_3224_ = stack[1].m_obj;
lean_object* v_name_3225_ = stack[2].m_obj;
lean_object* v___y_3226_ = stack[3].m_obj;
lean_object* v___y_3227_ = stack[4].m_obj;
lean_object* v_res_3670_;
v_res_3670_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3223_, v___f_3224_, v_name_3225_, v___y_3226_, v___y_3227_);
stack->m_obj
 = v_res_3670_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3671_, lean_object* v___f_3672_, lean_object* v_name_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3671_, v___f_3672_, v_name_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
return v_res_3677_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_unsigned_to_nat(3137104340u);
v___x_3723_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3724_ = l_Lean_Name_num___override(v___x_3723_, v___x_3722_);
return v___x_3724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3727_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3728_ = l_Lean_Name_str___override(v___x_3727_, v___x_3726_);
return v___x_3728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3730_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3731_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3732_ = l_Lean_Name_str___override(v___x_3731_, v___x_3730_);
return v___x_3732_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3733_ = lean_unsigned_to_nat(2u);
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3735_ = l_Lean_Name_num___override(v___x_3734_, v___x_3733_);
return v___x_3735_;
}
}
lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3737_; lean_object* v___x_3738_; 
v___f_3737_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3738_ = l_Lean_registerReservedNameAction(v___f_3737_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v___x_3739_; uint8_t v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_dec_ref_known(v___x_3738_, 1);
v___x_3739_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3740_ = 0;
v___x_3741_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3742_ = l_Lean_registerTraceClass(v___x_3739_, v___x_3740_, v___x_3741_);
return v___x_3742_;
}
else
{
return v___x_3738_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3743_;
v_res_3743_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3743_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3745_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3747_);
return v___x_3751_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3747_ = stack[1].m_obj;
lean_object* v___y_3748_ = stack[2].m_obj;
lean_object* v___y_3749_ = stack[3].m_obj;
lean_object* v_res_3752_;
v_res_3752_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_box(0), v_x_3747_, v___y_3748_, v___y_3749_);
stack->m_obj
 = v_res_3752_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3753_, lean_object* v_x_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3753_, v_x_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3758_;
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
