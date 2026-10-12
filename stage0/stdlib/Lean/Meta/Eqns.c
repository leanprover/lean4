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
lean_object* v___x_176_; lean_object* v___y_178_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_194_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v___x_193_, v_s_175_);
v___x_195_ = lean_array_get_size(v___x_194_);
v___x_196_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_197_ = lean_nat_dec_lt(v___x_176_, v___x_195_);
if (v___x_197_ == 0)
{
lean_dec_ref(v___x_194_);
v___y_178_ = v___x_196_;
goto v___jp_177_;
}
else
{
uint8_t v___x_198_; 
v___x_198_ = lean_nat_dec_le(v___x_195_, v___x_195_);
if (v___x_198_ == 0)
{
if (v___x_197_ == 0)
{
lean_dec_ref(v___x_194_);
v___y_178_ = v___x_196_;
goto v___jp_177_;
}
else
{
size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((size_t)0ULL);
v___x_200_ = lean_usize_of_nat(v___x_195_);
lean_inc_ref(v_env_174_);
v___x_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_174_, v___x_194_, v___x_199_, v___x_200_, v___x_196_);
lean_dec_ref(v___x_194_);
v___y_178_ = v___x_201_;
goto v___jp_177_;
}
}
else
{
size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_195_);
lean_inc_ref(v_env_174_);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__2(v_env_174_, v___x_194_, v___x_202_, v___x_203_, v___x_196_);
lean_dec_ref(v___x_194_);
v___y_178_ = v___x_204_;
goto v___jp_177_;
}
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
uint8_t v___x_183_; 
v___x_183_ = lean_nat_dec_le(v___x_179_, v___x_179_);
if (v___x_183_ == 0)
{
if (v___x_181_ == 0)
{
lean_object* v___x_184_; 
lean_dec_ref(v_env_174_);
v___x_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_180_);
lean_ctor_set(v___x_184_, 1, v___x_180_);
lean_ctor_set(v___x_184_, 2, v___y_178_);
return v___x_184_;
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_179_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_174_, v___y_178_, v___x_185_, v___x_186_, v___x_180_);
lean_inc_ref(v___x_187_);
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
lean_ctor_set(v___x_188_, 2, v___y_178_);
return v___x_188_;
}
}
else
{
size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = ((size_t)0ULL);
v___x_190_ = lean_usize_of_nat(v___x_179_);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_174_, v___y_178_, v___x_189_, v___x_190_, v___x_180_);
lean_inc_ref(v___x_191_);
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_ctor_set(v___x_192_, 2, v___y_178_);
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_env_205_, lean_object* v_s_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(v_env_205_, v_s_206_);
lean_dec(v_s_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; 
v___f_215_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_217_ = lean_box(1);
v___x_218_ = 0;
v___x_219_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_216_, v___x_217_, v___x_218_, v___f_215_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object* v_init_222_, lean_object* v_t_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_222_, v_t_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_225_, lean_object* v_t_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_225_, v_t_226_);
lean_dec(v_t_226_);
return v_res_227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_235_ = lean_string_utf8_byte_size(v_s_234_);
v___x_236_ = lean_unsigned_to_nat(3u);
v___x_237_ = lean_nat_dec_le(v___x_236_, v___x_235_);
if (v___x_237_ == 0)
{
lean_dec_ref(v_s_234_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_string_memcmp(v_s_234_, v___x_238_, v___x_239_, v___x_239_, v___x_236_);
if (v___x_240_ == 0)
{
lean_dec_ref(v_s_234_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
lean_inc_ref(v_s_234_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_s_234_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_235_);
v___x_242_ = l_String_Slice_Pos_nextn(v___x_241_, v___x_239_, v___x_236_);
lean_dec_ref_known(v___x_241_, 3);
v___x_243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_243_, 0, v_s_234_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_ctor_set(v___x_243_, 2, v___x_235_);
v___x_244_ = l_String_Slice_isNat(v___x_243_);
lean_dec_ref_known(v___x_243_, 3);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_252_){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_254_ = lean_string_dec_eq(v_s_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_256_ = lean_string_dec_eq(v_s_252_, v___x_255_);
if (v___x_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_252_);
return v___x_257_;
}
else
{
lean_dec_ref(v_s_252_);
return v___x_256_;
}
}
else
{
lean_dec_ref(v_s_252_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_Meta_isEqnLikeSuffix(v_s_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_264_, lean_object* v_env_265_, uint8_t v___x_266_, lean_object* v_as_x27_267_, lean_object* v_b_268_){
_start:
{
if (lean_obj_tag(v_as_x27_267_) == 0)
{
lean_dec_ref(v_env_265_);
lean_dec_ref(v_str_264_);
lean_inc_ref(v_b_268_);
return v_b_268_;
}
else
{
lean_object* v_head_269_; lean_object* v_tail_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___y_274_; uint8_t v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_head_269_ = lean_ctor_get(v_as_x27_267_, 0);
v_tail_270_ = lean_ctor_get(v_as_x27_267_, 1);
v___x_271_ = lean_box(0);
v___x_272_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_280_ = 0;
lean_inc_ref(v_env_265_);
v___x_281_ = l_Lean_Environment_setExporting(v_env_265_, v___x_280_);
lean_inc(v_head_269_);
v___x_282_ = l_Lean_Environment_isSafeDefinition(v___x_281_, v_head_269_);
if (v___x_282_ == 0)
{
v___y_274_ = v___x_282_;
goto v___jp_273_;
}
else
{
uint8_t v___x_283_; 
lean_inc(v_head_269_);
lean_inc_ref(v_env_265_);
v___x_283_ = l_Lean_Meta_isMatcherCore(v_env_265_, v_head_269_);
if (v___x_283_ == 0)
{
v___y_274_ = v___x_266_;
goto v___jp_273_;
}
else
{
v_as_x27_267_ = v_tail_270_;
v_b_268_ = v___x_272_;
goto _start;
}
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
v_as_x27_267_ = v_tail_270_;
v_b_268_ = v___x_272_;
goto _start;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref(v_env_265_);
lean_inc(v_head_269_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v_head_269_);
lean_ctor_set(v___x_276_, 1, v_str_264_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_271_);
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_285_, lean_object* v_env_286_, lean_object* v___x_287_, lean_object* v_as_x27_288_, lean_object* v_b_289_){
_start:
{
uint8_t v___x_616__boxed_290_; lean_object* v_res_291_; 
v___x_616__boxed_290_ = lean_unbox(v___x_287_);
v_res_291_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_285_, v_env_286_, v___x_616__boxed_290_, v_as_x27_288_, v_b_289_);
lean_dec_ref(v_b_289_);
lean_dec(v_as_x27_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_292_, lean_object* v_name_293_){
_start:
{
if (lean_obj_tag(v_name_293_) == 1)
{
lean_object* v_pre_294_; lean_object* v_str_295_; uint8_t v___x_296_; 
v_pre_294_ = lean_ctor_get(v_name_293_, 0);
lean_inc(v_pre_294_);
v_str_295_ = lean_ctor_get(v_name_293_, 1);
lean_inc_ref_n(v_str_295_, 2);
lean_dec_ref_known(v_name_293_, 2);
v___x_296_ = l_Lean_Meta_isEqnLikeSuffix(v_str_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v_str_295_);
lean_dec(v_pre_294_);
lean_dec_ref(v_env_292_);
v___x_297_ = lean_box(0);
return v___x_297_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_fst_305_; 
lean_inc(v_pre_294_);
v___x_298_ = l_Lean_privateToUserName(v_pre_294_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v_pre_294_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_304_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_295_, v_env_292_, v___x_296_, v___x_301_, v___x_303_);
lean_dec_ref_known(v___x_301_, 2);
v_fst_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_fst_305_);
lean_dec_ref(v___x_304_);
if (lean_obj_tag(v_fst_305_) == 0)
{
return v___x_302_;
}
else
{
lean_object* v_val_306_; 
v_val_306_ = lean_ctor_get(v_fst_305_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v_fst_305_, 1);
return v_val_306_;
}
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_name_293_);
lean_dec_ref(v_env_292_);
v___x_307_ = lean_box(0);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_308_, lean_object* v_env_309_, uint8_t v___x_310_, lean_object* v_as_311_, lean_object* v_as_x27_312_, lean_object* v_b_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_308_, v_env_309_, v___x_310_, v_as_x27_312_, v_b_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_316_, lean_object* v_env_317_, lean_object* v___x_318_, lean_object* v_as_319_, lean_object* v_as_x27_320_, lean_object* v_b_321_, lean_object* v_a_322_){
_start:
{
uint8_t v___x_687__boxed_323_; lean_object* v_res_324_; 
v___x_687__boxed_323_ = lean_unbox(v___x_318_);
v_res_324_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_316_, v_env_317_, v___x_687__boxed_323_, v_as_319_, v_as_x27_320_, v_b_321_, v_a_322_);
lean_dec_ref(v_b_321_);
lean_dec(v_as_x27_320_);
lean_dec(v_as_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_325_, lean_object* v_declName_326_, lean_object* v_suffix_327_){
_start:
{
uint8_t v_isExposed_328_; lean_object* v_name_329_; 
lean_inc(v_declName_326_);
lean_inc_ref(v_env_325_);
v_isExposed_328_ = l_Lean_Environment_hasExposedBody(v_env_325_, v_declName_326_);
v_name_329_ = l_Lean_Name_str___override(v_declName_326_, v_suffix_327_);
if (v_isExposed_328_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_mkPrivateName(v_env_325_, v_name_329_);
lean_dec_ref(v_env_325_);
return v___x_330_;
}
else
{
lean_dec_ref(v_env_325_);
return v_name_329_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_331_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v___x_335_);
lean_ctor_set(v___x_337_, 5, v___x_335_);
lean_ctor_set(v___x_337_, 6, v___x_335_);
lean_ctor_set(v___x_337_, 7, v___x_335_);
lean_ctor_set(v___x_337_, 8, v___x_335_);
lean_ctor_set(v___x_337_, 9, v___x_335_);
lean_ctor_set(v___x_337_, 10, v___x_335_);
lean_ctor_set(v___x_337_, 11, v___x_334_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(32u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_341_ = ((size_t)5ULL);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_unsigned_to_nat(32u);
v___x_344_ = lean_mk_empty_array_with_capacity(v___x_343_);
v___x_345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_346_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_342_);
lean_ctor_set(v___x_346_, 3, v___x_342_);
lean_ctor_set_usize(v___x_346_, 4, v___x_341_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_box(1);
v___x_348_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_349_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_toCold_356_; lean_object* v_env_357_; lean_object* v_options_358_; uint8_t v___x_359_; lean_object* v_env_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_toCold_356_ = lean_ctor_get(v___y_352_, 0);
v_env_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_355_);
v_options_358_ = lean_ctor_get(v_toCold_356_, 2);
v___x_359_ = 0;
v_env_360_ = l_Lean_Environment_setRecordingDeps(v_env_357_, v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_362_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_358_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_env_360_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
lean_ctor_set(v___x_363_, 3, v_options_358_);
v___x_364_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_msgData_351_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_ref_375_; lean_object* v___x_376_; lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v_ref_375_ = lean_ctor_get(v___y_372_, 2);
v___x_376_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_371_, v___y_372_, v___y_373_);
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_inc(v_ref_375_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_ref_375_);
lean_ctor_set(v___x_381_, 1, v_a_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 1);
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_390_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_400_, lean_object* v_reservedName_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_405_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_406_ = 0;
v___x_407_ = l_Lean_MessageData_ofConstName(v_declName_400_, v___x_406_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = 1;
v___x_412_ = l_Lean_MessageData_ofConstName(v_reservedName_401_, v___x_411_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_410_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_415_, v___y_402_, v___y_403_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_417_, lean_object* v_reservedName_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_417_, v_reservedName_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_423_, lean_object* v_suffix_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_reservedName_428_; lean_object* v___x_429_; lean_object* v_env_430_; uint8_t v___x_431_; uint8_t v___x_432_; 
lean_inc(v_declName_423_);
v_reservedName_428_ = l_Lean_Name_str___override(v_declName_423_, v_suffix_424_);
v___x_429_ = lean_st_ref_get(v___y_426_);
v_env_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_env_430_);
lean_dec(v___x_429_);
v___x_431_ = 1;
lean_inc(v_reservedName_428_);
v___x_432_ = l_Lean_Environment_contains(v_env_430_, v_reservedName_428_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_reservedName_428_);
lean_dec(v_declName_423_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_423_, v_reservedName_428_, v___y_425_, v___y_426_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_436_, lean_object* v_suffix_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_436_, v_suffix_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_442_);
v___x_447_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_442_, v___x_446_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_448_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_442_);
v___x_449_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_442_, v___x_448_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref_known(v___x_449_, 1);
v___x_450_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_451_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_442_, v___x_450_, v_a_443_, v_a_444_);
return v___x_451_;
}
else
{
lean_dec(v_declName_442_);
return v___x_449_;
}
}
else
{
lean_dec(v_declName_442_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_457_, lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_458_, v___y_459_, v___y_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_463_, v_msg_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_468_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_469_, lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; 
lean_inc(v_n_470_);
lean_inc_ref(v_env_469_);
v___x_471_ = l_Lean_Meta_declFromEqLikeName(v_env_469_, v_n_470_);
if (lean_obj_tag(v___x_471_) == 1)
{
lean_object* v_val_472_; lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_471_, 1);
v_fst_473_ = lean_ctor_get(v_val_472_, 0);
lean_inc(v_fst_473_);
v_snd_474_ = lean_ctor_get(v_val_472_, 1);
lean_inc(v_snd_474_);
lean_dec(v_val_472_);
v___x_475_ = l_Lean_Meta_mkEqLikeNameFor(v_env_469_, v_fst_473_, v_snd_474_);
v___x_476_ = lean_name_eq(v_n_470_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v_n_470_);
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
lean_dec(v___x_471_);
lean_dec(v_n_470_);
lean_dec_ref(v_env_469_);
v___x_477_ = 0;
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_478_, lean_object* v_n_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_478_, v_n_479_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; 
v___f_484_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_485_ = l_Lean_registerReservedNamePredicate(v___f_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = lean_st_mk_ref(v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_493_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_496_ = lean_mk_io_user_error(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_497_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_initializing();
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v_f_497_);
v___x_500_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_502_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_503_ = lean_st_ref_take(v___x_502_);
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v_f_497_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_st_ref_put(v___x_502_, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_registerGetEqnsFn(v_f_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_520_; lean_object* v_env_521_; uint8_t v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_st_ref_get(v_a_514_);
v_env_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_env_521_);
lean_dec(v___x_520_);
v___x_522_ = 0;
lean_inc(v_declName_510_);
v___x_523_ = l_Lean_Environment_findAsync_x3f(v_env_521_, v_declName_510_, v___x_522_);
if (lean_obj_tag(v___x_523_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_555_; 
v_val_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_555_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_555_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_555_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v_kind_528_; 
v_kind_528_ = lean_ctor_get_uint8(v_val_524_, sizeof(void*)*3);
if (v_kind_528_ == 0)
{
lean_object* v_sig_529_; lean_object* v___x_530_; lean_object* v_env_531_; uint8_t v___x_532_; 
v_sig_529_ = lean_ctor_get(v_val_524_, 1);
lean_inc_ref(v_sig_529_);
lean_dec(v_val_524_);
v___x_530_ = lean_st_ref_get(v_a_514_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_530_);
v___x_532_ = l_Lean_Meta_isMatcherCore(v_env_531_, v_declName_510_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v_type_534_; lean_object* v___x_535_; 
lean_del_object(v___x_526_);
v___x_533_ = lean_task_get_own(v_sig_529_);
v_type_534_ = lean_ctor_get(v___x_533_, 2);
lean_inc_ref(v_type_534_);
lean_dec(v___x_533_);
v___x_535_ = l_Lean_Meta_isProp(v_type_534_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_550_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_550_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_550_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_550_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_a_536_);
lean_dec(v_a_536_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = 1;
v___x_542_ = lean_box(v___x_541_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_542_);
v___x_544_ = v___x_538_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_box(v___x_532_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_546_);
v___x_548_ = v___x_538_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
return v___x_535_;
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec_ref(v_sig_529_);
v___x_551_ = lean_box(v___x_522_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
lean_ctor_set(v___x_526_, 0, v___x_551_);
v___x_553_ = v___x_526_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_del_object(v___x_526_);
lean_dec(v_val_524_);
lean_dec(v_declName_510_);
goto v___jp_516_;
}
}
}
else
{
lean_dec(v___x_523_);
lean_dec(v_declName_510_);
goto v___jp_516_;
}
v___jp_516_:
{
uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = 0;
v___x_518_ = lean_box(v___x_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object* v___x_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v___x_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_570_);
return v_res_572_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_573_; lean_object* v___f_574_; 
v___x_573_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_574_, 0, v___x_573_);
return v___f_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v___f_581_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_box(1);
v___x_584_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_));
v___x_585_ = 0;
v___x_586_ = 1;
v___x_587_ = l_Lean_registerEnvExtension___redArg(v___f_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_590_, lean_object* v_opt_591_){
_start:
{
lean_object* v_name_592_; lean_object* v_defValue_593_; lean_object* v_map_594_; lean_object* v___x_595_; 
v_name_592_ = lean_ctor_get(v_opt_591_, 0);
v_defValue_593_ = lean_ctor_get(v_opt_591_, 1);
v_map_594_ = lean_ctor_get(v_opts_590_, 0);
v___x_595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_594_, v_name_592_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_inc(v_defValue_593_);
return v_defValue_593_;
}
else
{
lean_object* v_val_596_; 
v_val_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v___x_595_, 1);
if (lean_obj_tag(v_val_596_) == 3)
{
lean_object* v_v_597_; 
v_v_597_ = lean_ctor_get(v_val_596_, 0);
lean_inc(v_v_597_);
lean_dec_ref_known(v_val_596_, 1);
return v_v_597_;
}
else
{
lean_dec(v_val_596_);
lean_inc(v_defValue_593_);
return v_defValue_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_598_, lean_object* v_opt_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_598_, v_opt_599_);
lean_dec_ref(v_opt_599_);
lean_dec_ref(v_opts_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_604_, size_t v_sz_605_, size_t v_i_606_, lean_object* v_b_607_){
_start:
{
lean_object* v_a_609_; uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_lt(v_i_606_, v_sz_605_);
if (v___x_613_ == 0)
{
return v_b_607_;
}
else
{
lean_object* v_a_614_; lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v_map_617_; uint8_t v_hasTrace_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_631_; 
v_a_614_ = lean_array_uget_borrowed(v_as_604_, v_i_606_);
v_fst_615_ = lean_ctor_get(v_a_614_, 0);
v_snd_616_ = lean_ctor_get(v_a_614_, 1);
v_map_617_ = lean_ctor_get(v_b_607_, 0);
v_hasTrace_618_ = lean_ctor_get_uint8(v_b_607_, sizeof(void*)*1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_b_607_);
if (v_isSharedCheck_631_ == 0)
{
v___x_620_ = v_b_607_;
v_isShared_621_ = v_isSharedCheck_631_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_map_617_);
lean_dec(v_b_607_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_631_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; 
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
v___x_622_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_615_, v_snd_616_, v_map_617_);
if (v_hasTrace_618_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; lean_object* v___x_626_; 
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_624_ = l_Lean_Name_isPrefixOf(v___x_623_, v_fst_615_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_622_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*1, v___x_624_);
v_a_609_ = v___x_626_;
goto v___jp_608_;
}
}
else
{
lean_object* v___x_629_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_629_ = v___x_620_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_622_);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, sizeof(void*)*1, v_hasTrace_618_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v_a_609_ = v___x_629_;
goto v___jp_608_;
}
}
}
}
v___jp_608_:
{
size_t v___x_610_; size_t v___x_611_; 
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_add(v_i_606_, v___x_610_);
v_i_606_ = v___x_611_;
v_b_607_ = v_a_609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_632_, lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_b_635_){
_start:
{
size_t v_sz_boxed_636_; size_t v_i_boxed_637_; lean_object* v_res_638_; 
v_sz_boxed_636_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_637_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_632_, v_sz_boxed_636_, v_i_boxed_637_, v_b_635_);
lean_dec_ref(v_as_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_639_, lean_object* v_k_640_, uint8_t v_v_641_){
_start:
{
lean_object* v_map_642_; uint8_t v_hasTrace_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_657_; 
v_map_642_ = lean_ctor_get(v_o_639_, 0);
v_hasTrace_643_ = lean_ctor_get_uint8(v_o_639_, sizeof(void*)*1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_o_639_);
if (v_isSharedCheck_657_ == 0)
{
v___x_645_ = v_o_639_;
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_map_642_);
lean_dec(v_o_639_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_647_, 0, v_v_641_);
lean_inc(v_k_640_);
v___x_648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_640_, v___x_647_, v_map_642_);
if (v_hasTrace_643_ == 0)
{
lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v___x_652_; 
v___x_649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_650_ = l_Lean_Name_isPrefixOf(v___x_649_, v_k_640_);
lean_dec(v_k_640_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_648_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*1, v___x_650_);
return v___x_652_;
}
}
else
{
lean_object* v___x_655_; 
lean_dec(v_k_640_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_655_ = v___x_645_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_656_, sizeof(void*)*1, v_hasTrace_643_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_658_, lean_object* v_k_659_, lean_object* v_v_660_){
_start:
{
uint8_t v_v_boxed_661_; lean_object* v_res_662_; 
v_v_boxed_661_ = lean_unbox(v_v_660_);
v_res_662_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_658_, v_k_659_, v_v_boxed_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_663_, lean_object* v_opt_664_, uint8_t v_val_665_){
_start:
{
lean_object* v_name_666_; lean_object* v___x_667_; 
v_name_666_ = lean_ctor_get(v_opt_664_, 0);
lean_inc(v_name_666_);
lean_dec_ref(v_opt_664_);
v___x_667_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_663_, v_name_666_, v_val_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_668_, lean_object* v_opt_669_, lean_object* v_val_670_){
_start:
{
uint8_t v_val_boxed_671_; lean_object* v_res_672_; 
v_val_boxed_671_ = lean_unbox(v_val_670_);
v_res_672_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_668_, v_opt_669_, v_val_boxed_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_673_, size_t v_i_674_, size_t v_stop_675_, lean_object* v_b_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_eq(v_i_674_, v_stop_675_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v_defValue_679_; uint8_t v___x_680_; lean_object* v___x_681_; size_t v___x_682_; size_t v___x_683_; 
v___x_678_ = lean_array_uget_borrowed(v_as_673_, v_i_674_);
v_defValue_679_ = lean_ctor_get(v___x_678_, 1);
v___x_680_ = lean_unbox(v_defValue_679_);
lean_inc(v___x_678_);
v___x_681_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_676_, v___x_678_, v___x_680_);
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_add(v_i_674_, v___x_682_);
v_i_674_ = v___x_683_;
v_b_676_ = v___x_681_;
goto _start;
}
else
{
return v_b_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_685_, lean_object* v_i_686_, lean_object* v_stop_687_, lean_object* v_b_688_){
_start:
{
size_t v_i_boxed_689_; size_t v_stop_boxed_690_; lean_object* v_res_691_; 
v_i_boxed_689_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_stop_boxed_690_ = lean_unbox_usize(v_stop_687_);
lean_dec(v_stop_687_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_685_, v_i_boxed_689_, v_stop_boxed_690_, v_b_688_);
lean_dec_ref(v_as_685_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Array_instInhabited___redArg();
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = l_Lean_Meta_eqnAffectingOptions;
v___x_698_ = lean_array_get_size(v___x_697_);
return v___x_698_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_lt(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_703_ = lean_nat_dec_le(v___x_702_, v___x_702_);
return v___x_703_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_704_; size_t v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_705_ = lean_usize_of_nat(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_706_, lean_object* v_act_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
uint16_t v___y_714_; lean_object* v___y_715_; lean_object* v_fileName_716_; lean_object* v_fileMap_717_; lean_object* v_currNamespace_718_; lean_object* v_openDecls_719_; lean_object* v_initHeartbeats_720_; lean_object* v_maxHeartbeats_721_; lean_object* v_quotContext_722_; lean_object* v_currMacroScope_723_; lean_object* v_cancelTk_x3f_724_; lean_object* v_inheritedTraceOptions_725_; lean_object* v_currRecDepth_726_; lean_object* v_ref_727_; uint8_t v_suppressElabErrors_728_; uint8_t v_isRecordingDeps_729_; lean_object* v___y_730_; uint8_t v___y_737_; uint16_t v___y_738_; lean_object* v___y_739_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_toCold_778_; lean_object* v_currRecDepth_779_; lean_object* v_ref_780_; uint8_t v_suppressElabErrors_781_; uint8_t v_isRecordingDeps_782_; lean_object* v_fileName_783_; lean_object* v_fileMap_784_; lean_object* v_options_785_; lean_object* v_currNamespace_786_; lean_object* v_openDecls_787_; lean_object* v_initHeartbeats_788_; lean_object* v_maxHeartbeats_789_; lean_object* v_quotContext_790_; lean_object* v_currMacroScope_791_; lean_object* v_cancelTk_x3f_792_; lean_object* v_inheritedTraceOptions_793_; lean_object* v___y_795_; 
v___x_776_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_777_ = lean_st_ref_get(v_a_711_);
v_toCold_778_ = lean_ctor_get(v_a_710_, 0);
v_currRecDepth_779_ = lean_ctor_get(v_a_710_, 1);
v_ref_780_ = lean_ctor_get(v_a_710_, 2);
v_suppressElabErrors_781_ = lean_ctor_get_uint8(v_a_710_, sizeof(void*)*3 + 2);
v_isRecordingDeps_782_ = lean_ctor_get_uint8(v_a_710_, sizeof(void*)*3 + 3);
v_fileName_783_ = lean_ctor_get(v_toCold_778_, 0);
v_fileMap_784_ = lean_ctor_get(v_toCold_778_, 1);
v_options_785_ = lean_ctor_get(v_toCold_778_, 2);
v_currNamespace_786_ = lean_ctor_get(v_toCold_778_, 4);
v_openDecls_787_ = lean_ctor_get(v_toCold_778_, 5);
v_initHeartbeats_788_ = lean_ctor_get(v_toCold_778_, 6);
v_maxHeartbeats_789_ = lean_ctor_get(v_toCold_778_, 7);
v_quotContext_790_ = lean_ctor_get(v_toCold_778_, 8);
v_currMacroScope_791_ = lean_ctor_get(v_toCold_778_, 9);
v_cancelTk_x3f_792_ = lean_ctor_get(v_toCold_778_, 10);
v_inheritedTraceOptions_793_ = lean_ctor_get(v_toCold_778_, 11);
if (v_isRecordingDeps_782_ == 0)
{
lean_object* v_env_806_; lean_object* v___x_807_; lean_object* v_toEnvExtension_808_; lean_object* v_asyncMode_809_; uint8_t v___x_810_; lean_object* v___x_811_; 
v_env_806_ = lean_ctor_get(v___x_777_, 0);
lean_inc_ref(v_env_806_);
lean_dec(v___x_777_);
v___x_807_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_808_ = lean_ctor_get(v___x_807_, 0);
v_asyncMode_809_ = lean_ctor_get(v_toEnvExtension_808_, 2);
v___x_810_ = 0;
v___x_811_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_776_, v___x_807_, v_env_806_, v_declName_706_, v_asyncMode_809_, v___x_810_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; lean_object* v___y_814_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_818_ = l_Lean_Meta_eqnAffectingOptions;
v___x_819_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_819_ == 0)
{
lean_inc_ref(v_options_785_);
v___y_814_ = v_options_785_;
goto v___jp_813_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_820_ == 0)
{
if (v___x_819_ == 0)
{
lean_inc_ref(v_options_785_);
v___y_814_ = v_options_785_;
goto v___jp_813_;
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((size_t)0ULL);
v___x_822_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_785_);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_818_, v___x_821_, v___x_822_, v_options_785_);
v___y_814_ = v___x_823_;
goto v___jp_813_;
}
}
else
{
size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((size_t)0ULL);
v___x_825_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_785_);
v___x_826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_818_, v___x_824_, v___x_825_, v_options_785_);
v___y_814_ = v___x_826_;
goto v___jp_813_;
}
}
v___jp_813_:
{
size_t v_sz_815_; size_t v___x_816_; lean_object* v___x_817_; 
v_sz_815_ = lean_array_size(v_val_812_);
v___x_816_ = ((size_t)0ULL);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_812_, v_sz_815_, v___x_816_, v___y_814_);
lean_dec(v_val_812_);
v___y_795_ = v___x_817_;
goto v___jp_794_;
}
}
else
{
lean_object* v___x_827_; uint8_t v___x_828_; 
lean_dec(v___x_811_);
v___x_827_ = l_Lean_Meta_eqnAffectingOptions;
v___x_828_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_828_ == 0)
{
lean_inc_ref(v_options_785_);
v___y_795_ = v_options_785_;
goto v___jp_794_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_829_ == 0)
{
if (v___x_828_ == 0)
{
lean_inc_ref(v_options_785_);
v___y_795_ = v_options_785_;
goto v___jp_794_;
}
else
{
size_t v___x_830_; size_t v___x_831_; lean_object* v___x_832_; 
v___x_830_ = ((size_t)0ULL);
v___x_831_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_785_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_827_, v___x_830_, v___x_831_, v_options_785_);
v___y_795_ = v___x_832_;
goto v___jp_794_;
}
}
else
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_785_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_827_, v___x_833_, v___x_834_, v_options_785_);
v___y_795_ = v___x_835_;
goto v___jp_794_;
}
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec(v___x_777_);
lean_dec(v_declName_706_);
lean_inc_ref(v_options_785_);
v___x_836_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_785_);
v___y_795_ = v___x_836_;
goto v___jp_794_;
}
v___jp_713_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_731_ = l_Lean_maxRecDepth;
v___x_732_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_715_, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_733_, 0, v_fileName_716_);
lean_ctor_set(v___x_733_, 1, v_fileMap_717_);
lean_ctor_set(v___x_733_, 2, v___y_715_);
lean_ctor_set(v___x_733_, 3, v___x_732_);
lean_ctor_set(v___x_733_, 4, v_currNamespace_718_);
lean_ctor_set(v___x_733_, 5, v_openDecls_719_);
lean_ctor_set(v___x_733_, 6, v_initHeartbeats_720_);
lean_ctor_set(v___x_733_, 7, v_maxHeartbeats_721_);
lean_ctor_set(v___x_733_, 8, v_quotContext_722_);
lean_ctor_set(v___x_733_, 9, v_currMacroScope_723_);
lean_ctor_set(v___x_733_, 10, v_cancelTk_x3f_724_);
lean_ctor_set(v___x_733_, 11, v_inheritedTraceOptions_725_);
lean_inc(v_ref_727_);
lean_inc(v_currRecDepth_726_);
v___x_734_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_currRecDepth_726_);
lean_ctor_set(v___x_734_, 2, v_ref_727_);
lean_ctor_set_uint16(v___x_734_, sizeof(void*)*3, v___y_714_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*3 + 2, v_suppressElabErrors_728_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*3 + 3, v_isRecordingDeps_729_);
lean_inc(v___y_730_);
lean_inc(v_a_709_);
lean_inc_ref(v_a_708_);
v___x_735_ = lean_apply_5(v_act_707_, v_a_708_, v_a_709_, v___x_734_, v___y_730_, lean_box(0));
return v___x_735_;
}
v___jp_736_:
{
lean_object* v___x_740_; lean_object* v_env_741_; lean_object* v_nextMacroScope_742_; lean_object* v_ngen_743_; lean_object* v_auxDeclNGen_744_; lean_object* v_traceState_745_; lean_object* v_recordedDeps_746_; lean_object* v_messages_747_; lean_object* v_infoState_748_; lean_object* v_snapshotTasks_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_774_; 
v___x_740_ = lean_st_ref_take(v_a_711_);
v_env_741_ = lean_ctor_get(v___x_740_, 0);
v_nextMacroScope_742_ = lean_ctor_get(v___x_740_, 1);
v_ngen_743_ = lean_ctor_get(v___x_740_, 2);
v_auxDeclNGen_744_ = lean_ctor_get(v___x_740_, 3);
v_traceState_745_ = lean_ctor_get(v___x_740_, 4);
v_recordedDeps_746_ = lean_ctor_get(v___x_740_, 6);
v_messages_747_ = lean_ctor_get(v___x_740_, 7);
v_infoState_748_ = lean_ctor_get(v___x_740_, 8);
v_snapshotTasks_749_ = lean_ctor_get(v___x_740_, 9);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_740_, 5);
lean_dec(v_unused_775_);
v___x_751_ = v___x_740_;
v_isShared_752_ = v_isSharedCheck_774_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snapshotTasks_749_);
lean_inc(v_infoState_748_);
lean_inc(v_messages_747_);
lean_inc(v_recordedDeps_746_);
lean_inc(v_traceState_745_);
lean_inc(v_auxDeclNGen_744_);
lean_inc(v_ngen_743_);
lean_inc(v_nextMacroScope_742_);
lean_inc(v_env_741_);
lean_dec(v___x_740_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_774_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = l_Lean_Kernel_enableDiag(v_env_741_, v___y_737_);
v___x_754_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 5, v___x_754_);
lean_ctor_set(v___x_751_, 0, v___x_753_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_nextMacroScope_742_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_ngen_743_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_auxDeclNGen_744_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_traceState_745_);
lean_ctor_set(v_reuseFailAlloc_773_, 5, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_773_, 6, v_recordedDeps_746_);
lean_ctor_set(v_reuseFailAlloc_773_, 7, v_messages_747_);
lean_ctor_set(v_reuseFailAlloc_773_, 8, v_infoState_748_);
lean_ctor_set(v_reuseFailAlloc_773_, 9, v_snapshotTasks_749_);
v___x_756_ = v_reuseFailAlloc_773_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v_toCold_758_; lean_object* v_currRecDepth_759_; lean_object* v_ref_760_; uint8_t v_suppressElabErrors_761_; uint8_t v_isRecordingDeps_762_; lean_object* v_fileName_763_; lean_object* v_fileMap_764_; lean_object* v_currNamespace_765_; lean_object* v_openDecls_766_; lean_object* v_initHeartbeats_767_; lean_object* v_maxHeartbeats_768_; lean_object* v_quotContext_769_; lean_object* v_currMacroScope_770_; lean_object* v_cancelTk_x3f_771_; lean_object* v_inheritedTraceOptions_772_; 
v___x_757_ = lean_st_ref_put(v_a_711_, v___x_756_);
v_toCold_758_ = lean_ctor_get(v_a_710_, 0);
v_currRecDepth_759_ = lean_ctor_get(v_a_710_, 1);
v_ref_760_ = lean_ctor_get(v_a_710_, 2);
v_suppressElabErrors_761_ = lean_ctor_get_uint8(v_a_710_, sizeof(void*)*3 + 2);
v_isRecordingDeps_762_ = lean_ctor_get_uint8(v_a_710_, sizeof(void*)*3 + 3);
v_fileName_763_ = lean_ctor_get(v_toCold_758_, 0);
v_fileMap_764_ = lean_ctor_get(v_toCold_758_, 1);
v_currNamespace_765_ = lean_ctor_get(v_toCold_758_, 4);
v_openDecls_766_ = lean_ctor_get(v_toCold_758_, 5);
v_initHeartbeats_767_ = lean_ctor_get(v_toCold_758_, 6);
v_maxHeartbeats_768_ = lean_ctor_get(v_toCold_758_, 7);
v_quotContext_769_ = lean_ctor_get(v_toCold_758_, 8);
v_currMacroScope_770_ = lean_ctor_get(v_toCold_758_, 9);
v_cancelTk_x3f_771_ = lean_ctor_get(v_toCold_758_, 10);
v_inheritedTraceOptions_772_ = lean_ctor_get(v_toCold_758_, 11);
lean_inc_ref(v_inheritedTraceOptions_772_);
lean_inc(v_cancelTk_x3f_771_);
lean_inc(v_currMacroScope_770_);
lean_inc(v_quotContext_769_);
lean_inc(v_maxHeartbeats_768_);
lean_inc(v_initHeartbeats_767_);
lean_inc(v_openDecls_766_);
lean_inc(v_currNamespace_765_);
lean_inc_ref(v_fileMap_764_);
lean_inc_ref(v_fileName_763_);
v___y_714_ = v___y_738_;
v___y_715_ = v___y_739_;
v_fileName_716_ = v_fileName_763_;
v_fileMap_717_ = v_fileMap_764_;
v_currNamespace_718_ = v_currNamespace_765_;
v_openDecls_719_ = v_openDecls_766_;
v_initHeartbeats_720_ = v_initHeartbeats_767_;
v_maxHeartbeats_721_ = v_maxHeartbeats_768_;
v_quotContext_722_ = v_quotContext_769_;
v_currMacroScope_723_ = v_currMacroScope_770_;
v_cancelTk_x3f_724_ = v_cancelTk_x3f_771_;
v_inheritedTraceOptions_725_ = v_inheritedTraceOptions_772_;
v_currRecDepth_726_ = v_currRecDepth_759_;
v_ref_727_ = v_ref_760_;
v_suppressElabErrors_728_ = v_suppressElabErrors_761_;
v_isRecordingDeps_729_ = v_isRecordingDeps_762_;
v___y_730_ = v_a_711_;
goto v___jp_713_;
}
}
}
v___jp_794_:
{
uint16_t v___x_796_; lean_object* v___x_797_; lean_object* v_env_798_; uint8_t v___x_799_; uint16_t v___x_800_; uint16_t v___x_801_; uint16_t v___x_802_; uint8_t v___x_803_; 
v___x_796_ = l_Lean_OptionFlags_ofOptions(v___y_795_);
v___x_797_ = lean_st_ref_get(v_a_711_);
v_env_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_env_798_);
lean_dec(v___x_797_);
v___x_799_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_798_);
lean_dec_ref(v_env_798_);
v___x_800_ = 512;
v___x_801_ = lean_uint16_land(v___x_796_, v___x_800_);
v___x_802_ = 0;
v___x_803_ = lean_uint16_dec_eq(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
if (v___x_799_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = 1;
v___y_737_ = v___x_804_;
v___y_738_ = v___x_796_;
v___y_739_ = v___y_795_;
goto v___jp_736_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_793_);
lean_inc(v_cancelTk_x3f_792_);
lean_inc(v_currMacroScope_791_);
lean_inc(v_quotContext_790_);
lean_inc(v_maxHeartbeats_789_);
lean_inc(v_initHeartbeats_788_);
lean_inc(v_openDecls_787_);
lean_inc(v_currNamespace_786_);
lean_inc_ref(v_fileMap_784_);
lean_inc_ref(v_fileName_783_);
v___y_714_ = v___x_796_;
v___y_715_ = v___y_795_;
v_fileName_716_ = v_fileName_783_;
v_fileMap_717_ = v_fileMap_784_;
v_currNamespace_718_ = v_currNamespace_786_;
v_openDecls_719_ = v_openDecls_787_;
v_initHeartbeats_720_ = v_initHeartbeats_788_;
v_maxHeartbeats_721_ = v_maxHeartbeats_789_;
v_quotContext_722_ = v_quotContext_790_;
v_currMacroScope_723_ = v_currMacroScope_791_;
v_cancelTk_x3f_724_ = v_cancelTk_x3f_792_;
v_inheritedTraceOptions_725_ = v_inheritedTraceOptions_793_;
v_currRecDepth_726_ = v_currRecDepth_779_;
v_ref_727_ = v_ref_780_;
v_suppressElabErrors_728_ = v_suppressElabErrors_781_;
v_isRecordingDeps_729_ = v_isRecordingDeps_782_;
v___y_730_ = v_a_711_;
goto v___jp_713_;
}
}
else
{
if (v___x_799_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_793_);
lean_inc(v_cancelTk_x3f_792_);
lean_inc(v_currMacroScope_791_);
lean_inc(v_quotContext_790_);
lean_inc(v_maxHeartbeats_789_);
lean_inc(v_initHeartbeats_788_);
lean_inc(v_openDecls_787_);
lean_inc(v_currNamespace_786_);
lean_inc_ref(v_fileMap_784_);
lean_inc_ref(v_fileName_783_);
v___y_714_ = v___x_796_;
v___y_715_ = v___y_795_;
v_fileName_716_ = v_fileName_783_;
v_fileMap_717_ = v_fileMap_784_;
v_currNamespace_718_ = v_currNamespace_786_;
v_openDecls_719_ = v_openDecls_787_;
v_initHeartbeats_720_ = v_initHeartbeats_788_;
v_maxHeartbeats_721_ = v_maxHeartbeats_789_;
v_quotContext_722_ = v_quotContext_790_;
v_currMacroScope_723_ = v_currMacroScope_791_;
v_cancelTk_x3f_724_ = v_cancelTk_x3f_792_;
v_inheritedTraceOptions_725_ = v_inheritedTraceOptions_793_;
v_currRecDepth_726_ = v_currRecDepth_779_;
v_ref_727_ = v_ref_780_;
v_suppressElabErrors_728_ = v_suppressElabErrors_781_;
v_isRecordingDeps_729_ = v_isRecordingDeps_782_;
v___y_730_ = v_a_711_;
goto v___jp_713_;
}
else
{
uint8_t v___x_805_; 
v___x_805_ = 0;
v___y_737_ = v___x_805_;
v___y_738_ = v___x_796_;
v___y_739_ = v___y_795_;
goto v___jp_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_837_, lean_object* v_act_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_837_, v_act_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_845_, lean_object* v_declName_846_, lean_object* v_act_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_846_, v_act_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_854_, lean_object* v_declName_855_, lean_object* v_act_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_854_, v_declName_855_, v_act_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_env_867_; lean_object* v_toConstantVal_868_; lean_object* v_value_869_; lean_object* v_all_870_; uint8_t v___y_872_; lean_object* v_type_880_; uint8_t v___x_881_; 
v___x_866_ = lean_st_ref_get(v___y_864_);
v_env_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref_n(v_env_867_, 2);
lean_dec(v___x_866_);
v_toConstantVal_868_ = lean_ctor_get(v_thm_863_, 0);
v_value_869_ = lean_ctor_get(v_thm_863_, 1);
v_all_870_ = lean_ctor_get(v_thm_863_, 2);
v_type_880_ = lean_ctor_get(v_toConstantVal_868_, 2);
v___x_881_ = l_Lean_Environment_hasUnsafe(v_env_867_, v_type_880_);
if (v___x_881_ == 0)
{
uint8_t v___x_882_; 
v___x_882_ = l_Lean_Environment_hasUnsafe(v_env_867_, v_value_869_);
v___y_872_ = v___x_882_;
goto v___jp_871_;
}
else
{
lean_dec_ref(v_env_867_);
v___y_872_ = v___x_881_;
goto v___jp_871_;
}
v___jp_871_:
{
if (v___y_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_873_, 0, v_thm_863_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_inc(v_all_870_);
lean_inc_ref(v_value_869_);
lean_inc_ref(v_toConstantVal_868_);
lean_dec_ref(v_thm_863_);
v___x_875_ = lean_box(0);
v___x_876_ = 0;
v___x_877_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_877_, 0, v_toConstantVal_868_);
lean_ctor_set(v___x_877_, 1, v_value_869_);
lean_ctor_set(v___x_877_, 2, v___x_875_);
lean_ctor_set(v___x_877_, 3, v_all_870_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*4, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_883_, v___y_884_);
lean_dec(v___y_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_887_, v___y_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_901_, lean_object* v_b_902_, lean_object* v_c_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
v___x_909_ = lean_apply_7(v_k_901_, v_b_902_, v_c_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_910_, lean_object* v_b_911_, lean_object* v_c_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_910_, v_b_911_, v_c_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_919_, lean_object* v_k_920_, uint8_t v_cleanupAnnotations_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___f_927_; uint8_t v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_927_, 0, v_k_920_);
v___x_928_ = 1;
v___x_929_ = 0;
v___x_930_ = lean_box(0);
v___x_931_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_919_, v___x_928_, v___x_929_, v___x_928_, v___x_929_, v___x_930_, v___f_927_, v_cleanupAnnotations_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_a_940_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_931_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_931_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_948_, lean_object* v_k_949_, lean_object* v_cleanupAnnotations_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_956_; lean_object* v_res_957_; 
v_cleanupAnnotations_boxed_956_ = lean_unbox(v_cleanupAnnotations_950_);
v_res_957_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_948_, v_k_949_, v_cleanupAnnotations_boxed_956_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_958_, lean_object* v_e_959_, lean_object* v_k_960_, uint8_t v_cleanupAnnotations_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_959_, v_k_960_, v_cleanupAnnotations_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_968_, lean_object* v_e_969_, lean_object* v_k_970_, lean_object* v_cleanupAnnotations_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_977_; lean_object* v_res_978_; 
v_cleanupAnnotations_boxed_977_ = lean_unbox(v_cleanupAnnotations_971_);
v_res_978_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_968_, v_e_969_, v_k_970_, v_cleanupAnnotations_boxed_977_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
if (lean_obj_tag(v_a_979_) == 0)
{
lean_object* v___x_981_; 
v___x_981_ = l_List_reverse___redArg(v_a_980_);
return v___x_981_;
}
else
{
lean_object* v_head_982_; lean_object* v_tail_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_992_; 
v_head_982_ = lean_ctor_get(v_a_979_, 0);
v_tail_983_ = lean_ctor_get(v_a_979_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_a_979_);
if (v_isSharedCheck_992_ == 0)
{
v___x_985_ = v_a_979_;
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_tail_983_);
lean_inc(v_head_982_);
lean_dec(v_a_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = l_Lean_mkLevelParam(v_head_982_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_a_980_);
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_a_980_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
v_a_979_ = v_tail_983_;
v_a_980_ = v___x_989_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_993_, lean_object* v_name_994_, lean_object* v_xs_995_, lean_object* v_body_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_name_1002_; lean_object* v_levelParams_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1073_; 
v_name_1002_ = lean_ctor_get(v_toConstantVal_993_, 0);
v_levelParams_1003_ = lean_ctor_get(v_toConstantVal_993_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_toConstantVal_993_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v_toConstantVal_993_, 2);
lean_dec(v_unused_1074_);
v___x_1005_ = v_toConstantVal_993_;
v_isShared_1006_ = v_isSharedCheck_1073_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_levelParams_1003_);
lean_inc(v_name_1002_);
lean_dec(v_toConstantVal_993_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1073_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_lhs_1010_; lean_object* v___x_1011_; 
v___x_1007_ = lean_box(0);
lean_inc(v_levelParams_1003_);
v___x_1008_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_1003_, v___x_1007_);
v___x_1009_ = l_Lean_mkConst(v_name_1002_, v___x_1008_);
v_lhs_1010_ = l_Lean_mkAppN(v___x_1009_, v_xs_995_);
lean_inc_ref(v_lhs_1010_);
v___x_1011_ = l_Lean_Meta_mkEq(v_lhs_1010_, v_body_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; uint8_t v___x_1013_; uint8_t v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = 0;
v___x_1014_ = 1;
v___x_1015_ = 1;
v___x_1016_ = l_Lean_Meta_mkForallFVars(v_xs_995_, v_a_1012_, v___x_1013_, v___x_1014_, v___x_1014_, v___x_1015_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = l_Lean_Meta_letToHave(v_a_1017_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = l_Lean_Meta_mkEqRefl(v_lhs_1010_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_Lean_Meta_mkLambdaFVars(v_xs_995_, v_a_1021_, v___x_1013_, v___x_1014_, v___x_1013_, v___x_1014_, v___x_1015_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
lean_inc(v_name_994_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 2, v_a_1019_);
lean_ctor_set(v___x_1005_, 0, v_name_994_);
v___x_1025_ = v___x_1005_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_name_994_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_levelParams_1003_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_a_1019_);
v___x_1025_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_a_1029_; lean_object* v___x_1030_; 
lean_inc(v_name_994_);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_name_994_);
lean_ctor_set(v___x_1026_, 1, v___x_1007_);
v___x_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v_a_1023_);
lean_ctor_set(v___x_1027_, 2, v___x_1026_);
v___x_1028_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_1027_, v___y_1000_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l_Lean_addDecl(v_a_1029_, v___x_1013_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref_known(v___x_1030_, 1);
v___x_1031_ = l_Lean_inferDefEqAttr(v_name_994_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v___x_1031_;
}
else
{
lean_dec(v_name_994_);
return v___x_1030_;
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_a_1019_);
lean_del_object(v___x_1005_);
lean_dec(v_levelParams_1003_);
lean_dec(v_name_994_);
v_a_1033_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1022_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1022_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_1019_);
lean_del_object(v___x_1005_);
lean_dec(v_levelParams_1003_);
lean_dec(v_name_994_);
v_a_1041_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1020_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1020_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_lhs_1010_);
lean_del_object(v___x_1005_);
lean_dec(v_levelParams_1003_);
lean_dec(v_name_994_);
v_a_1049_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1018_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1018_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_lhs_1010_);
lean_del_object(v___x_1005_);
lean_dec(v_levelParams_1003_);
lean_dec(v_name_994_);
v_a_1057_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1016_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1016_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
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
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_lhs_1010_);
lean_del_object(v___x_1005_);
lean_dec(v_levelParams_1003_);
lean_dec(v_name_994_);
v_a_1065_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1011_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1011_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1075_, lean_object* v_name_1076_, lean_object* v_xs_1077_, lean_object* v_body_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1075_, v_name_1076_, v_xs_1077_, v_body_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v_xs_1077_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1085_, lean_object* v_info_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_toConstantVal_1092_; lean_object* v_value_1093_; lean_object* v___f_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; 
v_toConstantVal_1092_ = lean_ctor_get(v_info_1086_, 0);
lean_inc_ref(v_toConstantVal_1092_);
v_value_1093_ = lean_ctor_get(v_info_1086_, 1);
lean_inc_ref(v_value_1093_);
lean_dec_ref(v_info_1086_);
v___f_1094_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1094_, 0, v_toConstantVal_1092_);
lean_closure_set(v___f_1094_, 1, v_name_1085_);
v___x_1095_ = 1;
v___x_1096_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1093_, v___f_1094_, v___x_1095_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1097_, lean_object* v_info_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1097_, v_info_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1105_, lean_object* v_name_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = lean_st_ref_get(v_a_1110_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1117_ = 0;
lean_inc(v_declName_1105_);
v___x_1118_ = l_Lean_Environment_find_x3f(v_env_1116_, v_declName_1105_, v___x_1117_);
if (lean_obj_tag(v___x_1118_) == 1)
{
lean_object* v_val_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1146_; 
v_val_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1146_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_val_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1146_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
if (lean_obj_tag(v_val_1119_) == 1)
{
lean_object* v_val_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_val_1123_ = lean_ctor_get(v_val_1119_, 0);
lean_inc_ref(v_val_1123_);
lean_dec_ref_known(v_val_1119_, 1);
lean_inc_n(v_name_1106_, 2);
v___x_1124_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1124_, 0, v_name_1106_);
lean_closure_set(v___x_1124_, 1, v_val_1123_);
lean_inc(v_declName_1105_);
v___x_1125_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1125_, 0, lean_box(0));
lean_closure_set(v___x_1125_, 1, v_declName_1105_);
lean_closure_set(v___x_1125_, 2, v___x_1124_);
v___x_1126_ = l_Lean_Meta_realizeConst(v_declName_1105_, v_name_1106_, v___x_1125_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1136_; 
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v___x_1126_, 0);
lean_dec(v_unused_1137_);
v___x_1128_ = v___x_1126_;
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v___x_1126_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v_name_1106_);
v___x_1131_ = v___x_1121_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_name_1106_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_del_object(v___x_1121_);
lean_dec(v_name_1106_);
v_a_1138_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1126_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1126_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_del_object(v___x_1121_);
lean_dec(v_val_1119_);
lean_dec(v_name_1106_);
lean_dec(v_declName_1105_);
goto v___jp_1112_;
}
}
}
else
{
lean_dec(v___x_1118_);
lean_dec(v_name_1106_);
lean_dec(v_declName_1105_);
goto v___jp_1112_;
}
v___jp_1112_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1147_, lean_object* v_name_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1147_, v_name_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_i_1157_, lean_object* v_k_1158_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_array_get_size(v_keys_1155_);
v___x_1160_ = lean_nat_dec_lt(v_i_1157_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v_i_1157_);
v___x_1161_ = lean_box(0);
return v___x_1161_;
}
else
{
lean_object* v_k_x27_1162_; uint8_t v___x_1163_; 
v_k_x27_1162_ = lean_array_fget_borrowed(v_keys_1155_, v_i_1157_);
v___x_1163_ = lean_name_eq(v_k_1158_, v_k_x27_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_add(v_i_1157_, v___x_1164_);
lean_dec(v_i_1157_);
v_i_1157_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_array_fget_borrowed(v_vals_1156_, v_i_1157_);
lean_dec(v_i_1157_);
lean_inc(v___x_1167_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1169_, lean_object* v_vals_1170_, lean_object* v_i_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1169_, v_vals_1170_, v_i_1171_, v_k_1172_);
lean_dec(v_k_1172_);
lean_dec_ref(v_vals_1170_);
lean_dec_ref(v_keys_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1174_, size_t v_x_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v_es_1177_; lean_object* v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; lean_object* v_j_1181_; lean_object* v___x_1182_; 
v_es_1177_ = lean_ctor_get(v_x_1174_, 0);
v___x_1178_ = lean_box(2);
v___x_1179_ = ((size_t)31ULL);
v___x_1180_ = lean_usize_land(v_x_1175_, v___x_1179_);
v_j_1181_ = lean_usize_to_nat(v___x_1180_);
v___x_1182_ = lean_array_get_borrowed(v___x_1178_, v_es_1177_, v_j_1181_);
lean_dec(v_j_1181_);
switch(lean_obj_tag(v___x_1182_))
{
case 0:
{
lean_object* v_key_1183_; lean_object* v_val_1184_; uint8_t v___x_1185_; 
v_key_1183_ = lean_ctor_get(v___x_1182_, 0);
v_val_1184_ = lean_ctor_get(v___x_1182_, 1);
v___x_1185_ = lean_name_eq(v_x_1176_, v_key_1183_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_box(0);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
lean_inc(v_val_1184_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_val_1184_);
return v___x_1187_;
}
}
case 1:
{
lean_object* v_node_1188_; size_t v___x_1189_; size_t v___x_1190_; 
v_node_1188_ = lean_ctor_get(v___x_1182_, 0);
v___x_1189_ = ((size_t)5ULL);
v___x_1190_ = lean_usize_shift_right(v_x_1175_, v___x_1189_);
v_x_1174_ = v_node_1188_;
v_x_1175_ = v___x_1190_;
goto _start;
}
default: 
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
}
}
else
{
lean_object* v_ks_1193_; lean_object* v_vs_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_ks_1193_ = lean_ctor_get(v_x_1174_, 0);
v_vs_1194_ = lean_ctor_get(v_x_1174_, 1);
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1193_, v_vs_1194_, v___x_1195_, v_x_1176_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
size_t v_x_344__boxed_1200_; lean_object* v_res_1201_; 
v_x_344__boxed_1200_ = lean_unbox_usize(v_x_1198_);
lean_dec(v_x_1198_);
v_res_1201_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1197_, v_x_344__boxed_1200_, v_x_1199_);
lean_dec(v_x_1199_);
lean_dec_ref(v_x_1197_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1202_, lean_object* v_x_1203_){
_start:
{
uint64_t v___y_1205_; 
if (lean_obj_tag(v_x_1203_) == 0)
{
uint64_t v___x_1208_; 
v___x_1208_ = 1723ULL;
v___y_1205_ = v___x_1208_;
goto v___jp_1204_;
}
else
{
uint64_t v_hash_1209_; 
v_hash_1209_ = lean_ctor_get_uint64(v_x_1203_, sizeof(void*)*2);
v___y_1205_ = v_hash_1209_;
goto v___jp_1204_;
}
v___jp_1204_:
{
size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_uint64_to_usize(v___y_1205_);
v___x_1207_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1202_, v___x_1206_, v_x_1203_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1210_, v_x_1211_);
lean_dec(v_x_1211_);
lean_dec_ref(v_x_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_env_1218_; lean_object* v___x_1219_; lean_object* v_asyncMode_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1216_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1217_ = lean_st_ref_get(v_a_1214_);
v_env_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_env_1218_);
lean_dec(v___x_1217_);
v___x_1219_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1220_ = lean_ctor_get(v___x_1219_, 2);
v___x_1221_ = lean_box(0);
v___x_1222_ = 0;
v___x_1223_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1216_, v___x_1219_, v_env_1218_, v_asyncMode_1220_, v___x_1221_, v___x_1222_);
v___x_1224_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1223_, v_thmName_1213_);
lean_dec(v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec(v_thmName_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1230_, v_a_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_thmName_1235_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1241_, v_x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1244_, v_x_1245_, v_x_1246_);
lean_dec(v_x_1246_);
lean_dec_ref(v_x_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1248_, lean_object* v_x_1249_, size_t v_x_1250_, lean_object* v_x_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1249_, v_x_1250_, v_x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
size_t v_x_439__boxed_1257_; lean_object* v_res_1258_; 
v_x_439__boxed_1257_ = lean_unbox_usize(v_x_1255_);
lean_dec(v_x_1255_);
v_res_1258_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1253_, v_x_1254_, v_x_439__boxed_1257_, v_x_1256_);
lean_dec(v_x_1256_);
lean_dec_ref(v_x_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1259_, lean_object* v_keys_1260_, lean_object* v_vals_1261_, lean_object* v_heq_1262_, lean_object* v_i_1263_, lean_object* v_k_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1260_, v_vals_1261_, v_i_1263_, v_k_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1266_, lean_object* v_keys_1267_, lean_object* v_vals_1268_, lean_object* v_heq_1269_, lean_object* v_i_1270_, lean_object* v_k_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1266_, v_keys_1267_, v_vals_1268_, v_heq_1269_, v_i_1270_, v_k_1271_);
lean_dec(v_k_1271_);
lean_dec_ref(v_vals_1268_);
lean_dec_ref(v_keys_1267_);
return v_res_1272_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1273_, lean_object* v_i_1274_, lean_object* v_k_1275_){
_start:
{
lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = lean_array_get_size(v_keys_1273_);
v___x_1277_ = lean_nat_dec_lt(v_i_1274_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec(v_i_1274_);
return v___x_1277_;
}
else
{
lean_object* v_k_x27_1278_; uint8_t v___x_1279_; 
v_k_x27_1278_ = lean_array_fget_borrowed(v_keys_1273_, v_i_1274_);
v___x_1279_ = lean_name_eq(v_k_1275_, v_k_x27_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_add(v_i_1274_, v___x_1280_);
lean_dec(v_i_1274_);
v_i_1274_ = v___x_1281_;
goto _start;
}
else
{
lean_dec(v_i_1274_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1283_, lean_object* v_i_1284_, lean_object* v_k_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1283_, v_i_1284_, v_k_1285_);
lean_dec(v_k_1285_);
lean_dec_ref(v_keys_1283_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1288_, size_t v_x_1289_, lean_object* v_x_1290_){
_start:
{
if (lean_obj_tag(v_x_1288_) == 0)
{
lean_object* v_es_1291_; lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v_j_1295_; lean_object* v___x_1296_; 
v_es_1291_ = lean_ctor_get(v_x_1288_, 0);
v___x_1292_ = lean_box(2);
v___x_1293_ = ((size_t)31ULL);
v___x_1294_ = lean_usize_land(v_x_1289_, v___x_1293_);
v_j_1295_ = lean_usize_to_nat(v___x_1294_);
v___x_1296_ = lean_array_get_borrowed(v___x_1292_, v_es_1291_, v_j_1295_);
lean_dec(v_j_1295_);
switch(lean_obj_tag(v___x_1296_))
{
case 0:
{
lean_object* v_key_1297_; uint8_t v___x_1298_; 
v_key_1297_ = lean_ctor_get(v___x_1296_, 0);
v___x_1298_ = lean_name_eq(v_x_1290_, v_key_1297_);
return v___x_1298_;
}
case 1:
{
lean_object* v_node_1299_; size_t v___x_1300_; size_t v___x_1301_; 
v_node_1299_ = lean_ctor_get(v___x_1296_, 0);
v___x_1300_ = ((size_t)5ULL);
v___x_1301_ = lean_usize_shift_right(v_x_1289_, v___x_1300_);
v_x_1288_ = v_node_1299_;
v_x_1289_ = v___x_1301_;
goto _start;
}
default: 
{
uint8_t v___x_1303_; 
v___x_1303_ = 0;
return v___x_1303_;
}
}
}
else
{
lean_object* v_ks_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_ks_1304_ = lean_ctor_get(v_x_1288_, 0);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1304_, v___x_1305_, v_x_1290_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
size_t v_x_328__boxed_1310_; uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_x_328__boxed_1310_ = lean_unbox_usize(v_x_1308_);
lean_dec(v_x_1308_);
v_res_1311_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1307_, v_x_328__boxed_1310_, v_x_1309_);
lean_dec(v_x_1309_);
lean_dec_ref(v_x_1307_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
uint64_t v___y_1316_; 
if (lean_obj_tag(v_x_1314_) == 0)
{
uint64_t v___x_1319_; 
v___x_1319_ = 1723ULL;
v___y_1316_ = v___x_1319_;
goto v___jp_1315_;
}
else
{
uint64_t v_hash_1320_; 
v_hash_1320_ = lean_ctor_get_uint64(v_x_1314_, sizeof(void*)*2);
v___y_1316_ = v_hash_1320_;
goto v___jp_1315_;
}
v___jp_1315_:
{
size_t v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_uint64_to_usize(v___y_1316_);
v___x_1318_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1313_, v___x_1317_, v_x_1314_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
uint8_t v_res_1323_; lean_object* v_r_1324_; 
v_res_1323_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1321_, v_x_1322_);
lean_dec(v_x_1322_);
lean_dec_ref(v_x_1321_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v_env_1330_; lean_object* v___x_1331_; lean_object* v_asyncMode_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1328_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1329_ = lean_st_ref_get(v_a_1326_);
v_env_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_env_1330_);
lean_dec(v___x_1329_);
v___x_1331_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1332_ = lean_ctor_get(v___x_1331_, 2);
v___x_1333_ = lean_box(0);
v___x_1334_ = 0;
v___x_1335_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1328_, v___x_1331_, v_env_1330_, v_asyncMode_1332_, v___x_1333_, v___x_1334_);
v___x_1336_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1335_, v_thmName_1325_);
lean_dec(v___x_1335_);
v___x_1337_ = lean_box(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec(v_thmName_1339_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1343_, v_a_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Meta_isEqnThm(v_thmName_1348_, v_a_1349_, v_a_1350_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_thmName_1348_);
return v_res_1352_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
uint8_t v___x_1356_; 
v___x_1356_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1354_, v_x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1357_, lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1357_, v_x_1358_, v_x_1359_);
lean_dec(v_x_1359_);
lean_dec_ref(v_x_1358_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1362_, lean_object* v_x_1363_, size_t v_x_1364_, lean_object* v_x_1365_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1363_, v_x_1364_, v_x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_){
_start:
{
size_t v_x_419__boxed_1371_; uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_x_419__boxed_1371_ = lean_unbox_usize(v_x_1369_);
lean_dec(v_x_1369_);
v_res_1372_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1367_, v_x_1368_, v_x_419__boxed_1371_, v_x_1370_);
lean_dec(v_x_1370_);
lean_dec_ref(v_x_1368_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1374_, lean_object* v_keys_1375_, lean_object* v_vals_1376_, lean_object* v_heq_1377_, lean_object* v_i_1378_, lean_object* v_k_1379_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1375_, v_i_1378_, v_k_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1381_, lean_object* v_keys_1382_, lean_object* v_vals_1383_, lean_object* v_heq_1384_, lean_object* v_i_1385_, lean_object* v_k_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1381_, v_keys_1382_, v_vals_1383_, v_heq_1384_, v_i_1385_, v_k_1386_);
lean_dec(v_k_1386_);
lean_dec_ref(v_vals_1383_);
lean_dec_ref(v_keys_1382_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1389_, lean_object* v_msg_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_panic_fn_borrowed(v_x1_1389_, v_msg_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1392_, lean_object* v_msg_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1392_, v_msg_1393_);
lean_dec_ref(v_x1_1392_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v_ks_1399_; lean_object* v_vs_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1424_; 
v_ks_1399_ = lean_ctor_get(v_x_1395_, 0);
v_vs_1400_ = lean_ctor_get(v_x_1395_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1395_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1402_ = v_x_1395_;
v_isShared_1403_ = v_isSharedCheck_1424_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_vs_1400_);
lean_inc(v_ks_1399_);
lean_dec(v_x_1395_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1424_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = lean_array_get_size(v_ks_1399_);
v___x_1405_ = lean_nat_dec_lt(v_x_1396_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_x_1396_);
v___x_1406_ = lean_array_push(v_ks_1399_, v_x_1397_);
v___x_1407_ = lean_array_push(v_vs_1400_, v_x_1398_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1407_);
lean_ctor_set(v___x_1402_, 0, v___x_1406_);
v___x_1409_ = v___x_1402_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_object* v_k_x27_1411_; uint8_t v___x_1412_; 
v_k_x27_1411_ = lean_array_fget_borrowed(v_ks_1399_, v_x_1396_);
v___x_1412_ = lean_name_eq(v_x_1397_, v_k_x27_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1414_; 
if (v_isShared_1403_ == 0)
{
v___x_1414_ = v___x_1402_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_ks_1399_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_vs_1400_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_unsigned_to_nat(1u);
v___x_1416_ = lean_nat_add(v_x_1396_, v___x_1415_);
lean_dec(v_x_1396_);
v_x_1395_ = v___x_1414_;
v_x_1396_ = v___x_1416_;
goto _start;
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = lean_array_fset(v_ks_1399_, v_x_1396_, v_x_1397_);
v___x_1420_ = lean_array_fset(v_vs_1400_, v_x_1396_, v_x_1398_);
lean_dec(v_x_1396_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1420_);
lean_ctor_set(v___x_1402_, 0, v___x_1419_);
v___x_1422_ = v___x_1402_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1425_, lean_object* v_k_1426_, lean_object* v_v_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1425_, v___x_1428_, v_k_1426_, v_v_1427_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1431_, size_t v_x_1432_, size_t v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1431_) == 0)
{
lean_object* v_es_1436_; size_t v___x_1437_; size_t v___x_1438_; lean_object* v_j_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_es_1436_ = lean_ctor_get(v_x_1431_, 0);
v___x_1437_ = ((size_t)31ULL);
v___x_1438_ = lean_usize_land(v_x_1432_, v___x_1437_);
v_j_1439_ = lean_usize_to_nat(v___x_1438_);
v___x_1440_ = lean_array_get_size(v_es_1436_);
v___x_1441_ = lean_nat_dec_lt(v_j_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_dec(v_j_1439_);
lean_dec(v_x_1435_);
lean_dec(v_x_1434_);
return v_x_1431_;
}
else
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1480_; 
lean_inc_ref(v_es_1436_);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_x_1431_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v_x_1431_, 0);
lean_dec(v_unused_1481_);
v___x_1443_ = v_x_1431_;
v_isShared_1444_ = v_isSharedCheck_1480_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_x_1431_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1480_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_v_1445_; lean_object* v___x_1446_; lean_object* v_xs_x27_1447_; lean_object* v___y_1449_; 
v_v_1445_ = lean_array_fget(v_es_1436_, v_j_1439_);
v___x_1446_ = lean_box(0);
v_xs_x27_1447_ = lean_array_fset(v_es_1436_, v_j_1439_, v___x_1446_);
switch(lean_obj_tag(v_v_1445_))
{
case 0:
{
lean_object* v_key_1454_; lean_object* v_val_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1465_; 
v_key_1454_ = lean_ctor_get(v_v_1445_, 0);
v_val_1455_ = lean_ctor_get(v_v_1445_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_v_1445_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1457_ = v_v_1445_;
v_isShared_1458_ = v_isSharedCheck_1465_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_val_1455_);
lean_inc(v_key_1454_);
lean_dec(v_v_1445_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1465_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_name_eq(v_x_1434_, v_key_1454_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_del_object(v___x_1457_);
v___x_1460_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1454_, v_val_1455_, v_x_1434_, v_x_1435_);
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
v___y_1449_ = v___x_1461_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_val_1455_);
lean_dec(v_key_1454_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v_x_1435_);
lean_ctor_set(v___x_1457_, 0, v_x_1434_);
v___x_1463_ = v___x_1457_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_x_1434_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_x_1435_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
v___y_1449_ = v___x_1463_;
goto v___jp_1448_;
}
}
}
}
case 1:
{
lean_object* v_node_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1478_; 
v_node_1466_ = lean_ctor_get(v_v_1445_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_v_1445_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1468_ = v_v_1445_;
v_isShared_1469_ = v_isSharedCheck_1478_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_node_1466_);
lean_dec(v_v_1445_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1478_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
size_t v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1470_ = ((size_t)5ULL);
v___x_1471_ = lean_usize_shift_right(v_x_1432_, v___x_1470_);
v___x_1472_ = ((size_t)1ULL);
v___x_1473_ = lean_usize_add(v_x_1433_, v___x_1472_);
v___x_1474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1466_, v___x_1471_, v___x_1473_, v_x_1434_, v_x_1435_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1474_);
v___x_1476_ = v___x_1468_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
v___y_1449_ = v___x_1476_;
goto v___jp_1448_;
}
}
}
default: 
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_x_1434_);
lean_ctor_set(v___x_1479_, 1, v_x_1435_);
v___y_1449_ = v___x_1479_;
goto v___jp_1448_;
}
}
v___jp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_array_fset(v_xs_x27_1447_, v_j_1439_, v___y_1449_);
lean_dec(v_j_1439_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1450_);
v___x_1452_ = v___x_1443_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_ks_1482_; lean_object* v_vs_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1501_; 
v_ks_1482_ = lean_ctor_get(v_x_1431_, 0);
v_vs_1483_ = lean_ctor_get(v_x_1431_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_x_1431_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1485_ = v_x_1431_;
v_isShared_1486_ = v_isSharedCheck_1501_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_vs_1483_);
lean_inc(v_ks_1482_);
lean_dec(v_x_1431_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1501_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_ks_1482_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_vs_1483_);
v___x_1488_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v_newNode_1489_; size_t v___x_1490_; uint8_t v___x_1491_; 
v_newNode_1489_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1488_, v_x_1434_, v_x_1435_);
v___x_1490_ = ((size_t)7ULL);
v___x_1491_ = lean_usize_dec_le(v___x_1490_, v_x_1433_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1489_);
v___x_1493_ = lean_unsigned_to_nat(4u);
v___x_1494_ = lean_nat_dec_lt(v___x_1492_, v___x_1493_);
lean_dec(v___x_1492_);
if (v___x_1494_ == 0)
{
lean_object* v_ks_1495_; lean_object* v_vs_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_ks_1495_ = lean_ctor_get(v_newNode_1489_, 0);
lean_inc_ref(v_ks_1495_);
v_vs_1496_ = lean_ctor_get(v_newNode_1489_, 1);
lean_inc_ref(v_vs_1496_);
lean_dec_ref(v_newNode_1489_);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1433_, v_ks_1495_, v_vs_1496_, v___x_1497_, v___x_1498_);
lean_dec_ref(v_vs_1496_);
lean_dec_ref(v_ks_1495_);
return v___x_1499_;
}
else
{
return v_newNode_1489_;
}
}
else
{
return v_newNode_1489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1502_, lean_object* v_keys_1503_, lean_object* v_vals_1504_, lean_object* v_i_1505_, lean_object* v_entries_1506_){
_start:
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = lean_array_get_size(v_keys_1503_);
v___x_1508_ = lean_nat_dec_lt(v_i_1505_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_dec(v_i_1505_);
return v_entries_1506_;
}
else
{
lean_object* v_k_1509_; lean_object* v_v_1510_; uint64_t v___y_1512_; 
v_k_1509_ = lean_array_fget_borrowed(v_keys_1503_, v_i_1505_);
v_v_1510_ = lean_array_fget_borrowed(v_vals_1504_, v_i_1505_);
if (lean_obj_tag(v_k_1509_) == 0)
{
uint64_t v___x_1523_; 
v___x_1523_ = 1723ULL;
v___y_1512_ = v___x_1523_;
goto v___jp_1511_;
}
else
{
uint64_t v_hash_1524_; 
v_hash_1524_ = lean_ctor_get_uint64(v_k_1509_, sizeof(void*)*2);
v___y_1512_ = v_hash_1524_;
goto v___jp_1511_;
}
v___jp_1511_:
{
size_t v_h_1513_; size_t v___x_1514_; lean_object* v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; size_t v_h_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_h_1513_ = lean_uint64_to_usize(v___y_1512_);
v___x_1514_ = ((size_t)5ULL);
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_sub(v_depth_1502_, v___x_1516_);
v___x_1518_ = lean_usize_mul(v___x_1514_, v___x_1517_);
v_h_1519_ = lean_usize_shift_right(v_h_1513_, v___x_1518_);
v___x_1520_ = lean_nat_add(v_i_1505_, v___x_1515_);
lean_dec(v_i_1505_);
lean_inc(v_v_1510_);
lean_inc(v_k_1509_);
v___x_1521_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1506_, v_h_1519_, v_depth_1502_, v_k_1509_, v_v_1510_);
v_i_1505_ = v___x_1520_;
v_entries_1506_ = v___x_1521_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1525_, lean_object* v_keys_1526_, lean_object* v_vals_1527_, lean_object* v_i_1528_, lean_object* v_entries_1529_){
_start:
{
size_t v_depth_boxed_1530_; lean_object* v_res_1531_; 
v_depth_boxed_1530_ = lean_unbox_usize(v_depth_1525_);
lean_dec(v_depth_1525_);
v_res_1531_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1530_, v_keys_1526_, v_vals_1527_, v_i_1528_, v_entries_1529_);
lean_dec_ref(v_vals_1527_);
lean_dec_ref(v_keys_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_){
_start:
{
size_t v_x_909__boxed_1537_; size_t v_x_910__boxed_1538_; lean_object* v_res_1539_; 
v_x_909__boxed_1537_ = lean_unbox_usize(v_x_1533_);
lean_dec(v_x_1533_);
v_x_910__boxed_1538_ = lean_unbox_usize(v_x_1534_);
lean_dec(v_x_1534_);
v_res_1539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1532_, v_x_909__boxed_1537_, v_x_910__boxed_1538_, v_x_1535_, v_x_1536_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
uint64_t v___y_1544_; 
if (lean_obj_tag(v_x_1541_) == 0)
{
uint64_t v___x_1548_; 
v___x_1548_ = 1723ULL;
v___y_1544_ = v___x_1548_;
goto v___jp_1543_;
}
else
{
uint64_t v_hash_1549_; 
v_hash_1549_ = lean_ctor_get_uint64(v_x_1541_, sizeof(void*)*2);
v___y_1544_ = v_hash_1549_;
goto v___jp_1543_;
}
v___jp_1543_:
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = lean_uint64_to_usize(v___y_1544_);
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1540_, v___x_1545_, v___x_1546_, v_x_1541_, v_x_1542_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1555_, lean_object* v_as_1556_, size_t v_i_1557_, size_t v_stop_1558_, lean_object* v_b_1559_){
_start:
{
lean_object* v___y_1561_; uint8_t v___x_1565_; 
v___x_1565_ = lean_usize_dec_eq(v_i_1557_, v_stop_1558_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_array_uget_borrowed(v_as_1556_, v_i_1557_);
v___x_1567_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1559_, v___x_1566_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; 
lean_inc(v_declName_1555_);
lean_inc(v___x_1566_);
v___x_1568_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1559_, v___x_1566_, v_declName_1555_);
v___y_1561_ = v___x_1568_;
goto v___jp_1560_;
}
else
{
lean_object* v_val_1569_; uint8_t v___x_1570_; 
v_val_1569_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_val_1569_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1570_ = lean_name_eq(v_val_1569_, v_declName_1555_);
if (v___x_1570_ == 0)
{
uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1571_ = 1;
v___x_1572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1574_ = lean_unsigned_to_nat(231u);
v___x_1575_ = lean_unsigned_to_nat(10u);
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1566_);
v___x_1577_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1566_, v___x_1571_);
v___x_1578_ = lean_string_append(v___x_1576_, v___x_1577_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1580_ = lean_string_append(v___x_1578_, v___x_1579_);
v___x_1581_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1569_, v___x_1571_);
v___x_1582_ = lean_string_append(v___x_1580_, v___x_1581_);
lean_dec_ref(v___x_1581_);
v___x_1583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1584_ = lean_string_append(v___x_1582_, v___x_1583_);
v___x_1585_ = l_mkPanicMessageWithDecl(v___x_1572_, v___x_1573_, v___x_1574_, v___x_1575_, v___x_1584_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = lean_panic_fn_borrowed(v_b_1559_, v___x_1585_);
lean_dec_ref(v_b_1559_);
v___y_1561_ = v___x_1586_;
goto v___jp_1560_;
}
else
{
lean_dec(v_val_1569_);
v___y_1561_ = v_b_1559_;
goto v___jp_1560_;
}
}
}
else
{
lean_dec(v_declName_1555_);
return v_b_1559_;
}
v___jp_1560_:
{
size_t v___x_1562_; size_t v___x_1563_; 
v___x_1562_ = ((size_t)1ULL);
v___x_1563_ = lean_usize_add(v_i_1557_, v___x_1562_);
v_i_1557_ = v___x_1563_;
v_b_1559_ = v___y_1561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1587_, lean_object* v_as_1588_, lean_object* v_i_1589_, lean_object* v_stop_1590_, lean_object* v_b_1591_){
_start:
{
size_t v_i_boxed_1592_; size_t v_stop_boxed_1593_; lean_object* v_res_1594_; 
v_i_boxed_1592_ = lean_unbox_usize(v_i_1589_);
lean_dec(v_i_1589_);
v_stop_boxed_1593_ = lean_unbox_usize(v_stop_1590_);
lean_dec(v_stop_1590_);
v_res_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1587_, v_as_1588_, v_i_boxed_1592_, v_stop_boxed_1593_, v_b_1591_);
lean_dec_ref(v_as_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1595_, lean_object* v_declName_1596_, lean_object* v_s_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = lean_array_get_size(v_eqThms_1595_);
v___x_1600_ = lean_nat_dec_lt(v___x_1598_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_dec(v_declName_1596_);
return v_s_1597_;
}
else
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_nat_dec_le(v___x_1599_, v___x_1599_);
if (v___x_1601_ == 0)
{
if (v___x_1600_ == 0)
{
lean_dec(v_declName_1596_);
return v_s_1597_;
}
else
{
size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = lean_usize_of_nat(v___x_1599_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1596_, v_eqThms_1595_, v___x_1602_, v___x_1603_, v_s_1597_);
return v___x_1604_;
}
}
else
{
size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = lean_usize_of_nat(v___x_1599_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1596_, v_eqThms_1595_, v___x_1605_, v___x_1606_, v_s_1597_);
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1608_, lean_object* v_declName_1609_, lean_object* v_s_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1608_, v_declName_1609_, v_s_1610_);
lean_dec_ref(v_eqThms_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1612_, lean_object* v_eqThms_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v_env_1618_; lean_object* v_nextMacroScope_1619_; lean_object* v_ngen_1620_; lean_object* v_auxDeclNGen_1621_; lean_object* v_traceState_1622_; lean_object* v_recordedDeps_1623_; lean_object* v_messages_1624_; lean_object* v_infoState_1625_; lean_object* v_snapshotTasks_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1642_; 
v___f_1616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1616_, 0, v_eqThms_1613_);
lean_closure_set(v___f_1616_, 1, v_declName_1612_);
v___x_1617_ = lean_st_ref_take(v_a_1614_);
v_env_1618_ = lean_ctor_get(v___x_1617_, 0);
v_nextMacroScope_1619_ = lean_ctor_get(v___x_1617_, 1);
v_ngen_1620_ = lean_ctor_get(v___x_1617_, 2);
v_auxDeclNGen_1621_ = lean_ctor_get(v___x_1617_, 3);
v_traceState_1622_ = lean_ctor_get(v___x_1617_, 4);
v_recordedDeps_1623_ = lean_ctor_get(v___x_1617_, 6);
v_messages_1624_ = lean_ctor_get(v___x_1617_, 7);
v_infoState_1625_ = lean_ctor_get(v___x_1617_, 8);
v_snapshotTasks_1626_ = lean_ctor_get(v___x_1617_, 9);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v___x_1617_, 5);
lean_dec(v_unused_1643_);
v___x_1628_ = v___x_1617_;
v_isShared_1629_ = v_isSharedCheck_1642_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_snapshotTasks_1626_);
lean_inc(v_infoState_1625_);
lean_inc(v_messages_1624_);
lean_inc(v_recordedDeps_1623_);
lean_inc(v_traceState_1622_);
lean_inc(v_auxDeclNGen_1621_);
lean_inc(v_ngen_1620_);
lean_inc(v_nextMacroScope_1619_);
lean_inc(v_env_1618_);
lean_dec(v___x_1617_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1642_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v_asyncMode_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1630_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1631_ = lean_ctor_get(v___x_1630_, 2);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_box(0);
v___x_1634_ = 1;
v___x_1635_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1630_, v_env_1618_, v___f_1616_, v_asyncMode_1631_, v___x_1633_, v___x_1634_);
v___x_1636_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 5, v___x_1636_);
lean_ctor_set(v___x_1628_, 0, v___x_1635_);
v___x_1638_ = v___x_1628_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_nextMacroScope_1619_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_ngen_1620_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_auxDeclNGen_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_traceState_1622_);
lean_ctor_set(v_reuseFailAlloc_1641_, 5, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1641_, 6, v_recordedDeps_1623_);
lean_ctor_set(v_reuseFailAlloc_1641_, 7, v_messages_1624_);
lean_ctor_set(v_reuseFailAlloc_1641_, 8, v_infoState_1625_);
lean_ctor_set(v_reuseFailAlloc_1641_, 9, v_snapshotTasks_1626_);
v___x_1638_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_st_ref_put(v_a_1614_, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1632_);
return v___x_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1644_, lean_object* v_eqThms_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1644_, v_eqThms_1645_, v_a_1646_);
lean_dec(v_a_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1649_, lean_object* v_eqThms_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1649_, v_eqThms_1650_, v_a_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1655_, lean_object* v_eqThms_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1655_, v_eqThms_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1662_, v_x_1663_, v_x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1666_, lean_object* v_x_1667_, size_t v_x_1668_, size_t v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1667_, v_x_1668_, v_x_1669_, v_x_1670_, v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_){
_start:
{
size_t v_x_1231__boxed_1679_; size_t v_x_1232__boxed_1680_; lean_object* v_res_1681_; 
v_x_1231__boxed_1679_ = lean_unbox_usize(v_x_1675_);
lean_dec(v_x_1675_);
v_x_1232__boxed_1680_ = lean_unbox_usize(v_x_1676_);
lean_dec(v_x_1676_);
v_res_1681_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1673_, v_x_1674_, v_x_1231__boxed_1679_, v_x_1232__boxed_1680_, v_x_1677_, v_x_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1682_, lean_object* v_n_1683_, lean_object* v_k_1684_, lean_object* v_v_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1683_, v_k_1684_, v_v_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1687_, size_t v_depth_1688_, lean_object* v_keys_1689_, lean_object* v_vals_1690_, lean_object* v_heq_1691_, lean_object* v_i_1692_, lean_object* v_entries_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1688_, v_keys_1689_, v_vals_1690_, v_i_1692_, v_entries_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1695_, lean_object* v_depth_1696_, lean_object* v_keys_1697_, lean_object* v_vals_1698_, lean_object* v_heq_1699_, lean_object* v_i_1700_, lean_object* v_entries_1701_){
_start:
{
size_t v_depth_boxed_1702_; lean_object* v_res_1703_; 
v_depth_boxed_1702_ = lean_unbox_usize(v_depth_1696_);
lean_dec(v_depth_1696_);
v_res_1703_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1695_, v_depth_boxed_1702_, v_keys_1697_, v_vals_1698_, v_heq_1699_, v_i_1700_, v_entries_1701_);
lean_dec_ref(v_vals_1698_);
lean_dec_ref(v_keys_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1705_, v_x_1706_, v_x_1707_, v_x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1710_, lean_object* v_env_1711_, lean_object* v_idx_1712_, lean_object* v_eqs_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_nextEq_1720_; uint8_t v___x_1721_; 
v___x_1715_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v_idx_1712_, v___x_1716_);
lean_dec(v_idx_1712_);
lean_inc(v___x_1717_);
v___x_1718_ = l_Nat_reprFast(v___x_1717_);
v___x_1719_ = lean_string_append(v___x_1715_, v___x_1718_);
lean_dec_ref(v___x_1718_);
lean_inc(v_declName_1710_);
lean_inc_ref(v_env_1711_);
v_nextEq_1720_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1711_, v_declName_1710_, v___x_1719_);
v___x_1721_ = l_Lean_Environment_containsOnBranch(v_env_1711_, v_nextEq_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec(v_nextEq_1720_);
lean_dec(v___x_1717_);
lean_dec_ref(v_env_1711_);
lean_dec(v_declName_1710_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_eqs_1713_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_array_push(v_eqs_1713_, v_nextEq_1720_);
v_idx_1712_ = v___x_1717_;
v_eqs_1713_ = v___x_1723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1725_, lean_object* v_env_1726_, lean_object* v_idx_1727_, lean_object* v_eqs_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1725_, v_env_1726_, v_idx_1727_, v_eqs_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1731_, lean_object* v_env_1732_, lean_object* v_idx_1733_, lean_object* v_eqs_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1731_, v_env_1732_, v_idx_1733_, v_eqs_1734_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1741_, lean_object* v_env_1742_, lean_object* v_idx_1743_, lean_object* v_eqs_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1741_, v_env_1742_, v_idx_1743_, v_eqs_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v_env_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; 
v___x_1754_ = lean_st_ref_get(v_a_1752_);
v_env_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_ref_n(v_env_1755_, 3);
lean_dec(v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1751_);
v___x_1757_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1755_, v_declName_1751_, v___x_1756_);
v___x_1758_ = 1;
lean_inc(v___x_1757_);
v___x_1759_ = l_Lean_Environment_contains(v_env_1755_, v___x_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v___x_1757_);
lean_dec_ref(v_env_1755_);
lean_dec(v_declName_1751_);
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_mk_empty_array_with_capacity(v___x_1762_);
v___x_1764_ = lean_array_push(v___x_1763_, v___x_1757_);
lean_inc(v_declName_1751_);
v___x_1765_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1751_, v_env_1755_, v___x_1762_, v___x_1764_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1775_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc_n(v_a_1766_, 2);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1751_, v_a_1766_, v_a_1752_);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1767_, 0);
lean_dec(v_unused_1776_);
v___x_1769_ = v___x_1767_;
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
else
{
lean_dec(v___x_1767_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_a_1766_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1771_);
v___x_1773_ = v___x_1769_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
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
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_declName_1751_);
v_a_1777_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1765_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1765_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1785_, v_a_1786_);
lean_dec(v_a_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1789_, v_a_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1803_, lean_object* v_localInsts_1804_, lean_object* v_x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1803_, v_localInsts_1804_, v_x_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1811_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1811_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1828_, lean_object* v_localInsts_1829_, lean_object* v_x_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1828_, v_localInsts_1829_, v_x_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1837_, lean_object* v_lctx_1838_, lean_object* v_localInsts_1839_, lean_object* v_x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1838_, v_localInsts_1839_, v_x_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_lctx_1848_, lean_object* v_localInsts_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1847_, v_lctx_1848_, v_localInsts_1849_, v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1860_, lean_object* v_as_x27_1861_, lean_object* v_b_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
if (lean_obj_tag(v_as_x27_1861_) == 0)
{
lean_object* v___x_1868_; 
lean_dec(v_declName_1860_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_b_1862_);
return v___x_1868_;
}
else
{
lean_object* v_head_1869_; lean_object* v_tail_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec_ref(v_b_1862_);
v_head_1869_ = lean_ctor_get(v_as_x27_1861_, 0);
v_tail_1870_ = lean_ctor_get(v_as_x27_1861_, 1);
v___x_1871_ = lean_box(0);
v___x_1872_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1869_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc_ref(v___y_1863_);
lean_inc(v_declName_1860_);
v___x_1873_ = lean_apply_6(v_head_1869_, v_declName_1860_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, lean_box(0));
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
if (lean_obj_tag(v_a_1874_) == 1)
{
lean_object* v_val_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1885_; 
v_val_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_val_1875_);
v___x_1876_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1860_, v_val_1875_, v___y_1866_);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v___x_1876_, 0);
lean_dec(v_unused_1886_);
v___x_1878_ = v___x_1876_;
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
else
{
lean_dec(v___x_1876_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1874_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1871_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
else
{
lean_dec(v_a_1874_);
v_as_x27_1861_ = v_tail_1870_;
v_b_1862_ = v___x_1872_;
goto _start;
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_declName_1860_);
v_a_1888_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1873_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1873_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1896_, lean_object* v_as_x27_1897_, lean_object* v_b_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1896_, v_as_x27_1897_, v_b_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v_as_x27_1897_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
lean_inc(v_declName_1905_);
v___x_1911_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1949_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1949_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1949_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_unbox(v_a_1912_);
lean_dec(v_a_1912_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
lean_dec(v_declName_1905_);
v___x_1917_ = lean_box(0);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1917_);
v___x_1919_ = v___x_1914_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
else
{
lean_object* v___x_1921_; 
lean_del_object(v___x_1914_);
lean_inc(v_declName_1905_);
v___x_1921_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1905_, v___y_1909_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
if (lean_obj_tag(v_a_1922_) == 1)
{
lean_dec(v_declName_1905_);
return v___x_1921_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1924_ = lean_st_ref_get(v___x_1923_);
v___x_1925_ = lean_box(0);
v___x_1926_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1927_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1905_, v___x_1924_, v___x_1926_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___x_1924_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1940_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1940_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1940_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_fst_1932_; 
v_fst_1932_ = lean_ctor_get(v_a_1928_, 0);
lean_inc(v_fst_1932_);
lean_dec(v_a_1928_);
if (lean_obj_tag(v_fst_1932_) == 0)
{
lean_object* v___x_1934_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1925_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1925_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
else
{
lean_object* v_val_1936_; lean_object* v___x_1938_; 
v_val_1936_ = lean_ctor_get(v_fst_1932_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v_fst_1932_, 1);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v_val_1936_);
v___x_1938_ = v___x_1930_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_val_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_a_1941_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1927_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1927_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
else
{
lean_dec(v_declName_1905_);
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_declName_1905_);
v_a_1950_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1911_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1911_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = lean_box(1);
v___x_1968_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1969_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___x_1968_);
lean_ctor_set(v___x_1970_, 2, v___x_1967_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___f_1979_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1979_, 0, v_declName_1973_);
v___x_1980_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1981_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1982_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1980_, v___x_1981_, v___f_1979_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1990_, lean_object* v_as_1991_, lean_object* v_as_x27_1992_, lean_object* v_b_1993_, lean_object* v_a_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1990_, v_as_x27_1992_, v_b_1993_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_2001_, lean_object* v_as_2002_, lean_object* v_as_x27_2003_, lean_object* v_b_2004_, lean_object* v_a_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_2001_, v_as_2002_, v_as_x27_2003_, v_b_2004_, v_a_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v_as_x27_2003_);
lean_dec(v_as_2002_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2018_ = lean_unsigned_to_nat(32u);
v___x_2019_ = lean_mk_empty_array_with_capacity(v___x_2018_);
lean_dec_ref(v___x_2019_);
v___x_2020_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2021_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_2012_);
v___x_2022_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_2022_, 0, v_declName_2012_);
v___x_2023_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_2023_, 0, lean_box(0));
lean_closure_set(v___x_2023_, 1, v_declName_2012_);
lean_closure_set(v___x_2023_, 2, v___x_2022_);
v___x_2024_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2020_, v___x_2021_, v___x_2023_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
return v_res_2031_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_2032_, lean_object* v_opt_2033_){
_start:
{
lean_object* v_name_2034_; lean_object* v_defValue_2035_; lean_object* v_map_2036_; lean_object* v___x_2037_; 
v_name_2034_ = lean_ctor_get(v_opt_2033_, 0);
v_defValue_2035_ = lean_ctor_get(v_opt_2033_, 1);
v_map_2036_ = lean_ctor_get(v_opts_2032_, 0);
v___x_2037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2036_, v_name_2034_);
if (lean_obj_tag(v___x_2037_) == 0)
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_unbox(v_defValue_2035_);
return v___x_2038_;
}
else
{
lean_object* v_val_2039_; 
v_val_2039_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_val_2039_);
lean_dec_ref_known(v___x_2037_, 1);
if (lean_obj_tag(v_val_2039_) == 1)
{
uint8_t v_v_2040_; 
v_v_2040_ = lean_ctor_get_uint8(v_val_2039_, 0);
lean_dec_ref_known(v_val_2039_, 0);
return v_v_2040_;
}
else
{
uint8_t v___x_2041_; 
lean_dec(v_val_2039_);
v___x_2041_ = lean_unbox(v_defValue_2035_);
return v___x_2041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_2042_, lean_object* v_opt_2043_){
_start:
{
uint8_t v_res_2044_; lean_object* v_r_2045_; 
v_res_2044_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2042_, v_opt_2043_);
lean_dec_ref(v_opt_2043_);
lean_dec_ref(v_opts_2042_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2046_, lean_object* v_as_2047_, size_t v_sz_2048_, size_t v_i_2049_, lean_object* v_b_2050_){
_start:
{
lean_object* v_a_2053_; uint8_t v___x_2057_; 
v___x_2057_ = lean_usize_dec_lt(v_i_2049_, v_sz_2048_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_b_2050_);
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; lean_object* v_defValue_2060_; uint8_t v___x_2061_; uint8_t v___y_2075_; uint8_t v___x_2076_; 
v_a_2059_ = lean_array_uget(v_as_2047_, v_i_2049_);
v_defValue_2060_ = lean_ctor_get(v_a_2059_, 1);
v___x_2061_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2046_, v_a_2059_);
v___x_2076_ = lean_unbox(v_defValue_2060_);
if (v___x_2076_ == 0)
{
if (v___x_2061_ == 0)
{
v___y_2075_ = v___x_2057_;
goto v___jp_2074_;
}
else
{
goto v___jp_2062_;
}
}
else
{
v___y_2075_ = v___x_2061_;
goto v___jp_2074_;
}
v___jp_2062_:
{
lean_object* v_name_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2072_; 
v_name_2063_ = lean_ctor_get(v_a_2059_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_a_2059_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v_a_2059_, 1);
lean_dec(v_unused_2073_);
v___x_2065_ = v_a_2059_;
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_name_2063_);
lean_dec(v_a_2059_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2067_, 0, v___x_2061_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 1, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_name_2063_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_array_push(v_b_2050_, v___x_2069_);
v_a_2053_ = v___x_2070_;
goto v___jp_2052_;
}
}
}
v___jp_2074_:
{
if (v___y_2075_ == 0)
{
goto v___jp_2062_;
}
else
{
lean_dec(v_a_2059_);
v_a_2053_ = v_b_2050_;
goto v___jp_2052_;
}
}
}
v___jp_2052_:
{
size_t v___x_2054_; size_t v___x_2055_; 
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_add(v_i_2049_, v___x_2054_);
v_i_2049_ = v___x_2055_;
v_b_2050_ = v_a_2053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2077_, lean_object* v_as_2078_, lean_object* v_sz_2079_, lean_object* v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2079_);
lean_dec(v_sz_2079_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2080_);
lean_dec(v_i_2080_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2077_, v_as_2078_, v_sz_boxed_2083_, v_i_boxed_2084_, v_b_2081_);
lean_dec_ref(v_as_2078_);
lean_dec_ref(v___x_2077_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; lean_object* v_env_2093_; uint8_t v___x_2094_; lean_object* v_env_2095_; lean_object* v___x_2096_; lean_object* v_toCold_2097_; lean_object* v_mctx_2098_; lean_object* v_lctx_2099_; lean_object* v_options_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2092_ = lean_st_ref_get(v___y_2090_);
v_env_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc_ref(v_env_2093_);
lean_dec(v___x_2092_);
v___x_2094_ = 0;
v_env_2095_ = l_Lean_Environment_setRecordingDeps(v_env_2093_, v___x_2094_);
v___x_2096_ = lean_st_ref_get(v___y_2088_);
v_toCold_2097_ = lean_ctor_get(v___y_2089_, 0);
v_mctx_2098_ = lean_ctor_get(v___x_2096_, 0);
lean_inc_ref(v_mctx_2098_);
lean_dec(v___x_2096_);
v_lctx_2099_ = lean_ctor_get(v___y_2087_, 2);
v_options_2100_ = lean_ctor_get(v_toCold_2097_, 2);
lean_inc_ref(v_options_2100_);
lean_inc_ref(v_lctx_2099_);
v___x_2101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2101_, 0, v_env_2095_);
lean_ctor_set(v___x_2101_, 1, v_mctx_2098_);
lean_ctor_set(v___x_2101_, 2, v_lctx_2099_);
lean_ctor_set(v___x_2101_, 3, v_options_2100_);
v___x_2102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v_msgData_2086_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2111_; double v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = lean_float_of_nat(v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2116_, lean_object* v_msg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_ref_2123_; lean_object* v___x_2124_; lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2170_; 
v_ref_2123_ = lean_ctor_get(v___y_2120_, 2);
v___x_2124_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2170_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2170_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v_traceState_2130_; lean_object* v_env_2131_; lean_object* v_nextMacroScope_2132_; lean_object* v_ngen_2133_; lean_object* v_auxDeclNGen_2134_; lean_object* v_cache_2135_; lean_object* v_recordedDeps_2136_; lean_object* v_messages_2137_; lean_object* v_infoState_2138_; lean_object* v_snapshotTasks_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2169_; 
v___x_2129_ = lean_st_ref_take(v___y_2121_);
v_traceState_2130_ = lean_ctor_get(v___x_2129_, 4);
v_env_2131_ = lean_ctor_get(v___x_2129_, 0);
v_nextMacroScope_2132_ = lean_ctor_get(v___x_2129_, 1);
v_ngen_2133_ = lean_ctor_get(v___x_2129_, 2);
v_auxDeclNGen_2134_ = lean_ctor_get(v___x_2129_, 3);
v_cache_2135_ = lean_ctor_get(v___x_2129_, 5);
v_recordedDeps_2136_ = lean_ctor_get(v___x_2129_, 6);
v_messages_2137_ = lean_ctor_get(v___x_2129_, 7);
v_infoState_2138_ = lean_ctor_get(v___x_2129_, 8);
v_snapshotTasks_2139_ = lean_ctor_get(v___x_2129_, 9);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2141_ = v___x_2129_;
v_isShared_2142_ = v_isSharedCheck_2169_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snapshotTasks_2139_);
lean_inc(v_infoState_2138_);
lean_inc(v_messages_2137_);
lean_inc(v_recordedDeps_2136_);
lean_inc(v_cache_2135_);
lean_inc(v_traceState_2130_);
lean_inc(v_auxDeclNGen_2134_);
lean_inc(v_ngen_2133_);
lean_inc(v_nextMacroScope_2132_);
lean_inc(v_env_2131_);
lean_dec(v___x_2129_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2169_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
uint64_t v_tid_2143_; lean_object* v_traces_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2168_; 
v_tid_2143_ = lean_ctor_get_uint64(v_traceState_2130_, sizeof(void*)*1);
v_traces_2144_ = lean_ctor_get(v_traceState_2130_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_traceState_2130_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2146_ = v_traceState_2130_;
v_isShared_2147_ = v_isSharedCheck_2168_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_traces_2144_);
lean_dec(v_traceState_2130_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2168_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; double v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2151_ = 0;
v___x_2152_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2153_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2153_, 0, v_cls_2116_);
lean_ctor_set(v___x_2153_, 1, v___x_2149_);
lean_ctor_set(v___x_2153_, 2, v___x_2152_);
lean_ctor_set_float(v___x_2153_, sizeof(void*)*3, v___x_2150_);
lean_ctor_set_float(v___x_2153_, sizeof(void*)*3 + 8, v___x_2150_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*3 + 16, v___x_2151_);
v___x_2154_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2155_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v_a_2125_);
lean_ctor_set(v___x_2155_, 2, v___x_2154_);
lean_inc(v_ref_2123_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v_ref_2123_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = l_Lean_PersistentArray_push___redArg(v_traces_2144_, v___x_2156_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2157_);
v___x_2159_ = v___x_2146_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2157_);
lean_ctor_set_uint64(v_reuseFailAlloc_2167_, sizeof(void*)*1, v_tid_2143_);
v___x_2159_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v___x_2159_);
v___x_2161_ = v___x_2141_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_env_2131_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_nextMacroScope_2132_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_ngen_2133_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_auxDeclNGen_2134_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2166_, 5, v_cache_2135_);
lean_ctor_set(v_reuseFailAlloc_2166_, 6, v_recordedDeps_2136_);
lean_ctor_set(v_reuseFailAlloc_2166_, 7, v_messages_2137_);
lean_ctor_set(v_reuseFailAlloc_2166_, 8, v_infoState_2138_);
lean_ctor_set(v_reuseFailAlloc_2166_, 9, v_snapshotTasks_2139_);
v___x_2161_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = lean_st_ref_put(v___y_2121_, v___x_2161_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2148_);
v___x_2164_ = v___x_2127_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2148_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2171_, lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2171_, v_msg_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v_res_2178_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2181_; size_t v_sz_2182_; 
v___x_2181_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2182_ = lean_array_size(v___x_2181_);
return v_sz_2182_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2184_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
lean_ctor_set(v___x_2184_, 2, v___x_2183_);
lean_ctor_set(v___x_2184_, 3, v___x_2183_);
lean_ctor_set(v___x_2184_, 4, v___x_2183_);
lean_ctor_set(v___x_2184_, 5, v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2193_ = l_Lean_Name_append(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; size_t v_sz_2207_; size_t v___x_2208_; lean_object* v___x_2209_; 
v___x_2203_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2200_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2206_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2207_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2208_ = ((size_t)0ULL);
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2203_, v___x_2206_, v_sz_2207_, v___x_2208_, v___x_2205_);
lean_dec_ref(v___x_2203_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2273_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2273_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2273_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___y_2217_; lean_object* v___y_2218_; 
v___x_2214_ = lean_array_get_size(v_a_2210_);
v___x_2215_ = lean_nat_dec_eq(v___x_2214_, v___x_2204_);
if (v___x_2215_ == 0)
{
lean_object* v_toCold_2260_; lean_object* v_options_2261_; uint8_t v_hasTrace_2262_; 
v_toCold_2260_ = lean_ctor_get(v_a_2200_, 0);
v_options_2261_ = lean_ctor_get(v_toCold_2260_, 2);
v_hasTrace_2262_ = lean_ctor_get_uint8(v_options_2261_, sizeof(void*)*1);
if (v_hasTrace_2262_ == 0)
{
v___y_2217_ = v_a_2199_;
v___y_2218_ = v_a_2201_;
goto v___jp_2216_;
}
else
{
lean_object* v_inheritedTraceOptions_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_inheritedTraceOptions_2263_ = lean_ctor_get(v_toCold_2260_, 11);
v___x_2264_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2265_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2263_, v_options_2261_, v___x_2265_);
if (v___x_2266_ == 0)
{
v___y_2217_ = v_a_2199_;
v___y_2218_ = v_a_2201_;
goto v___jp_2216_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2267_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2197_);
v___x_2268_ = l_Lean_MessageData_ofName(v_declName_2197_);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2264_, v___x_2269_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_dec_ref_known(v___x_2270_, 1);
v___y_2217_ = v_a_2199_;
v___y_2218_ = v_a_2201_;
goto v___jp_2216_;
}
else
{
lean_del_object(v___x_2212_);
lean_dec(v_a_2210_);
lean_dec(v_declName_2197_);
return v___x_2270_;
}
}
}
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_del_object(v___x_2212_);
lean_dec(v_a_2210_);
lean_dec(v_declName_2197_);
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
v___jp_2216_:
{
lean_object* v___x_2219_; lean_object* v_env_2220_; lean_object* v_nextMacroScope_2221_; lean_object* v_ngen_2222_; lean_object* v_auxDeclNGen_2223_; lean_object* v_traceState_2224_; lean_object* v_recordedDeps_2225_; lean_object* v_messages_2226_; lean_object* v_infoState_2227_; lean_object* v_snapshotTasks_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2258_; 
v___x_2219_ = lean_st_ref_take(v___y_2218_);
v_env_2220_ = lean_ctor_get(v___x_2219_, 0);
v_nextMacroScope_2221_ = lean_ctor_get(v___x_2219_, 1);
v_ngen_2222_ = lean_ctor_get(v___x_2219_, 2);
v_auxDeclNGen_2223_ = lean_ctor_get(v___x_2219_, 3);
v_traceState_2224_ = lean_ctor_get(v___x_2219_, 4);
v_recordedDeps_2225_ = lean_ctor_get(v___x_2219_, 6);
v_messages_2226_ = lean_ctor_get(v___x_2219_, 7);
v_infoState_2227_ = lean_ctor_get(v___x_2219_, 8);
v_snapshotTasks_2228_ = lean_ctor_get(v___x_2219_, 9);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; 
v_unused_2259_ = lean_ctor_get(v___x_2219_, 5);
lean_dec(v_unused_2259_);
v___x_2230_ = v___x_2219_;
v_isShared_2231_ = v_isSharedCheck_2258_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_snapshotTasks_2228_);
lean_inc(v_infoState_2227_);
lean_inc(v_messages_2226_);
lean_inc(v_recordedDeps_2225_);
lean_inc(v_traceState_2224_);
lean_inc(v_auxDeclNGen_2223_);
lean_inc(v_ngen_2222_);
lean_inc(v_nextMacroScope_2221_);
lean_inc(v_env_2220_);
lean_dec(v___x_2219_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2258_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2232_ = l_Lean_Meta_eqnOptionsExt;
v___x_2233_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2232_, v_env_2220_, v_declName_2197_, v_a_2210_, v___x_2215_);
v___x_2234_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 5, v___x_2234_);
lean_ctor_set(v___x_2230_, 0, v___x_2233_);
v___x_2236_ = v___x_2230_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_nextMacroScope_2221_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_ngen_2222_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_auxDeclNGen_2223_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_traceState_2224_);
lean_ctor_set(v_reuseFailAlloc_2257_, 5, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2257_, 6, v_recordedDeps_2225_);
lean_ctor_set(v_reuseFailAlloc_2257_, 7, v_messages_2226_);
lean_ctor_set(v_reuseFailAlloc_2257_, 8, v_infoState_2227_);
lean_ctor_set(v_reuseFailAlloc_2257_, 9, v_snapshotTasks_2228_);
v___x_2236_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_mctx_2239_; lean_object* v_zetaDeltaFVarIds_2240_; lean_object* v_postponed_2241_; lean_object* v_diag_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2255_; 
v___x_2237_ = lean_st_ref_put(v___y_2218_, v___x_2236_);
v___x_2238_ = lean_st_ref_take(v___y_2217_);
v_mctx_2239_ = lean_ctor_get(v___x_2238_, 0);
v_zetaDeltaFVarIds_2240_ = lean_ctor_get(v___x_2238_, 2);
v_postponed_2241_ = lean_ctor_get(v___x_2238_, 3);
v_diag_2242_ = lean_ctor_get(v___x_2238_, 4);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2238_, 1);
lean_dec(v_unused_2256_);
v___x_2244_ = v___x_2238_;
v_isShared_2245_ = v_isSharedCheck_2255_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_diag_2242_);
lean_inc(v_postponed_2241_);
lean_inc(v_zetaDeltaFVarIds_2240_);
lean_inc(v_mctx_2239_);
lean_dec(v___x_2238_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2255_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2246_ = lean_box(0);
v___x_2247_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 1, v___x_2247_);
v___x_2249_ = v___x_2244_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_mctx_2239_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_zetaDeltaFVarIds_2240_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_postponed_2241_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_diag_2242_);
v___x_2249_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_st_ref_put(v___y_2217_, v___x_2249_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2246_);
v___x_2252_ = v___x_2212_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2246_);
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
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_declName_2197_);
v_a_2274_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2209_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2209_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2289_, lean_object* v_as_2290_, size_t v_sz_2291_, size_t v_i_2292_, lean_object* v_b_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2289_, v_as_2290_, v_sz_2291_, v_i_2292_, v_b_2293_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2300_, lean_object* v_as_2301_, lean_object* v_sz_2302_, lean_object* v_i_2303_, lean_object* v_b_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
size_t v_sz_boxed_2310_; size_t v_i_boxed_2311_; lean_object* v_res_2312_; 
v_sz_boxed_2310_ = lean_unbox_usize(v_sz_2302_);
lean_dec(v_sz_2302_);
v_i_boxed_2311_ = lean_unbox_usize(v_i_2303_);
lean_dec(v_i_2303_);
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2300_, v_as_2301_, v_sz_boxed_2310_, v_i_boxed_2311_, v_b_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v_as_2301_);
lean_dec_ref(v___x_2300_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = lean_st_mk_ref(v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2319_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = l_Lean_initializing();
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_f_2319_);
v___x_2322_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2324_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2325_ = lean_st_ref_take(v___x_2324_);
v___x_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_f_2319_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_st_ref_put(v___x_2324_, v___x_2326_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2335_, lean_object* v_as_x27_2336_, lean_object* v_b_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
if (lean_obj_tag(v_as_x27_2336_) == 0)
{
lean_object* v___x_2343_; 
lean_dec(v_declName_2335_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_b_2337_);
return v___x_2343_;
}
else
{
lean_object* v_head_2344_; lean_object* v_tail_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec_ref(v_b_2337_);
v_head_2344_ = lean_ctor_get(v_as_x27_2336_, 0);
v_tail_2345_ = lean_ctor_get(v_as_x27_2336_, 1);
v___x_2346_ = lean_box(0);
v___x_2347_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2344_);
lean_inc(v___y_2341_);
lean_inc_ref(v___y_2340_);
lean_inc(v___y_2339_);
lean_inc_ref(v___y_2338_);
lean_inc(v_declName_2335_);
v___x_2348_ = lean_apply_6(v_head_2344_, v_declName_2335_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, lean_box(0));
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2359_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2359_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2359_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
if (lean_obj_tag(v_a_2349_) == 1)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec(v_declName_2335_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_a_2349_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_2346_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2354_);
v___x_2356_ = v___x_2351_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
else
{
lean_del_object(v___x_2351_);
lean_dec(v_a_2349_);
v_as_x27_2336_ = v_tail_2345_;
v_b_2337_ = v___x_2347_;
goto _start;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_declName_2335_);
v_a_2360_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2348_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2348_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2368_, lean_object* v_as_x27_2369_, lean_object* v_b_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2368_, v_as_x27_2369_, v_b_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v_as_x27_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2377_, lean_object* v_declName_2378_, uint8_t v_nonRec_2379_, lean_object* v___x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2389_; lean_object* v_env_2390_; uint8_t v___x_2391_; uint8_t v___x_2392_; 
v___x_2389_ = lean_st_ref_get(v___y_2384_);
v_env_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc_ref(v_env_2390_);
lean_dec(v___x_2389_);
v___x_2391_ = 1;
lean_inc(v___x_2377_);
v___x_2392_ = l_Lean_Environment_contains(v_env_2390_, v___x_2377_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v___x_2377_);
lean_inc(v_declName_2378_);
v___x_2393_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2378_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; uint8_t v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = lean_unbox(v_a_2394_);
lean_dec(v_a_2394_);
if (v___x_2395_ == 0)
{
lean_dec_ref(v___x_2380_);
lean_dec(v_declName_2378_);
goto v___jp_2386_;
}
else
{
lean_object* v___x_2396_; 
lean_inc(v_declName_2378_);
v___x_2396_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2378_, v___y_2384_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; uint8_t v___x_2398_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = lean_unbox(v_a_2397_);
lean_dec(v_a_2397_);
if (v___x_2398_ == 0)
{
if (v_nonRec_2379_ == 0)
{
lean_dec_ref(v___x_2380_);
lean_dec(v_declName_2378_);
goto v___jp_2386_;
}
else
{
lean_object* v___x_2399_; lean_object* v_env_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2399_ = lean_st_ref_get(v___y_2384_);
v_env_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc_ref(v_env_2400_);
lean_dec(v___x_2399_);
lean_inc(v_declName_2378_);
v___x_2401_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2400_, v_declName_2378_, v___x_2380_);
v___x_2402_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2378_, v___x_2401_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v___x_2380_);
v___x_2403_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2404_ = lean_st_ref_get(v___x_2403_);
v___x_2405_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2406_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2378_, v___x_2404_, v___x_2405_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___x_2404_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2416_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_fst_2411_; 
v_fst_2411_ = lean_ctor_get(v_a_2407_, 0);
lean_inc(v_fst_2411_);
lean_dec(v_a_2407_);
if (lean_obj_tag(v_fst_2411_) == 0)
{
lean_del_object(v___x_2409_);
goto v___jp_2386_;
}
else
{
lean_object* v_val_2412_; lean_object* v___x_2414_; 
v_val_2412_ = lean_ctor_get(v_fst_2411_, 0);
lean_inc(v_val_2412_);
lean_dec_ref_known(v_fst_2411_, 1);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v_val_2412_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_val_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2417_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2406_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2406_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v___x_2380_);
lean_dec(v_declName_2378_);
v_a_2425_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2396_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2396_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v___x_2380_);
lean_dec(v_declName_2378_);
v_a_2433_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2393_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2393_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v___x_2380_);
lean_dec(v_declName_2378_);
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2377_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
v___jp_2386_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2443_, lean_object* v_declName_2444_, lean_object* v_nonRec_2445_, lean_object* v___x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_nonRec_boxed_2452_; lean_object* v_res_2453_; 
v_nonRec_boxed_2452_ = lean_unbox(v_nonRec_2445_);
v_res_2453_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2443_, v_declName_2444_, v_nonRec_boxed_2452_, v___x_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
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
v___x_2461_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
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
v___x_2570_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
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
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2659_, 0, v___x_2657_);
lean_closure_set(v___f_2659_, 1, v_declName_2647_);
lean_closure_set(v___f_2659_, 2, v___x_2658_);
lean_closure_set(v___f_2659_, 3, v___x_2656_);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2737_, lean_object* v_x_2738_, uint8_t v_isExporting_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2738_, v_isExporting_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2746_, lean_object* v_x_2747_, lean_object* v_isExporting_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v_isExporting_boxed_2754_; lean_object* v_res_2755_; 
v_isExporting_boxed_2754_ = lean_unbox(v_isExporting_2748_);
v_res_2755_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2746_, v_x_2747_, v_isExporting_boxed_2754_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2756_, lean_object* v_x_2757_, uint8_t v_when_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2757_, v_when_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2765_, lean_object* v_x_2766_, lean_object* v_when_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
uint8_t v_when_boxed_2773_; lean_object* v_res_2774_; 
v_when_boxed_2773_ = lean_unbox(v_when_2767_);
v_res_2774_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2765_, v_x_2766_, v_when_boxed_2773_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2775_, lean_object* v_msg_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_msg_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2783_, v_msg_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
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
lean_object* v_toCold_2931_; lean_object* v_currRecDepth_2932_; lean_object* v_ref_2933_; uint16_t v_optionFlags_2934_; uint8_t v_suppressElabErrors_2935_; uint8_t v_isRecordingDeps_2936_; lean_object* v_ref_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_traceState_2940_; lean_object* v_traces_2941_; lean_object* v___x_2942_; size_t v_sz_2943_; size_t v___x_2944_; lean_object* v___x_2945_; lean_object* v_msg_2946_; lean_object* v___x_2947_; lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2986_; 
v_toCold_2931_ = lean_ctor_get(v___y_2928_, 0);
v_currRecDepth_2932_ = lean_ctor_get(v___y_2928_, 1);
v_ref_2933_ = lean_ctor_get(v___y_2928_, 2);
v_optionFlags_2934_ = lean_ctor_get_uint16(v___y_2928_, sizeof(void*)*3);
v_suppressElabErrors_2935_ = lean_ctor_get_uint8(v___y_2928_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2936_ = lean_ctor_get_uint8(v___y_2928_, sizeof(void*)*3 + 3);
v_ref_2937_ = l_Lean_replaceRef(v_ref_2926_, v_ref_2933_);
lean_inc(v_currRecDepth_2932_);
lean_inc_ref(v_toCold_2931_);
v___x_2938_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2938_, 0, v_toCold_2931_);
lean_ctor_set(v___x_2938_, 1, v_currRecDepth_2932_);
lean_ctor_set(v___x_2938_, 2, v_ref_2937_);
lean_ctor_set_uint16(v___x_2938_, sizeof(void*)*3, v_optionFlags_2934_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*3 + 2, v_suppressElabErrors_2935_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*3 + 3, v_isRecordingDeps_2936_);
v___x_2939_ = lean_st_ref_get(v___y_2929_);
v_traceState_2940_ = lean_ctor_get(v___x_2939_, 4);
lean_inc_ref(v_traceState_2940_);
lean_dec(v___x_2939_);
v_traces_2941_ = lean_ctor_get(v_traceState_2940_, 0);
lean_inc_ref(v_traces_2941_);
lean_dec_ref(v_traceState_2940_);
v___x_2942_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2941_);
lean_dec_ref(v_traces_2941_);
v_sz_2943_ = lean_array_size(v___x_2942_);
v___x_2944_ = ((size_t)0ULL);
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2943_, v___x_2944_, v___x_2942_);
v_msg_2946_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2946_, 0, v_data_2925_);
lean_ctor_set(v_msg_2946_, 1, v_msg_2927_);
lean_ctor_set(v_msg_2946_, 2, v___x_2945_);
v___x_2947_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2946_, v___x_2938_, v___y_2929_);
lean_dec_ref_known(v___x_2938_, 3);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2986_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2986_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v_traceState_2953_; lean_object* v_env_2954_; lean_object* v_nextMacroScope_2955_; lean_object* v_ngen_2956_; lean_object* v_auxDeclNGen_2957_; lean_object* v_cache_2958_; lean_object* v_recordedDeps_2959_; lean_object* v_messages_2960_; lean_object* v_infoState_2961_; lean_object* v_snapshotTasks_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2985_; 
v___x_2952_ = lean_st_ref_take(v___y_2929_);
v_traceState_2953_ = lean_ctor_get(v___x_2952_, 4);
v_env_2954_ = lean_ctor_get(v___x_2952_, 0);
v_nextMacroScope_2955_ = lean_ctor_get(v___x_2952_, 1);
v_ngen_2956_ = lean_ctor_get(v___x_2952_, 2);
v_auxDeclNGen_2957_ = lean_ctor_get(v___x_2952_, 3);
v_cache_2958_ = lean_ctor_get(v___x_2952_, 5);
v_recordedDeps_2959_ = lean_ctor_get(v___x_2952_, 6);
v_messages_2960_ = lean_ctor_get(v___x_2952_, 7);
v_infoState_2961_ = lean_ctor_get(v___x_2952_, 8);
v_snapshotTasks_2962_ = lean_ctor_get(v___x_2952_, 9);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2964_ = v___x_2952_;
v_isShared_2965_ = v_isSharedCheck_2985_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_snapshotTasks_2962_);
lean_inc(v_infoState_2961_);
lean_inc(v_messages_2960_);
lean_inc(v_recordedDeps_2959_);
lean_inc(v_cache_2958_);
lean_inc(v_traceState_2953_);
lean_inc(v_auxDeclNGen_2957_);
lean_inc(v_ngen_2956_);
lean_inc(v_nextMacroScope_2955_);
lean_inc(v_env_2954_);
lean_dec(v___x_2952_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2985_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
uint64_t v_tid_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2983_; 
v_tid_2966_ = lean_ctor_get_uint64(v_traceState_2953_, sizeof(void*)*1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_traceState_2953_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_traceState_2953_, 0);
lean_dec(v_unused_2984_);
v___x_2968_ = v_traceState_2953_;
v_isShared_2969_ = v_isSharedCheck_2983_;
goto v_resetjp_2967_;
}
else
{
lean_dec(v_traceState_2953_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2983_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2970_ = lean_box(0);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_ref_2926_);
lean_ctor_set(v___x_2971_, 1, v_a_2948_);
v___x_2972_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2924_, v___x_2971_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2972_);
v___x_2974_ = v___x_2968_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2972_);
lean_ctor_set_uint64(v_reuseFailAlloc_2982_, sizeof(void*)*1, v_tid_2966_);
v___x_2974_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 4, v___x_2974_);
v___x_2976_ = v___x_2964_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_env_2954_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_nextMacroScope_2955_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_ngen_2956_);
lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_auxDeclNGen_2957_);
lean_ctor_set(v_reuseFailAlloc_2981_, 4, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2981_, 5, v_cache_2958_);
lean_ctor_set(v_reuseFailAlloc_2981_, 6, v_recordedDeps_2959_);
lean_ctor_set(v_reuseFailAlloc_2981_, 7, v_messages_2960_);
lean_ctor_set(v_reuseFailAlloc_2981_, 8, v_infoState_2961_);
lean_ctor_set(v_reuseFailAlloc_2981_, 9, v_snapshotTasks_2962_);
v___x_2976_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = lean_st_ref_put(v___y_2929_, v___x_2976_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2970_);
v___x_2979_ = v___x_2950_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2970_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2987_, lean_object* v_data_2988_, lean_object* v_ref_2989_, lean_object* v_msg_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2987_, v_data_2988_, v_ref_2989_, v_msg_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
return v_res_2994_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2997_ = l_Lean_stringToMessageData(v___x_2996_);
return v___x_2997_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2998_; double v___x_2999_; 
v___x_2998_ = lean_unsigned_to_nat(1000u);
v___x_2999_ = lean_float_of_nat(v___x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_3000_, uint8_t v_collapsed_3001_, lean_object* v_tag_3002_, lean_object* v_opts_3003_, uint8_t v_clsEnabled_3004_, lean_object* v_oldTraces_3005_, lean_object* v_msg_3006_, lean_object* v_resStartStop_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_fst_3011_; lean_object* v_snd_3012_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v_data_3016_; lean_object* v_fst_3027_; lean_object* v_snd_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___y_3032_; lean_object* v_a_3033_; uint8_t v___y_3048_; double v___y_3080_; 
v_fst_3011_ = lean_ctor_get(v_resStartStop_3007_, 0);
lean_inc(v_fst_3011_);
v_snd_3012_ = lean_ctor_get(v_resStartStop_3007_, 1);
lean_inc(v_snd_3012_);
lean_dec_ref(v_resStartStop_3007_);
v_fst_3027_ = lean_ctor_get(v_snd_3012_, 0);
lean_inc(v_fst_3027_);
v_snd_3028_ = lean_ctor_get(v_snd_3012_, 1);
lean_inc(v_snd_3028_);
lean_dec(v_snd_3012_);
v___x_3029_ = l_Lean_trace_profiler;
v___x_3030_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_3003_, v___x_3029_);
if (v___x_3030_ == 0)
{
v___y_3048_ = v___x_3030_;
goto v___jp_3047_;
}
else
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3086_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_3003_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; double v___x_3089_; double v___x_3090_; double v___x_3091_; 
v___x_3087_ = l_Lean_trace_profiler_threshold;
v___x_3088_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_3003_, v___x_3087_);
v___x_3089_ = lean_float_of_nat(v___x_3088_);
v___x_3090_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3091_ = lean_float_div(v___x_3089_, v___x_3090_);
v___y_3080_ = v___x_3091_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; double v___x_3094_; 
v___x_3092_ = l_Lean_trace_profiler_threshold;
v___x_3093_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_3003_, v___x_3092_);
v___x_3094_ = lean_float_of_nat(v___x_3093_);
v___y_3080_ = v___x_3094_;
goto v___jp_3079_;
}
}
v___jp_3013_:
{
lean_object* v___x_3017_; 
lean_inc(v___y_3015_);
v___x_3017_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_3005_, v_data_3016_, v___y_3015_, v___y_3014_, v___y_3008_, v___y_3009_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3018_; 
lean_dec_ref_known(v___x_3017_, 1);
v___x_3018_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_3011_);
return v___x_3018_;
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_fst_3011_);
v_a_3019_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3017_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3017_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
v___jp_3031_:
{
uint8_t v_result_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; double v___x_3037_; lean_object* v_data_3038_; 
v_result_3034_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_3011_);
v___x_3035_ = lean_box(v_result_3034_);
v___x_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
v___x_3037_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_3002_);
lean_inc_ref(v___x_3036_);
lean_inc(v_cls_3000_);
v_data_3038_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3038_, 0, v_cls_3000_);
lean_ctor_set(v_data_3038_, 1, v___x_3036_);
lean_ctor_set(v_data_3038_, 2, v_tag_3002_);
lean_ctor_set_float(v_data_3038_, sizeof(void*)*3, v___x_3037_);
lean_ctor_set_float(v_data_3038_, sizeof(void*)*3 + 8, v___x_3037_);
lean_ctor_set_uint8(v_data_3038_, sizeof(void*)*3 + 16, v_collapsed_3001_);
if (v___x_3030_ == 0)
{
lean_dec_ref_known(v___x_3036_, 1);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_dec_ref(v_tag_3002_);
lean_dec(v_cls_3000_);
v___y_3014_ = v_a_3033_;
v___y_3015_ = v___y_3032_;
v_data_3016_ = v_data_3038_;
goto v___jp_3013_;
}
else
{
lean_object* v_data_3039_; double v___x_3040_; double v___x_3041_; 
lean_dec_ref_known(v_data_3038_, 3);
v_data_3039_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3039_, 0, v_cls_3000_);
lean_ctor_set(v_data_3039_, 1, v___x_3036_);
lean_ctor_set(v_data_3039_, 2, v_tag_3002_);
v___x_3040_ = lean_unbox_float(v_fst_3027_);
lean_dec(v_fst_3027_);
lean_ctor_set_float(v_data_3039_, sizeof(void*)*3, v___x_3040_);
v___x_3041_ = lean_unbox_float(v_snd_3028_);
lean_dec(v_snd_3028_);
lean_ctor_set_float(v_data_3039_, sizeof(void*)*3 + 8, v___x_3041_);
lean_ctor_set_uint8(v_data_3039_, sizeof(void*)*3 + 16, v_collapsed_3001_);
v___y_3014_ = v_a_3033_;
v___y_3015_ = v___y_3032_;
v_data_3016_ = v_data_3039_;
goto v___jp_3013_;
}
}
v___jp_3042_:
{
lean_object* v_ref_3043_; lean_object* v___x_3044_; 
v_ref_3043_ = lean_ctor_get(v___y_3008_, 2);
lean_inc(v___y_3009_);
lean_inc_ref(v___y_3008_);
lean_inc(v_fst_3011_);
v___x_3044_ = lean_apply_4(v_msg_3006_, v_fst_3011_, v___y_3008_, v___y_3009_, lean_box(0));
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___y_3032_ = v_ref_3043_;
v_a_3033_ = v_a_3045_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3046_; 
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_3032_ = v_ref_3043_;
v_a_3033_ = v___x_3046_;
goto v___jp_3031_;
}
}
v___jp_3047_:
{
if (v_clsEnabled_3004_ == 0)
{
if (v___y_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v_traceState_3050_; lean_object* v_env_3051_; lean_object* v_nextMacroScope_3052_; lean_object* v_ngen_3053_; lean_object* v_auxDeclNGen_3054_; lean_object* v_cache_3055_; lean_object* v_recordedDeps_3056_; lean_object* v_messages_3057_; lean_object* v_infoState_3058_; lean_object* v_snapshotTasks_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_dec_ref(v_msg_3006_);
lean_dec_ref(v_tag_3002_);
lean_dec(v_cls_3000_);
v___x_3049_ = lean_st_ref_take(v___y_3009_);
v_traceState_3050_ = lean_ctor_get(v___x_3049_, 4);
v_env_3051_ = lean_ctor_get(v___x_3049_, 0);
v_nextMacroScope_3052_ = lean_ctor_get(v___x_3049_, 1);
v_ngen_3053_ = lean_ctor_get(v___x_3049_, 2);
v_auxDeclNGen_3054_ = lean_ctor_get(v___x_3049_, 3);
v_cache_3055_ = lean_ctor_get(v___x_3049_, 5);
v_recordedDeps_3056_ = lean_ctor_get(v___x_3049_, 6);
v_messages_3057_ = lean_ctor_get(v___x_3049_, 7);
v_infoState_3058_ = lean_ctor_get(v___x_3049_, 8);
v_snapshotTasks_3059_ = lean_ctor_get(v___x_3049_, 9);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3061_ = v___x_3049_;
v_isShared_3062_ = v_isSharedCheck_3078_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_snapshotTasks_3059_);
lean_inc(v_infoState_3058_);
lean_inc(v_messages_3057_);
lean_inc(v_recordedDeps_3056_);
lean_inc(v_cache_3055_);
lean_inc(v_traceState_3050_);
lean_inc(v_auxDeclNGen_3054_);
lean_inc(v_ngen_3053_);
lean_inc(v_nextMacroScope_3052_);
lean_inc(v_env_3051_);
lean_dec(v___x_3049_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3078_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
uint64_t v_tid_3063_; lean_object* v_traces_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3077_; 
v_tid_3063_ = lean_ctor_get_uint64(v_traceState_3050_, sizeof(void*)*1);
v_traces_3064_ = lean_ctor_get(v_traceState_3050_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_traceState_3050_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3066_ = v_traceState_3050_;
v_isShared_3067_ = v_isSharedCheck_3077_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_traces_3064_);
lean_dec(v_traceState_3050_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3077_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3068_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3005_, v_traces_3064_);
lean_dec_ref(v_traces_3064_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3068_);
lean_ctor_set_uint64(v_reuseFailAlloc_3076_, sizeof(void*)*1, v_tid_3063_);
v___x_3070_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3072_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 4, v___x_3070_);
v___x_3072_ = v___x_3061_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_env_3051_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_nextMacroScope_3052_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_ngen_3053_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_auxDeclNGen_3054_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3075_, 5, v_cache_3055_);
lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_recordedDeps_3056_);
lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_messages_3057_);
lean_ctor_set(v_reuseFailAlloc_3075_, 8, v_infoState_3058_);
lean_ctor_set(v_reuseFailAlloc_3075_, 9, v_snapshotTasks_3059_);
v___x_3072_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_st_ref_put(v___y_3009_, v___x_3072_);
v___x_3074_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_3011_);
return v___x_3074_;
}
}
}
}
}
else
{
goto v___jp_3042_;
}
}
else
{
goto v___jp_3042_;
}
}
v___jp_3079_:
{
double v___x_3081_; double v___x_3082_; double v___x_3083_; uint8_t v___x_3084_; 
v___x_3081_ = lean_unbox_float(v_snd_3028_);
v___x_3082_ = lean_unbox_float(v_fst_3027_);
v___x_3083_ = lean_float_sub(v___x_3081_, v___x_3082_);
v___x_3084_ = lean_float_decLt(v___y_3080_, v___x_3083_);
v___y_3048_ = v___x_3084_;
goto v___jp_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3095_, lean_object* v_collapsed_3096_, lean_object* v_tag_3097_, lean_object* v_opts_3098_, lean_object* v_clsEnabled_3099_, lean_object* v_oldTraces_3100_, lean_object* v_msg_3101_, lean_object* v_resStartStop_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
uint8_t v_collapsed_boxed_3106_; uint8_t v_clsEnabled_boxed_3107_; lean_object* v_res_3108_; 
v_collapsed_boxed_3106_ = lean_unbox(v_collapsed_3096_);
v_clsEnabled_boxed_3107_ = lean_unbox(v_clsEnabled_3099_);
v_res_3108_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3095_, v_collapsed_boxed_3106_, v_tag_3097_, v_opts_3098_, v_clsEnabled_boxed_3107_, v_oldTraces_3100_, v_msg_3101_, v_resStartStop_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v_opts_3098_);
return v_res_3108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3111_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3112_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_3114_, 11, v___x_3111_);
return v___x_3114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3116_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
lean_ctor_set(v___x_3116_, 2, v___x_3115_);
lean_ctor_set(v___x_3116_, 3, v___x_3115_);
lean_ctor_set(v___x_3116_, 4, v___x_3115_);
lean_ctor_set(v___x_3116_, 5, v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
lean_ctor_set(v___x_3118_, 2, v___x_3117_);
lean_ctor_set(v___x_3118_, 3, v___x_3117_);
lean_ctor_set(v___x_3118_, 4, v___x_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3124_ = l_Lean_Name_append(v___x_3123_, v___x_3122_);
return v___x_3124_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3125_; double v___x_3126_; 
v___x_3125_ = lean_unsigned_to_nat(1000000000u);
v___x_3126_ = lean_float_of_nat(v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3127_, lean_object* v___f_3128_, lean_object* v_name_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_toCold_3133_; lean_object* v_options_3134_; uint8_t v_hasTrace_3135_; 
v_toCold_3133_ = lean_ctor_get(v___y_3130_, 0);
v_options_3134_ = lean_ctor_get(v_toCold_3133_, 2);
v_hasTrace_3135_ = lean_ctor_get_uint8(v_options_3134_, sizeof(void*)*1);
if (v_hasTrace_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v_env_3137_; lean_object* v___x_3138_; 
lean_dec_ref(v___f_3128_);
v___x_3136_ = lean_st_ref_get(v___y_3131_);
v_env_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc_ref(v_env_3137_);
lean_dec(v___x_3136_);
lean_inc(v_name_3129_);
v___x_3138_ = l_Lean_Meta_declFromEqLikeName(v_env_3137_, v_name_3129_);
if (lean_obj_tag(v___x_3138_) == 1)
{
lean_object* v_val_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3244_; 
v_val_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3244_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_val_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3244_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v_fst_3143_; lean_object* v_snd_3144_; lean_object* v___x_3145_; lean_object* v_env_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_fst_3143_ = lean_ctor_get(v_val_3139_, 0);
lean_inc_n(v_fst_3143_, 2);
v_snd_3144_ = lean_ctor_get(v_val_3139_, 1);
lean_inc_n(v_snd_3144_, 2);
lean_dec(v_val_3139_);
v___x_3145_ = lean_st_ref_get(v___y_3131_);
v_env_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc_ref(v_env_3146_);
lean_dec(v___x_3145_);
v___x_3147_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3146_, v_fst_3143_, v_snd_3144_);
v___x_3148_ = lean_name_eq(v_name_3129_, v___x_3147_);
lean_dec(v___x_3147_);
lean_dec(v_name_3129_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
lean_dec(v_snd_3144_);
lean_dec(v_fst_3143_);
lean_dec(v___x_3127_);
v___x_3149_ = lean_box(v_hasTrace_3135_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set_tag(v___x_3141_, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3149_);
v___x_3151_ = v___x_3141_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
else
{
uint8_t v___x_3153_; lean_object* v_a_3155_; 
lean_inc(v_snd_3144_);
v___x_3153_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3144_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3169_; uint8_t v___x_3170_; lean_object* v_a_3172_; 
lean_del_object(v___x_3141_);
v___x_3169_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3170_ = lean_string_dec_eq(v_snd_3144_, v___x_3169_);
lean_dec(v_snd_3144_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_dec(v_fst_3143_);
lean_dec(v___x_3127_);
v___x_3184_ = lean_box(v_hasTrace_3135_);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
return v___x_3185_;
}
else
{
uint8_t v___x_3186_; uint8_t v___x_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; uint64_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3186_ = 1;
v___x_3187_ = 0;
v___x_3188_ = 2;
v___x_3189_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3189_, 0, v___x_3153_);
lean_ctor_set_uint8(v___x_3189_, 1, v___x_3153_);
lean_ctor_set_uint8(v___x_3189_, 2, v___x_3153_);
lean_ctor_set_uint8(v___x_3189_, 3, v___x_3153_);
lean_ctor_set_uint8(v___x_3189_, 4, v___x_3153_);
lean_ctor_set_uint8(v___x_3189_, 5, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 6, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 7, v___x_3153_);
lean_ctor_set_uint8(v___x_3189_, 8, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 9, v___x_3186_);
lean_ctor_set_uint8(v___x_3189_, 10, v___x_3187_);
lean_ctor_set_uint8(v___x_3189_, 11, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 12, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 13, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 14, v___x_3188_);
lean_ctor_set_uint8(v___x_3189_, 15, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 16, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 17, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 18, v___x_3170_);
lean_ctor_set_uint8(v___x_3189_, 19, v___x_3153_);
v___x_3190_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3189_);
v___x_3191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
lean_ctor_set_uint64(v___x_3191_, sizeof(void*)*1, v___x_3190_);
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3194_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3195_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3196_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3197_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3197_, 0, v___x_3191_);
lean_ctor_set(v___x_3197_, 1, v___x_3127_);
lean_ctor_set(v___x_3197_, 2, v___x_3194_);
lean_ctor_set(v___x_3197_, 3, v___x_3195_);
lean_ctor_set(v___x_3197_, 4, v___x_3196_);
lean_ctor_set(v___x_3197_, 5, v___x_3192_);
lean_ctor_set(v___x_3197_, 6, v___x_3196_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*7, v___x_3153_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*7 + 1, v___x_3153_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*7 + 2, v___x_3153_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*7 + 3, v___x_3148_);
v___x_3198_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3199_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3200_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3198_);
lean_ctor_set(v___x_3201_, 1, v___x_3199_);
lean_ctor_set(v___x_3201_, 2, v___x_3127_);
lean_ctor_set(v___x_3201_, 3, v___x_3193_);
lean_ctor_set(v___x_3201_, 4, v___x_3200_);
v___x_3202_ = lean_st_mk_ref(v___x_3201_);
v___x_3203_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3143_, v___x_3148_, v___x_3197_, v___x_3202_, v___y_3130_, v___y_3131_);
lean_dec_ref_known(v___x_3197_, 7);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = lean_st_ref_get(v___x_3202_);
lean_dec(v___x_3202_);
lean_dec(v___x_3205_);
v_a_3172_ = v_a_3204_;
goto v___jp_3171_;
}
else
{
lean_dec(v___x_3202_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3206_; 
v_a_3206_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3203_, 1);
v_a_3172_ = v_a_3206_;
goto v___jp_3171_;
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_a_3207_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3203_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3203_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
v___jp_3171_:
{
if (lean_obj_tag(v_a_3172_) == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_box(v___x_3153_);
v___x_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
return v___x_3174_;
}
else
{
lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3182_; 
v_isSharedCheck_3182_ = !lean_is_exclusive(v_a_3172_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v_a_3172_, 0);
lean_dec(v_unused_3183_);
v___x_3176_ = v_a_3172_;
v_isShared_3177_ = v_isSharedCheck_3182_;
goto v_resetjp_3175_;
}
else
{
lean_dec(v_a_3172_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3182_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3178_ = lean_box(v___x_3170_);
if (v_isShared_3177_ == 0)
{
lean_ctor_set_tag(v___x_3176_, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3178_);
v___x_3180_ = v___x_3176_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
else
{
uint8_t v___x_3215_; uint8_t v___x_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; uint64_t v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v_snd_3144_);
v___x_3215_ = 1;
v___x_3216_ = 0;
v___x_3217_ = 2;
v___x_3218_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3218_, 0, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3218_, 1, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3218_, 2, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3218_, 3, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3218_, 4, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3218_, 5, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 6, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 7, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3218_, 8, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 9, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, 10, v___x_3216_);
lean_ctor_set_uint8(v___x_3218_, 11, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 12, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 13, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 14, v___x_3217_);
lean_ctor_set_uint8(v___x_3218_, 15, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 16, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 17, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 18, v___x_3153_);
lean_ctor_set_uint8(v___x_3218_, 19, v_hasTrace_3135_);
v___x_3219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3218_);
v___x_3220_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set_uint64(v___x_3220_, sizeof(void*)*1, v___x_3219_);
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3223_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3224_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3225_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3226_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3226_, 0, v___x_3220_);
lean_ctor_set(v___x_3226_, 1, v___x_3127_);
lean_ctor_set(v___x_3226_, 2, v___x_3223_);
lean_ctor_set(v___x_3226_, 3, v___x_3224_);
lean_ctor_set(v___x_3226_, 4, v___x_3225_);
lean_ctor_set(v___x_3226_, 5, v___x_3221_);
lean_ctor_set(v___x_3226_, 6, v___x_3225_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7 + 1, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7 + 2, v_hasTrace_3135_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7 + 3, v___x_3148_);
v___x_3227_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3228_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3229_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3227_);
lean_ctor_set(v___x_3230_, 1, v___x_3228_);
lean_ctor_set(v___x_3230_, 2, v___x_3127_);
lean_ctor_set(v___x_3230_, 3, v___x_3222_);
lean_ctor_set(v___x_3230_, 4, v___x_3229_);
v___x_3231_ = lean_st_mk_ref(v___x_3230_);
v___x_3232_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3143_, v___x_3226_, v___x_3231_, v___y_3130_, v___y_3131_);
lean_dec_ref_known(v___x_3226_, 7);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = lean_st_ref_get(v___x_3231_);
lean_dec(v___x_3231_);
lean_dec(v___x_3234_);
v_a_3155_ = v_a_3233_;
goto v___jp_3154_;
}
else
{
lean_dec(v___x_3231_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3235_; 
v_a_3235_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3232_, 1);
v_a_3155_ = v_a_3235_;
goto v___jp_3154_;
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_del_object(v___x_3141_);
v_a_3236_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3232_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3232_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
v___jp_3154_:
{
if (lean_obj_tag(v_a_3155_) == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = lean_box(v_hasTrace_3135_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set_tag(v___x_3141_, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3156_);
v___x_3158_ = v___x_3141_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
else
{
lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3167_; 
lean_del_object(v___x_3141_);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_a_3155_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v_a_3155_, 0);
lean_dec(v_unused_3168_);
v___x_3161_ = v_a_3155_;
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
else
{
lean_dec(v_a_3155_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3163_ = lean_box(v___x_3153_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3163_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_dec(v___x_3138_);
lean_dec(v_name_3129_);
lean_dec(v___x_3127_);
v___x_3245_ = lean_box(v_hasTrace_3135_);
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
return v___x_3246_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3247_; lean_object* v___f_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v_a_3256_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v_a_3271_; lean_object* v___y_3275_; uint8_t v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3278_; lean_object* v_a_3279_; uint8_t v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; uint8_t v___y_3284_; lean_object* v_a_3285_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v_a_3289_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v_a_3294_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v_a_3306_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v_a_3311_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3322_; uint8_t v___y_3323_; lean_object* v___y_3324_; lean_object* v_a_3325_; lean_object* v___y_3328_; uint8_t v___y_3329_; lean_object* v___y_3330_; uint8_t v___y_3331_; lean_object* v_a_3332_; 
v_inheritedTraceOptions_3247_ = lean_ctor_get(v_toCold_3133_, 11);
lean_inc(v_name_3129_);
v___f_3248_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3248_, 0, v_name_3129_);
v___x_3249_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3250_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3251_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3252_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3247_, v_options_3134_, v___x_3251_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3461_ = l_Lean_trace_profiler;
v___x_3462_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3134_, v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v_env_3464_; lean_object* v___x_3465_; 
lean_dec_ref(v___f_3248_);
lean_dec_ref(v___f_3128_);
v___x_3463_ = lean_st_ref_get(v___y_3131_);
v_env_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc_ref(v_env_3464_);
lean_dec(v___x_3463_);
lean_inc(v_name_3129_);
v___x_3465_ = l_Lean_Meta_declFromEqLikeName(v_env_3464_, v_name_3129_);
if (lean_obj_tag(v___x_3465_) == 1)
{
lean_object* v_val_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3571_; 
v_val_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3571_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_val_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3571_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v_fst_3470_; lean_object* v_snd_3471_; lean_object* v___x_3472_; lean_object* v_env_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v_fst_3470_ = lean_ctor_get(v_val_3466_, 0);
lean_inc_n(v_fst_3470_, 2);
v_snd_3471_ = lean_ctor_get(v_val_3466_, 1);
lean_inc_n(v_snd_3471_, 2);
lean_dec(v_val_3466_);
v___x_3472_ = lean_st_ref_get(v___y_3131_);
v_env_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc_ref(v_env_3473_);
lean_dec(v___x_3472_);
v___x_3474_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3473_, v_fst_3470_, v_snd_3471_);
v___x_3475_ = lean_name_eq(v_name_3129_, v___x_3474_);
lean_dec(v___x_3474_);
lean_dec(v_name_3129_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
lean_dec(v_snd_3471_);
lean_dec(v_fst_3470_);
lean_dec(v___x_3127_);
v___x_3476_ = lean_box(v___x_3462_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set_tag(v___x_3468_, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3476_);
v___x_3478_ = v___x_3468_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
else
{
uint8_t v___x_3480_; lean_object* v_a_3482_; 
lean_inc(v_snd_3471_);
v___x_3480_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3471_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v_a_3499_; 
lean_del_object(v___x_3468_);
v___x_3496_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3497_ = lean_string_dec_eq(v_snd_3471_, v___x_3496_);
lean_dec(v_snd_3471_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec(v_fst_3470_);
lean_dec(v___x_3127_);
v___x_3511_ = lean_box(v___x_3462_);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
else
{
uint8_t v___x_3513_; uint8_t v___x_3514_; uint8_t v___x_3515_; lean_object* v___x_3516_; uint64_t v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3513_ = 1;
v___x_3514_ = 0;
v___x_3515_ = 2;
v___x_3516_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3516_, 0, v___x_3480_);
lean_ctor_set_uint8(v___x_3516_, 1, v___x_3480_);
lean_ctor_set_uint8(v___x_3516_, 2, v___x_3480_);
lean_ctor_set_uint8(v___x_3516_, 3, v___x_3480_);
lean_ctor_set_uint8(v___x_3516_, 4, v___x_3480_);
lean_ctor_set_uint8(v___x_3516_, 5, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 6, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 7, v___x_3480_);
lean_ctor_set_uint8(v___x_3516_, 8, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 9, v___x_3513_);
lean_ctor_set_uint8(v___x_3516_, 10, v___x_3514_);
lean_ctor_set_uint8(v___x_3516_, 11, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 12, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 13, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 14, v___x_3515_);
lean_ctor_set_uint8(v___x_3516_, 15, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 16, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 17, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 18, v___x_3497_);
lean_ctor_set_uint8(v___x_3516_, 19, v___x_3480_);
v___x_3517_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3516_);
v___x_3518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set_uint64(v___x_3518_, sizeof(void*)*1, v___x_3517_);
v___x_3519_ = lean_unsigned_to_nat(0u);
v___x_3520_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3522_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3523_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3524_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3524_, 0, v___x_3518_);
lean_ctor_set(v___x_3524_, 1, v___x_3127_);
lean_ctor_set(v___x_3524_, 2, v___x_3521_);
lean_ctor_set(v___x_3524_, 3, v___x_3522_);
lean_ctor_set(v___x_3524_, 4, v___x_3523_);
lean_ctor_set(v___x_3524_, 5, v___x_3519_);
lean_ctor_set(v___x_3524_, 6, v___x_3523_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7, v___x_3480_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7 + 1, v___x_3480_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7 + 2, v___x_3480_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7 + 3, v_hasTrace_3135_);
v___x_3525_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3526_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3527_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3525_);
lean_ctor_set(v___x_3528_, 1, v___x_3526_);
lean_ctor_set(v___x_3528_, 2, v___x_3127_);
lean_ctor_set(v___x_3528_, 3, v___x_3520_);
lean_ctor_set(v___x_3528_, 4, v___x_3527_);
v___x_3529_ = lean_st_mk_ref(v___x_3528_);
v___x_3530_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3470_, v_hasTrace_3135_, v___x_3524_, v___x_3529_, v___y_3130_, v___y_3131_);
lean_dec_ref_known(v___x_3524_, 7);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = lean_st_ref_get(v___x_3529_);
lean_dec(v___x_3529_);
lean_dec(v___x_3532_);
v_a_3499_ = v_a_3531_;
goto v___jp_3498_;
}
else
{
lean_dec(v___x_3529_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3533_; 
v_a_3533_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3530_, 1);
v_a_3499_ = v_a_3533_;
goto v___jp_3498_;
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
v_a_3534_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3530_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3530_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
v___jp_3498_:
{
if (lean_obj_tag(v_a_3499_) == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_box(v___x_3480_);
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
return v___x_3501_;
}
else
{
lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3509_; 
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3499_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; 
v_unused_3510_ = lean_ctor_get(v_a_3499_, 0);
lean_dec(v_unused_3510_);
v___x_3503_ = v_a_3499_;
v_isShared_3504_ = v_isSharedCheck_3509_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v_a_3499_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3509_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = lean_box(v___x_3497_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set_tag(v___x_3503_, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3505_);
v___x_3507_ = v___x_3503_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
else
{
uint8_t v___x_3542_; uint8_t v___x_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; uint64_t v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
lean_dec(v_snd_3471_);
v___x_3542_ = 1;
v___x_3543_ = 0;
v___x_3544_ = 2;
v___x_3545_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3545_, 0, v___x_3462_);
lean_ctor_set_uint8(v___x_3545_, 1, v___x_3462_);
lean_ctor_set_uint8(v___x_3545_, 2, v___x_3462_);
lean_ctor_set_uint8(v___x_3545_, 3, v___x_3462_);
lean_ctor_set_uint8(v___x_3545_, 4, v___x_3462_);
lean_ctor_set_uint8(v___x_3545_, 5, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 6, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 7, v___x_3462_);
lean_ctor_set_uint8(v___x_3545_, 8, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 9, v___x_3542_);
lean_ctor_set_uint8(v___x_3545_, 10, v___x_3543_);
lean_ctor_set_uint8(v___x_3545_, 11, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 12, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 13, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 14, v___x_3544_);
lean_ctor_set_uint8(v___x_3545_, 15, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 16, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 17, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 18, v___x_3480_);
lean_ctor_set_uint8(v___x_3545_, 19, v___x_3462_);
v___x_3546_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3545_);
v___x_3547_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set_uint64(v___x_3547_, sizeof(void*)*1, v___x_3546_);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3550_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3551_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3552_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3553_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3553_, 0, v___x_3547_);
lean_ctor_set(v___x_3553_, 1, v___x_3127_);
lean_ctor_set(v___x_3553_, 2, v___x_3550_);
lean_ctor_set(v___x_3553_, 3, v___x_3551_);
lean_ctor_set(v___x_3553_, 4, v___x_3552_);
lean_ctor_set(v___x_3553_, 5, v___x_3548_);
lean_ctor_set(v___x_3553_, 6, v___x_3552_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*7, v___x_3462_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*7 + 1, v___x_3462_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*7 + 2, v___x_3462_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*7 + 3, v_hasTrace_3135_);
v___x_3554_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3555_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3556_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3554_);
lean_ctor_set(v___x_3557_, 1, v___x_3555_);
lean_ctor_set(v___x_3557_, 2, v___x_3127_);
lean_ctor_set(v___x_3557_, 3, v___x_3549_);
lean_ctor_set(v___x_3557_, 4, v___x_3556_);
v___x_3558_ = lean_st_mk_ref(v___x_3557_);
v___x_3559_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3470_, v___x_3553_, v___x_3558_, v___y_3130_, v___y_3131_);
lean_dec_ref_known(v___x_3553_, 7);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = lean_st_ref_get(v___x_3558_);
lean_dec(v___x_3558_);
lean_dec(v___x_3561_);
v_a_3482_ = v_a_3560_;
goto v___jp_3481_;
}
else
{
lean_dec(v___x_3558_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3562_; 
v_a_3562_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3559_, 1);
v_a_3482_ = v_a_3562_;
goto v___jp_3481_;
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3468_);
v_a_3563_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3559_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3559_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
v___jp_3481_:
{
if (lean_obj_tag(v_a_3482_) == 0)
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = lean_box(v___x_3462_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set_tag(v___x_3468_, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3483_);
v___x_3485_ = v___x_3468_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
else
{
lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3494_; 
lean_del_object(v___x_3468_);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_a_3482_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v_a_3482_, 0);
lean_dec(v_unused_3495_);
v___x_3488_ = v_a_3482_;
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
else
{
lean_dec(v_a_3482_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3490_ = lean_box(v___x_3480_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set_tag(v___x_3488_, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3490_);
v___x_3492_ = v___x_3488_;
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
}
}
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v___x_3465_);
lean_dec(v_name_3129_);
lean_dec(v___x_3127_);
v___x_3572_ = lean_box(v___x_3462_);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
else
{
goto v___jp_3333_;
}
}
else
{
goto v___jp_3333_;
}
v___jp_3253_:
{
lean_object* v___x_3257_; double v___x_3258_; double v___x_3259_; double v___x_3260_; double v___x_3261_; double v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3257_ = lean_io_mono_nanos_now();
v___x_3258_ = lean_float_of_nat(v___y_3255_);
v___x_3259_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3260_ = lean_float_div(v___x_3258_, v___x_3259_);
v___x_3261_ = lean_float_of_nat(v___x_3257_);
v___x_3262_ = lean_float_div(v___x_3261_, v___x_3259_);
v___x_3263_ = lean_box_float(v___x_3260_);
v___x_3264_ = lean_box_float(v___x_3262_);
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v_a_3256_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3249_, v_hasTrace_3135_, v___x_3250_, v_options_3134_, v___x_3252_, v___y_3254_, v___f_3248_, v___x_3266_, v___y_3130_, v___y_3131_);
return v___x_3267_;
}
v___jp_3268_:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_box(v_a_3271_);
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
v___y_3254_ = v___y_3269_;
v___y_3255_ = v___y_3270_;
v_a_3256_ = v___x_3273_;
goto v___jp_3253_;
}
v___jp_3274_:
{
if (lean_obj_tag(v_a_3279_) == 0)
{
v___y_3269_ = v___y_3275_;
v___y_3270_ = v___y_3277_;
v_a_3271_ = v___y_3278_;
goto v___jp_3268_;
}
else
{
lean_dec_ref_known(v_a_3279_, 1);
v___y_3269_ = v___y_3275_;
v___y_3270_ = v___y_3277_;
v_a_3271_ = v___y_3276_;
goto v___jp_3268_;
}
}
v___jp_3280_:
{
if (lean_obj_tag(v_a_3285_) == 0)
{
v___y_3269_ = v___y_3282_;
v___y_3270_ = v___y_3283_;
v_a_3271_ = v___y_3281_;
goto v___jp_3268_;
}
else
{
lean_dec_ref_known(v_a_3285_, 1);
v___y_3269_ = v___y_3282_;
v___y_3270_ = v___y_3283_;
v_a_3271_ = v___y_3284_;
goto v___jp_3268_;
}
}
v___jp_3286_:
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_a_3289_);
v___y_3254_ = v___y_3287_;
v___y_3255_ = v___y_3288_;
v_a_3256_ = v___x_3290_;
goto v___jp_3253_;
}
v___jp_3291_:
{
lean_object* v___x_3295_; double v___x_3296_; double v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3295_ = lean_io_get_num_heartbeats();
v___x_3296_ = lean_float_of_nat(v___y_3292_);
v___x_3297_ = lean_float_of_nat(v___x_3295_);
v___x_3298_ = lean_box_float(v___x_3296_);
v___x_3299_ = lean_box_float(v___x_3297_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v_a_3294_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3249_, v_hasTrace_3135_, v___x_3250_, v_options_3134_, v___x_3252_, v___y_3293_, v___f_3248_, v___x_3301_, v___y_3130_, v___y_3131_);
return v___x_3302_;
}
v___jp_3303_:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v_a_3306_);
v___y_3292_ = v___y_3304_;
v___y_3293_ = v___y_3305_;
v_a_3294_ = v___x_3307_;
goto v___jp_3291_;
}
v___jp_3308_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_box(v_a_3311_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
v___y_3292_ = v___y_3309_;
v___y_3293_ = v___y_3310_;
v_a_3294_ = v___x_3313_;
goto v___jp_3291_;
}
v___jp_3314_:
{
if (lean_obj_tag(v___y_3317_) == 0)
{
lean_object* v_a_3318_; uint8_t v___x_3319_; 
v_a_3318_ = lean_ctor_get(v___y_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___y_3317_, 1);
v___x_3319_ = lean_unbox(v_a_3318_);
lean_dec(v_a_3318_);
v___y_3309_ = v___y_3315_;
v___y_3310_ = v___y_3316_;
v_a_3311_ = v___x_3319_;
goto v___jp_3308_;
}
else
{
lean_object* v_a_3320_; 
v_a_3320_ = lean_ctor_get(v___y_3317_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___y_3317_, 1);
v___y_3304_ = v___y_3315_;
v___y_3305_ = v___y_3316_;
v_a_3306_ = v_a_3320_;
goto v___jp_3303_;
}
}
v___jp_3321_:
{
if (lean_obj_tag(v_a_3325_) == 0)
{
uint8_t v___x_3326_; 
v___x_3326_ = 0;
v___y_3309_ = v___y_3322_;
v___y_3310_ = v___y_3324_;
v_a_3311_ = v___x_3326_;
goto v___jp_3308_;
}
else
{
lean_dec_ref_known(v_a_3325_, 1);
v___y_3309_ = v___y_3322_;
v___y_3310_ = v___y_3324_;
v_a_3311_ = v___y_3323_;
goto v___jp_3308_;
}
}
v___jp_3327_:
{
if (lean_obj_tag(v_a_3332_) == 0)
{
v___y_3309_ = v___y_3328_;
v___y_3310_ = v___y_3330_;
v_a_3311_ = v___y_3331_;
goto v___jp_3308_;
}
else
{
lean_dec_ref_known(v_a_3332_, 1);
v___y_3309_ = v___y_3328_;
v___y_3310_ = v___y_3330_;
v_a_3311_ = v___y_3329_;
goto v___jp_3308_;
}
}
v___jp_3333_:
{
lean_object* v___x_3334_; lean_object* v_a_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3334_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3131_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3337_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3134_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v_env_3340_; lean_object* v___x_3341_; 
lean_dec_ref(v___f_3128_);
v___x_3338_ = lean_io_mono_nanos_now();
v___x_3339_ = lean_st_ref_get(v___y_3131_);
v_env_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc_ref(v_env_3340_);
lean_dec(v___x_3339_);
lean_inc(v_name_3129_);
v___x_3341_ = l_Lean_Meta_declFromEqLikeName(v_env_3340_, v_name_3129_);
if (lean_obj_tag(v___x_3341_) == 1)
{
lean_object* v_val_3342_; lean_object* v_fst_3343_; lean_object* v_snd_3344_; lean_object* v___x_3345_; lean_object* v_env_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v_val_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v_fst_3343_ = lean_ctor_get(v_val_3342_, 0);
lean_inc_n(v_fst_3343_, 2);
v_snd_3344_ = lean_ctor_get(v_val_3342_, 1);
lean_inc_n(v_snd_3344_, 2);
lean_dec(v_val_3342_);
v___x_3345_ = lean_st_ref_get(v___y_3131_);
v_env_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc_ref(v_env_3346_);
lean_dec(v___x_3345_);
v___x_3347_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3346_, v_fst_3343_, v_snd_3344_);
v___x_3348_ = lean_name_eq(v_name_3129_, v___x_3347_);
lean_dec(v___x_3347_);
lean_dec(v_name_3129_);
if (v___x_3348_ == 0)
{
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v___x_3127_);
v___y_3269_ = v_a_3335_;
v___y_3270_ = v___x_3338_;
v_a_3271_ = v___x_3337_;
goto v___jp_3268_;
}
else
{
uint8_t v___x_3349_; 
lean_inc(v_snd_3344_);
v___x_3349_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3344_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3350_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3351_ = lean_string_dec_eq(v_snd_3344_, v___x_3350_);
lean_dec(v_snd_3344_);
if (v___x_3351_ == 0)
{
lean_dec(v_fst_3343_);
lean_dec(v___x_3127_);
v___y_3269_ = v_a_3335_;
v___y_3270_ = v___x_3338_;
v_a_3271_ = v___x_3337_;
goto v___jp_3268_;
}
else
{
uint8_t v___x_3352_; uint8_t v___x_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; uint64_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3352_ = 1;
v___x_3353_ = 0;
v___x_3354_ = 2;
v___x_3355_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3355_, 0, v___x_3349_);
lean_ctor_set_uint8(v___x_3355_, 1, v___x_3349_);
lean_ctor_set_uint8(v___x_3355_, 2, v___x_3349_);
lean_ctor_set_uint8(v___x_3355_, 3, v___x_3349_);
lean_ctor_set_uint8(v___x_3355_, 4, v___x_3349_);
lean_ctor_set_uint8(v___x_3355_, 5, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 6, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 7, v___x_3349_);
lean_ctor_set_uint8(v___x_3355_, 8, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 9, v___x_3352_);
lean_ctor_set_uint8(v___x_3355_, 10, v___x_3353_);
lean_ctor_set_uint8(v___x_3355_, 11, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 12, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 13, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 14, v___x_3354_);
lean_ctor_set_uint8(v___x_3355_, 15, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 16, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 17, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 18, v___x_3351_);
lean_ctor_set_uint8(v___x_3355_, 19, v___x_3349_);
v___x_3356_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3355_);
v___x_3357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set_uint64(v___x_3357_, sizeof(void*)*1, v___x_3356_);
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3360_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3362_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3363_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3363_, 0, v___x_3357_);
lean_ctor_set(v___x_3363_, 1, v___x_3127_);
lean_ctor_set(v___x_3363_, 2, v___x_3360_);
lean_ctor_set(v___x_3363_, 3, v___x_3361_);
lean_ctor_set(v___x_3363_, 4, v___x_3362_);
lean_ctor_set(v___x_3363_, 5, v___x_3358_);
lean_ctor_set(v___x_3363_, 6, v___x_3362_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7, v___x_3349_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 1, v___x_3349_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 2, v___x_3349_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 3, v_hasTrace_3135_);
v___x_3364_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3365_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3364_);
lean_ctor_set(v___x_3367_, 1, v___x_3365_);
lean_ctor_set(v___x_3367_, 2, v___x_3127_);
lean_ctor_set(v___x_3367_, 3, v___x_3359_);
lean_ctor_set(v___x_3367_, 4, v___x_3366_);
v___x_3368_ = lean_st_mk_ref(v___x_3367_);
v___x_3369_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3343_, v_hasTrace_3135_, v___x_3363_, v___x_3368_, v___y_3130_, v___y_3131_);
lean_dec_ref_known(v___x_3363_, 7);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3371_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v___x_3369_, 1);
v___x_3371_ = lean_st_ref_get(v___x_3368_);
lean_dec(v___x_3368_);
lean_dec(v___x_3371_);
v___y_3275_ = v_a_3335_;
v___y_3276_ = v___x_3351_;
v___y_3277_ = v___x_3338_;
v___y_3278_ = v___x_3349_;
v_a_3279_ = v_a_3370_;
goto v___jp_3274_;
}
else
{
lean_dec(v___x_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3369_, 1);
v___y_3275_ = v_a_3335_;
v___y_3276_ = v___x_3351_;
v___y_3277_ = v___x_3338_;
v___y_3278_ = v___x_3349_;
v_a_3279_ = v_a_3372_;
goto v___jp_3274_;
}
else
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3369_, 1);
v___y_3287_ = v_a_3335_;
v___y_3288_ = v___x_3338_;
v_a_3289_ = v_a_3373_;
goto v___jp_3286_;
}
}
}
}
else
{
uint8_t v___x_3374_; uint8_t v___x_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; uint64_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec(v_snd_3344_);
v___x_3374_ = 1;
v___x_3375_ = 0;
v___x_3376_ = 2;
v___x_3377_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3377_, 0, v___x_3337_);
lean_ctor_set_uint8(v___x_3377_, 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3377_, 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3377_, 3, v___x_3337_);
lean_ctor_set_uint8(v___x_3377_, 4, v___x_3337_);
lean_ctor_set_uint8(v___x_3377_, 5, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 6, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 7, v___x_3337_);
lean_ctor_set_uint8(v___x_3377_, 8, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 9, v___x_3374_);
lean_ctor_set_uint8(v___x_3377_, 10, v___x_3375_);
lean_ctor_set_uint8(v___x_3377_, 11, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 12, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 13, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 14, v___x_3376_);
lean_ctor_set_uint8(v___x_3377_, 15, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 16, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 17, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 18, v___x_3349_);
lean_ctor_set_uint8(v___x_3377_, 19, v___x_3337_);
v___x_3378_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3377_);
v___x_3379_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set_uint64(v___x_3379_, sizeof(void*)*1, v___x_3378_);
v___x_3380_ = lean_unsigned_to_nat(0u);
v___x_3381_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3382_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3384_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3385_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3385_, 0, v___x_3379_);
lean_ctor_set(v___x_3385_, 1, v___x_3127_);
lean_ctor_set(v___x_3385_, 2, v___x_3382_);
lean_ctor_set(v___x_3385_, 3, v___x_3383_);
lean_ctor_set(v___x_3385_, 4, v___x_3384_);
lean_ctor_set(v___x_3385_, 5, v___x_3380_);
lean_ctor_set(v___x_3385_, 6, v___x_3384_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7, v___x_3337_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7 + 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7 + 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7 + 3, v_hasTrace_3135_);
v___x_3386_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3388_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3386_);
lean_ctor_set(v___x_3389_, 1, v___x_3387_);
lean_ctor_set(v___x_3389_, 2, v___x_3127_);
lean_ctor_set(v___x_3389_, 3, v___x_3381_);
lean_ctor_set(v___x_3389_, 4, v___x_3388_);
v___x_3390_ = lean_st_mk_ref(v___x_3389_);
v___x_3391_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3343_, v___x_3385_, v___x_3390_, v___y_3130_, v___y_3131_);
lean_dec_ref_known(v___x_3385_, 7);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = lean_st_ref_get(v___x_3390_);
lean_dec(v___x_3390_);
lean_dec(v___x_3393_);
v___y_3281_ = v___x_3337_;
v___y_3282_ = v_a_3335_;
v___y_3283_ = v___x_3338_;
v___y_3284_ = v___x_3349_;
v_a_3285_ = v_a_3392_;
goto v___jp_3280_;
}
else
{
lean_dec(v___x_3390_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3391_, 1);
v___y_3281_ = v___x_3337_;
v___y_3282_ = v_a_3335_;
v___y_3283_ = v___x_3338_;
v___y_3284_ = v___x_3349_;
v_a_3285_ = v_a_3394_;
goto v___jp_3280_;
}
else
{
lean_object* v_a_3395_; 
v_a_3395_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3391_, 1);
v___y_3287_ = v_a_3335_;
v___y_3288_ = v___x_3338_;
v_a_3289_ = v_a_3395_;
goto v___jp_3286_;
}
}
}
}
}
else
{
lean_dec(v___x_3341_);
lean_dec(v_name_3129_);
lean_dec(v___x_3127_);
v___y_3269_ = v_a_3335_;
v___y_3270_ = v___x_3338_;
v_a_3271_ = v___x_3337_;
goto v___jp_3268_;
}
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_env_3398_; lean_object* v___x_3399_; 
v___x_3396_ = lean_io_get_num_heartbeats();
v___x_3397_ = lean_st_ref_get(v___y_3131_);
v_env_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc_ref(v_env_3398_);
lean_dec(v___x_3397_);
lean_inc(v_name_3129_);
v___x_3399_ = l_Lean_Meta_declFromEqLikeName(v_env_3398_, v_name_3129_);
if (lean_obj_tag(v___x_3399_) == 1)
{
lean_object* v_val_3400_; lean_object* v_fst_3401_; lean_object* v_snd_3402_; lean_object* v___x_3403_; lean_object* v_env_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v_val_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_val_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v_fst_3401_ = lean_ctor_get(v_val_3400_, 0);
lean_inc_n(v_fst_3401_, 2);
v_snd_3402_ = lean_ctor_get(v_val_3400_, 1);
lean_inc_n(v_snd_3402_, 2);
lean_dec(v_val_3400_);
v___x_3403_ = lean_st_ref_get(v___y_3131_);
v_env_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc_ref(v_env_3404_);
lean_dec(v___x_3403_);
v___x_3405_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3404_, v_fst_3401_, v_snd_3402_);
v___x_3406_ = lean_name_eq(v_name_3129_, v___x_3405_);
lean_dec(v___x_3405_);
lean_dec(v_name_3129_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_dec(v_snd_3402_);
lean_dec(v_fst_3401_);
lean_dec(v___x_3127_);
v___x_3407_ = lean_box(0);
lean_inc(v___y_3131_);
lean_inc_ref(v___y_3130_);
v___x_3408_ = lean_apply_4(v___f_3128_, v___x_3407_, v___y_3130_, v___y_3131_, lean_box(0));
v___y_3315_ = v___x_3396_;
v___y_3316_ = v_a_3335_;
v___y_3317_ = v___x_3408_;
goto v___jp_3314_;
}
else
{
uint8_t v___x_3409_; 
lean_inc(v_snd_3402_);
v___x_3409_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3402_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3411_ = lean_string_dec_eq(v_snd_3402_, v___x_3410_);
lean_dec(v_snd_3402_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec(v_fst_3401_);
lean_dec(v___x_3127_);
v___x_3412_ = lean_box(0);
lean_inc(v___y_3131_);
lean_inc_ref(v___y_3130_);
v___x_3413_ = lean_apply_4(v___f_3128_, v___x_3412_, v___y_3130_, v___y_3131_, lean_box(0));
v___y_3315_ = v___x_3396_;
v___y_3316_ = v_a_3335_;
v___y_3317_ = v___x_3413_;
goto v___jp_3314_;
}
else
{
uint8_t v___x_3414_; uint8_t v___x_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; uint64_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec_ref(v___f_3128_);
v___x_3414_ = 1;
v___x_3415_ = 0;
v___x_3416_ = 2;
v___x_3417_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3417_, 0, v___x_3409_);
lean_ctor_set_uint8(v___x_3417_, 1, v___x_3409_);
lean_ctor_set_uint8(v___x_3417_, 2, v___x_3409_);
lean_ctor_set_uint8(v___x_3417_, 3, v___x_3409_);
lean_ctor_set_uint8(v___x_3417_, 4, v___x_3409_);
lean_ctor_set_uint8(v___x_3417_, 5, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 6, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 7, v___x_3409_);
lean_ctor_set_uint8(v___x_3417_, 8, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 9, v___x_3414_);
lean_ctor_set_uint8(v___x_3417_, 10, v___x_3415_);
lean_ctor_set_uint8(v___x_3417_, 11, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 12, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 13, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 14, v___x_3416_);
lean_ctor_set_uint8(v___x_3417_, 15, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 16, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 17, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 18, v___x_3411_);
lean_ctor_set_uint8(v___x_3417_, 19, v___x_3409_);
v___x_3418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3417_);
v___x_3419_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set_uint64(v___x_3419_, sizeof(void*)*1, v___x_3418_);
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3422_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3424_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3425_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3425_, 0, v___x_3419_);
lean_ctor_set(v___x_3425_, 1, v___x_3127_);
lean_ctor_set(v___x_3425_, 2, v___x_3422_);
lean_ctor_set(v___x_3425_, 3, v___x_3423_);
lean_ctor_set(v___x_3425_, 4, v___x_3424_);
lean_ctor_set(v___x_3425_, 5, v___x_3420_);
lean_ctor_set(v___x_3425_, 6, v___x_3424_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7, v___x_3409_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 1, v___x_3409_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 2, v___x_3409_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 3, v___x_3337_);
v___x_3426_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3426_);
lean_ctor_set(v___x_3429_, 1, v___x_3427_);
lean_ctor_set(v___x_3429_, 2, v___x_3127_);
lean_ctor_set(v___x_3429_, 3, v___x_3421_);
lean_ctor_set(v___x_3429_, 4, v___x_3428_);
v___x_3430_ = lean_st_mk_ref(v___x_3429_);
v___x_3431_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3401_, v___x_3337_, v___x_3425_, v___x_3430_, v___y_3130_, v___y_3131_);
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
v___y_3328_ = v___x_3396_;
v___y_3329_ = v___x_3411_;
v___y_3330_ = v_a_3335_;
v___y_3331_ = v___x_3409_;
v_a_3332_ = v_a_3432_;
goto v___jp_3327_;
}
else
{
lean_dec(v___x_3430_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3434_; 
v_a_3434_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3431_, 1);
v___y_3328_ = v___x_3396_;
v___y_3329_ = v___x_3411_;
v___y_3330_ = v_a_3335_;
v___y_3331_ = v___x_3409_;
v_a_3332_ = v_a_3434_;
goto v___jp_3327_;
}
else
{
lean_object* v_a_3435_; 
v_a_3435_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3431_, 1);
v___y_3304_ = v___x_3396_;
v___y_3305_ = v_a_3335_;
v_a_3306_ = v_a_3435_;
goto v___jp_3303_;
}
}
}
}
else
{
uint8_t v___x_3436_; uint8_t v___x_3437_; uint8_t v___x_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; uint64_t v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec(v_snd_3402_);
lean_dec_ref(v___f_3128_);
v___x_3436_ = 0;
v___x_3437_ = 1;
v___x_3438_ = 0;
v___x_3439_ = 2;
v___x_3440_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3440_, 0, v___x_3436_);
lean_ctor_set_uint8(v___x_3440_, 1, v___x_3436_);
lean_ctor_set_uint8(v___x_3440_, 2, v___x_3436_);
lean_ctor_set_uint8(v___x_3440_, 3, v___x_3436_);
lean_ctor_set_uint8(v___x_3440_, 4, v___x_3436_);
lean_ctor_set_uint8(v___x_3440_, 5, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 6, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 7, v___x_3436_);
lean_ctor_set_uint8(v___x_3440_, 8, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 9, v___x_3437_);
lean_ctor_set_uint8(v___x_3440_, 10, v___x_3438_);
lean_ctor_set_uint8(v___x_3440_, 11, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 12, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 13, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 14, v___x_3439_);
lean_ctor_set_uint8(v___x_3440_, 15, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 16, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 17, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 18, v___x_3409_);
lean_ctor_set_uint8(v___x_3440_, 19, v___x_3436_);
v___x_3441_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3440_);
v___x_3442_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set_uint64(v___x_3442_, sizeof(void*)*1, v___x_3441_);
v___x_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3447_ = lean_box(0);
lean_inc(v___x_3127_);
v___x_3448_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3448_, 0, v___x_3442_);
lean_ctor_set(v___x_3448_, 1, v___x_3127_);
lean_ctor_set(v___x_3448_, 2, v___x_3445_);
lean_ctor_set(v___x_3448_, 3, v___x_3446_);
lean_ctor_set(v___x_3448_, 4, v___x_3447_);
lean_ctor_set(v___x_3448_, 5, v___x_3443_);
lean_ctor_set(v___x_3448_, 6, v___x_3447_);
lean_ctor_set_uint8(v___x_3448_, sizeof(void*)*7, v___x_3436_);
lean_ctor_set_uint8(v___x_3448_, sizeof(void*)*7 + 1, v___x_3436_);
lean_ctor_set_uint8(v___x_3448_, sizeof(void*)*7 + 2, v___x_3436_);
lean_ctor_set_uint8(v___x_3448_, sizeof(void*)*7 + 3, v___x_3337_);
v___x_3449_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3450_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3449_);
lean_ctor_set(v___x_3452_, 1, v___x_3450_);
lean_ctor_set(v___x_3452_, 2, v___x_3127_);
lean_ctor_set(v___x_3452_, 3, v___x_3444_);
lean_ctor_set(v___x_3452_, 4, v___x_3451_);
v___x_3453_ = lean_st_mk_ref(v___x_3452_);
v___x_3454_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3401_, v___x_3448_, v___x_3453_, v___y_3130_, v___y_3131_);
lean_dec_ref_known(v___x_3448_, 7);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = lean_st_ref_get(v___x_3453_);
lean_dec(v___x_3453_);
lean_dec(v___x_3456_);
v___y_3322_ = v___x_3396_;
v___y_3323_ = v___x_3409_;
v___y_3324_ = v_a_3335_;
v_a_3325_ = v_a_3455_;
goto v___jp_3321_;
}
else
{
lean_dec(v___x_3453_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3457_; 
v_a_3457_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3454_, 1);
v___y_3322_ = v___x_3396_;
v___y_3323_ = v___x_3409_;
v___y_3324_ = v_a_3335_;
v_a_3325_ = v_a_3457_;
goto v___jp_3321_;
}
else
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3454_, 1);
v___y_3304_ = v___x_3396_;
v___y_3305_ = v_a_3335_;
v_a_3306_ = v_a_3458_;
goto v___jp_3303_;
}
}
}
}
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v___x_3399_);
lean_dec(v_name_3129_);
lean_dec(v___x_3127_);
v___x_3459_ = lean_box(0);
lean_inc(v___y_3131_);
lean_inc_ref(v___y_3130_);
v___x_3460_ = lean_apply_4(v___f_3128_, v___x_3459_, v___y_3130_, v___y_3131_, lean_box(0));
v___y_3315_ = v___x_3396_;
v___y_3316_ = v_a_3335_;
v___y_3317_ = v___x_3460_;
goto v___jp_3314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3574_, lean_object* v___f_3575_, lean_object* v_name_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3574_, v___f_3575_, v_name_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
return v_res_3580_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3625_ = lean_unsigned_to_nat(3137104340u);
v___x_3626_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3627_ = l_Lean_Name_num___override(v___x_3626_, v___x_3625_);
return v___x_3627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3630_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3631_ = l_Lean_Name_str___override(v___x_3630_, v___x_3629_);
return v___x_3631_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3634_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3635_ = l_Lean_Name_str___override(v___x_3634_, v___x_3633_);
return v___x_3635_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = lean_unsigned_to_nat(2u);
v___x_3637_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3638_ = l_Lean_Name_num___override(v___x_3637_, v___x_3636_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3640_; lean_object* v___x_3641_; 
v___f_3640_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3641_ = l_Lean_registerReservedNameAction(v___f_3640_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_dec_ref_known(v___x_3641_, 1);
v___x_3642_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3643_ = 0;
v___x_3644_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3645_ = l_Lean_registerTraceClass(v___x_3642_, v___x_3643_, v___x_3644_);
return v___x_3645_;
}
else
{
return v___x_3641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3648_, lean_object* v_x_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3649_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3654_, lean_object* v_x_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3654_, v_x_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3659_;
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
