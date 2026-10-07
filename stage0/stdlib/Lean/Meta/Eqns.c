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
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_292_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
lean_ctor_set(v___x_294_, 2, v___x_293_);
lean_ctor_set(v___x_294_, 3, v___x_293_);
lean_ctor_set(v___x_294_, 4, v___x_292_);
lean_ctor_set(v___x_294_, 5, v___x_292_);
lean_ctor_set(v___x_294_, 6, v___x_292_);
lean_ctor_set(v___x_294_, 7, v___x_292_);
lean_ctor_set(v___x_294_, 8, v___x_292_);
lean_ctor_set(v___x_294_, 9, v___x_292_);
lean_ctor_set(v___x_294_, 10, v___x_292_);
lean_ctor_set(v___x_294_, 11, v___x_291_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_unsigned_to_nat(32u);
v___x_296_ = lean_mk_empty_array_with_capacity(v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_298_ = ((size_t)5ULL);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_unsigned_to_nat(32u);
v___x_301_ = lean_mk_empty_array_with_capacity(v___x_300_);
v___x_302_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_303_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
lean_ctor_set(v___x_303_, 2, v___x_299_);
lean_ctor_set(v___x_303_, 3, v___x_299_);
lean_ctor_set_usize(v___x_303_, 4, v___x_298_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_box(1);
v___x_305_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
lean_ctor_set(v___x_307_, 2, v___x_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v_toCold_313_; lean_object* v_env_314_; lean_object* v_options_315_; uint8_t v___x_316_; lean_object* v_env_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_312_ = lean_st_ref_get(v___y_310_);
v_toCold_313_ = lean_ctor_get(v___y_309_, 0);
v_env_314_ = lean_ctor_get(v___x_312_, 0);
lean_inc_ref(v_env_314_);
lean_dec(v___x_312_);
v_options_315_ = lean_ctor_get(v_toCold_313_, 2);
v___x_316_ = 0;
v_env_317_ = l_Lean_Environment_setRecordingDeps(v_env_314_, v___x_316_);
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_315_);
v___x_320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_320_, 0, v_env_317_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_319_);
lean_ctor_set(v___x_320_, 3, v_options_315_);
v___x_321_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_msgData_308_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_ref_332_; lean_object* v___x_333_; lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_ref_332_ = lean_ctor_get(v___y_329_, 2);
v___x_333_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_328_, v___y_329_, v___y_330_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
lean_inc(v_ref_332_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_ref_332_);
lean_ctor_set(v___x_338_, 1, v_a_334_);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 1);
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_357_, lean_object* v_reservedName_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_362_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_363_ = 0;
v___x_364_ = l_Lean_MessageData_ofConstName(v_declName_357_, v___x_363_);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_362_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = 1;
v___x_369_ = l_Lean_MessageData_ofConstName(v_reservedName_358_, v___x_368_);
v___x_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_367_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_372_, v___y_359_, v___y_360_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_374_, lean_object* v_reservedName_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_374_, v_reservedName_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_380_, lean_object* v_suffix_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_reservedName_385_; lean_object* v___x_386_; lean_object* v_env_387_; uint8_t v___x_388_; uint8_t v___x_389_; 
lean_inc(v_declName_380_);
v_reservedName_385_ = l_Lean_Name_str___override(v_declName_380_, v_suffix_381_);
v___x_386_ = lean_st_ref_get(v___y_383_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v___x_388_ = 1;
lean_inc(v_reservedName_385_);
v___x_389_ = l_Lean_Environment_contains(v_env_387_, v_reservedName_385_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_reservedName_385_);
lean_dec(v_declName_380_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_380_, v_reservedName_385_, v___y_382_, v___y_383_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_393_, lean_object* v_suffix_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_393_, v_suffix_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_399_);
v___x_404_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_399_, v___x_403_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref_known(v___x_404_, 1);
v___x_405_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_399_);
v___x_406_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_399_, v___x_405_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref_known(v___x_406_, 1);
v___x_407_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_408_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_399_, v___x_407_, v_a_400_, v_a_401_);
return v___x_408_;
}
else
{
lean_dec(v_declName_399_);
return v___x_406_;
}
}
else
{
lean_dec(v_declName_399_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_415_, v___y_416_, v___y_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_420_, lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_420_, v_msg_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_425_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_426_, lean_object* v_n_427_){
_start:
{
lean_object* v___x_428_; 
lean_inc(v_n_427_);
lean_inc_ref(v_env_426_);
v___x_428_ = l_Lean_Meta_declFromEqLikeName(v_env_426_, v_n_427_);
if (lean_obj_tag(v___x_428_) == 1)
{
lean_object* v_val_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_val_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_429_);
lean_dec_ref_known(v___x_428_, 1);
v_fst_430_ = lean_ctor_get(v_val_429_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v_val_429_, 1);
lean_inc(v_snd_431_);
lean_dec(v_val_429_);
v___x_432_ = l_Lean_Meta_mkEqLikeNameFor(v_env_426_, v_fst_430_, v_snd_431_);
v___x_433_ = lean_name_eq(v_n_427_, v___x_432_);
lean_dec(v___x_432_);
lean_dec(v_n_427_);
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
lean_dec(v___x_428_);
lean_dec(v_n_427_);
lean_dec_ref(v_env_426_);
v___x_434_ = 0;
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_435_, lean_object* v_n_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_435_, v_n_436_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_441_; lean_object* v___x_442_; 
v___f_441_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_442_ = l_Lean_registerReservedNamePredicate(v___f_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_st_mk_ref(v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_450_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_453_ = lean_mk_io_user_error(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_454_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_initializing();
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v_f_454_);
v___x_457_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_459_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_460_ = lean_st_ref_take(v___x_459_);
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v_f_454_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_st_ref_put(v___x_459_, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_registerGetEqnsFn(v_f_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_477_; lean_object* v_env_478_; uint8_t v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_st_ref_get(v_a_471_);
v_env_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_env_478_);
lean_dec(v___x_477_);
v___x_479_ = 0;
lean_inc(v_declName_467_);
v___x_480_ = l_Lean_Environment_findAsync_x3f(v_env_478_, v_declName_467_, v___x_479_);
if (lean_obj_tag(v___x_480_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_512_; 
v_val_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_512_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_512_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_512_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v_kind_485_; 
v_kind_485_ = lean_ctor_get_uint8(v_val_481_, sizeof(void*)*3);
if (v_kind_485_ == 0)
{
lean_object* v_sig_486_; lean_object* v___x_487_; lean_object* v_env_488_; uint8_t v___x_489_; 
v_sig_486_ = lean_ctor_get(v_val_481_, 1);
lean_inc_ref(v_sig_486_);
lean_dec(v_val_481_);
v___x_487_ = lean_st_ref_get(v_a_471_);
v_env_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc_ref(v_env_488_);
lean_dec(v___x_487_);
v___x_489_ = l_Lean_Meta_isMatcherCore(v_env_488_, v_declName_467_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v_type_491_; lean_object* v___x_492_; 
lean_del_object(v___x_483_);
v___x_490_ = lean_task_get_own(v_sig_486_);
v_type_491_ = lean_ctor_get(v___x_490_, 2);
lean_inc_ref(v_type_491_);
lean_dec(v___x_490_);
v___x_492_ = l_Lean_Meta_isProp(v_type_491_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_507_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_507_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_507_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_507_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
uint8_t v___x_497_; 
v___x_497_ = lean_unbox(v_a_493_);
lean_dec(v_a_493_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = 1;
v___x_499_ = lean_box(v___x_498_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_499_);
v___x_501_ = v___x_495_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_box(v___x_489_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_503_);
v___x_505_ = v___x_495_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
return v___x_492_;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec_ref(v_sig_486_);
v___x_508_ = lean_box(v___x_479_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 0);
lean_ctor_set(v___x_483_, 0, v___x_508_);
v___x_510_ = v___x_483_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_del_object(v___x_483_);
lean_dec(v_val_481_);
lean_dec(v_declName_467_);
goto v___jp_473_;
}
}
}
else
{
lean_dec(v___x_480_);
lean_dec(v_declName_467_);
goto v___jp_473_;
}
v___jp_473_:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = 0;
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object* v___x_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v___x_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_527_);
return v_res_529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_530_; lean_object* v___f_531_; 
v___x_530_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_531_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_531_, 0, v___x_530_);
return v___f_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; 
v___f_538_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_box(1);
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_));
v___x_542_ = 0;
v___x_543_ = 1;
v___x_544_ = l_Lean_registerEnvExtension___redArg(v___f_538_, v___x_539_, v___x_540_, v___x_541_, v___x_542_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_547_, lean_object* v_opt_548_){
_start:
{
lean_object* v_name_549_; lean_object* v_defValue_550_; lean_object* v_map_551_; lean_object* v___x_552_; 
v_name_549_ = lean_ctor_get(v_opt_548_, 0);
v_defValue_550_ = lean_ctor_get(v_opt_548_, 1);
v_map_551_ = lean_ctor_get(v_opts_547_, 0);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_551_, v_name_549_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_inc(v_defValue_550_);
return v_defValue_550_;
}
else
{
lean_object* v_val_553_; 
v_val_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v___x_552_, 1);
if (lean_obj_tag(v_val_553_) == 3)
{
lean_object* v_v_554_; 
v_v_554_ = lean_ctor_get(v_val_553_, 0);
lean_inc(v_v_554_);
lean_dec_ref_known(v_val_553_, 1);
return v_v_554_;
}
else
{
lean_dec(v_val_553_);
lean_inc(v_defValue_550_);
return v_defValue_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_555_, lean_object* v_opt_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_555_, v_opt_556_);
lean_dec_ref(v_opt_556_);
lean_dec_ref(v_opts_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_561_, size_t v_sz_562_, size_t v_i_563_, lean_object* v_b_564_){
_start:
{
lean_object* v_a_566_; uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_lt(v_i_563_, v_sz_562_);
if (v___x_570_ == 0)
{
return v_b_564_;
}
else
{
lean_object* v_a_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v_map_574_; uint8_t v_hasTrace_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_588_; 
v_a_571_ = lean_array_uget_borrowed(v_as_561_, v_i_563_);
v_fst_572_ = lean_ctor_get(v_a_571_, 0);
v_snd_573_ = lean_ctor_get(v_a_571_, 1);
v_map_574_ = lean_ctor_get(v_b_564_, 0);
v_hasTrace_575_ = lean_ctor_get_uint8(v_b_564_, sizeof(void*)*1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_b_564_);
if (v_isSharedCheck_588_ == 0)
{
v___x_577_ = v_b_564_;
v_isShared_578_ = v_isSharedCheck_588_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_map_574_);
lean_dec(v_b_564_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_588_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; 
lean_inc(v_snd_573_);
lean_inc(v_fst_572_);
v___x_579_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_572_, v_snd_573_, v_map_574_);
if (v_hasTrace_575_ == 0)
{
lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_583_; 
v___x_580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_581_ = l_Lean_Name_isPrefixOf(v___x_580_, v_fst_572_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_579_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_581_);
v_a_566_ = v___x_583_;
goto v___jp_565_;
}
}
else
{
lean_object* v___x_586_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_586_ = v___x_577_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_587_, sizeof(void*)*1, v_hasTrace_575_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v_a_566_ = v___x_586_;
goto v___jp_565_;
}
}
}
}
v___jp_565_:
{
size_t v___x_567_; size_t v___x_568_; 
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_563_, v___x_567_);
v_i_563_ = v___x_568_;
v_b_564_ = v_a_566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_589_, lean_object* v_sz_590_, lean_object* v_i_591_, lean_object* v_b_592_){
_start:
{
size_t v_sz_boxed_593_; size_t v_i_boxed_594_; lean_object* v_res_595_; 
v_sz_boxed_593_ = lean_unbox_usize(v_sz_590_);
lean_dec(v_sz_590_);
v_i_boxed_594_ = lean_unbox_usize(v_i_591_);
lean_dec(v_i_591_);
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_589_, v_sz_boxed_593_, v_i_boxed_594_, v_b_592_);
lean_dec_ref(v_as_589_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_596_, lean_object* v_k_597_, uint8_t v_v_598_){
_start:
{
lean_object* v_map_599_; uint8_t v_hasTrace_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_614_; 
v_map_599_ = lean_ctor_get(v_o_596_, 0);
v_hasTrace_600_ = lean_ctor_get_uint8(v_o_596_, sizeof(void*)*1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_o_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_602_ = v_o_596_;
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_map_599_);
lean_dec(v_o_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_604_, 0, v_v_598_);
lean_inc(v_k_597_);
v___x_605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_597_, v___x_604_, v_map_599_);
if (v_hasTrace_600_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_609_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_607_ = l_Lean_Name_isPrefixOf(v___x_606_, v_k_597_);
lean_dec(v_k_597_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_605_);
v___x_609_ = v___x_602_;
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
return v___x_609_;
}
}
else
{
lean_object* v___x_612_; 
lean_dec(v_k_597_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_605_);
v___x_612_ = v___x_602_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
lean_ctor_set_uint8(v_reuseFailAlloc_613_, sizeof(void*)*1, v_hasTrace_600_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_615_, lean_object* v_k_616_, lean_object* v_v_617_){
_start:
{
uint8_t v_v_boxed_618_; lean_object* v_res_619_; 
v_v_boxed_618_ = lean_unbox(v_v_617_);
v_res_619_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_615_, v_k_616_, v_v_boxed_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_620_, lean_object* v_opt_621_, uint8_t v_val_622_){
_start:
{
lean_object* v_name_623_; lean_object* v___x_624_; 
v_name_623_ = lean_ctor_get(v_opt_621_, 0);
lean_inc(v_name_623_);
lean_dec_ref(v_opt_621_);
v___x_624_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_620_, v_name_623_, v_val_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_625_, lean_object* v_opt_626_, lean_object* v_val_627_){
_start:
{
uint8_t v_val_boxed_628_; lean_object* v_res_629_; 
v_val_boxed_628_ = lean_unbox(v_val_627_);
v_res_629_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_625_, v_opt_626_, v_val_boxed_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_630_, size_t v_i_631_, size_t v_stop_632_, lean_object* v_b_633_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = lean_usize_dec_eq(v_i_631_, v_stop_632_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v_defValue_636_; uint8_t v___x_637_; lean_object* v___x_638_; size_t v___x_639_; size_t v___x_640_; 
v___x_635_ = lean_array_uget_borrowed(v_as_630_, v_i_631_);
v_defValue_636_ = lean_ctor_get(v___x_635_, 1);
v___x_637_ = lean_unbox(v_defValue_636_);
lean_inc(v___x_635_);
v___x_638_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_633_, v___x_635_, v___x_637_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_add(v_i_631_, v___x_639_);
v_i_631_ = v___x_640_;
v_b_633_ = v___x_638_;
goto _start;
}
else
{
return v_b_633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_642_, lean_object* v_i_643_, lean_object* v_stop_644_, lean_object* v_b_645_){
_start:
{
size_t v_i_boxed_646_; size_t v_stop_boxed_647_; lean_object* v_res_648_; 
v_i_boxed_646_ = lean_unbox_usize(v_i_643_);
lean_dec(v_i_643_);
v_stop_boxed_647_ = lean_unbox_usize(v_stop_644_);
lean_dec(v_stop_644_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_642_, v_i_boxed_646_, v_stop_boxed_647_, v_b_645_);
lean_dec_ref(v_as_642_);
return v_res_648_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Array_instInhabited___redArg();
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = l_Lean_Meta_eqnAffectingOptions;
v___x_655_ = lean_array_get_size(v___x_654_);
return v___x_655_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_dec_lt(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_660_ = lean_nat_dec_le(v___x_659_, v___x_659_);
return v___x_660_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_661_; size_t v___x_662_; 
v___x_661_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_662_ = lean_usize_of_nat(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_663_, lean_object* v_act_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint16_t v___y_671_; lean_object* v___y_672_; lean_object* v_fileName_673_; lean_object* v_fileMap_674_; lean_object* v_currNamespace_675_; lean_object* v_openDecls_676_; lean_object* v_initHeartbeats_677_; lean_object* v_maxHeartbeats_678_; lean_object* v_quotContext_679_; lean_object* v_currMacroScope_680_; lean_object* v_cancelTk_x3f_681_; lean_object* v_inheritedTraceOptions_682_; lean_object* v_currRecDepth_683_; lean_object* v_ref_684_; uint8_t v_suppressElabErrors_685_; uint8_t v_isRecordingDeps_686_; lean_object* v___y_687_; uint8_t v___y_694_; lean_object* v___y_695_; uint16_t v___y_696_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_toCold_735_; lean_object* v_currRecDepth_736_; lean_object* v_ref_737_; uint8_t v_suppressElabErrors_738_; uint8_t v_isRecordingDeps_739_; lean_object* v_fileName_740_; lean_object* v_fileMap_741_; lean_object* v_options_742_; lean_object* v_currNamespace_743_; lean_object* v_openDecls_744_; lean_object* v_initHeartbeats_745_; lean_object* v_maxHeartbeats_746_; lean_object* v_quotContext_747_; lean_object* v_currMacroScope_748_; lean_object* v_cancelTk_x3f_749_; lean_object* v_inheritedTraceOptions_750_; lean_object* v___y_752_; 
v___x_733_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_734_ = lean_st_ref_get(v_a_668_);
v_toCold_735_ = lean_ctor_get(v_a_667_, 0);
v_currRecDepth_736_ = lean_ctor_get(v_a_667_, 1);
v_ref_737_ = lean_ctor_get(v_a_667_, 2);
v_suppressElabErrors_738_ = lean_ctor_get_uint8(v_a_667_, sizeof(void*)*3 + 2);
v_isRecordingDeps_739_ = lean_ctor_get_uint8(v_a_667_, sizeof(void*)*3 + 3);
v_fileName_740_ = lean_ctor_get(v_toCold_735_, 0);
v_fileMap_741_ = lean_ctor_get(v_toCold_735_, 1);
v_options_742_ = lean_ctor_get(v_toCold_735_, 2);
v_currNamespace_743_ = lean_ctor_get(v_toCold_735_, 4);
v_openDecls_744_ = lean_ctor_get(v_toCold_735_, 5);
v_initHeartbeats_745_ = lean_ctor_get(v_toCold_735_, 6);
v_maxHeartbeats_746_ = lean_ctor_get(v_toCold_735_, 7);
v_quotContext_747_ = lean_ctor_get(v_toCold_735_, 8);
v_currMacroScope_748_ = lean_ctor_get(v_toCold_735_, 9);
v_cancelTk_x3f_749_ = lean_ctor_get(v_toCold_735_, 10);
v_inheritedTraceOptions_750_ = lean_ctor_get(v_toCold_735_, 11);
if (v_isRecordingDeps_739_ == 0)
{
lean_object* v_env_763_; lean_object* v___x_764_; lean_object* v_toEnvExtension_765_; lean_object* v_asyncMode_766_; uint8_t v___x_767_; lean_object* v___x_768_; 
v_env_763_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_env_763_);
lean_dec(v___x_734_);
v___x_764_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_765_ = lean_ctor_get(v___x_764_, 0);
v_asyncMode_766_ = lean_ctor_get(v_toEnvExtension_765_, 2);
v___x_767_ = 0;
v___x_768_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_733_, v___x_764_, v_env_763_, v_declName_663_, v_asyncMode_766_, v___x_767_);
if (lean_obj_tag(v___x_768_) == 1)
{
lean_object* v_val_769_; lean_object* v___y_771_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_775_ = l_Lean_Meta_eqnAffectingOptions;
v___x_776_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_776_ == 0)
{
lean_inc_ref(v_options_742_);
v___y_771_ = v_options_742_;
goto v___jp_770_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_777_ == 0)
{
if (v___x_776_ == 0)
{
lean_inc_ref(v_options_742_);
v___y_771_ = v_options_742_;
goto v___jp_770_;
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_742_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_775_, v___x_778_, v___x_779_, v_options_742_);
v___y_771_ = v___x_780_;
goto v___jp_770_;
}
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_742_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_775_, v___x_781_, v___x_782_, v_options_742_);
v___y_771_ = v___x_783_;
goto v___jp_770_;
}
}
v___jp_770_:
{
size_t v_sz_772_; size_t v___x_773_; lean_object* v___x_774_; 
v_sz_772_ = lean_array_size(v_val_769_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_769_, v_sz_772_, v___x_773_, v___y_771_);
lean_dec(v_val_769_);
v___y_752_ = v___x_774_;
goto v___jp_751_;
}
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
lean_dec(v___x_768_);
v___x_784_ = l_Lean_Meta_eqnAffectingOptions;
v___x_785_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_785_ == 0)
{
lean_inc_ref(v_options_742_);
v___y_752_ = v_options_742_;
goto v___jp_751_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_786_ == 0)
{
if (v___x_785_ == 0)
{
lean_inc_ref(v_options_742_);
v___y_752_ = v_options_742_;
goto v___jp_751_;
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
v___x_787_ = ((size_t)0ULL);
v___x_788_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_742_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_784_, v___x_787_, v___x_788_, v_options_742_);
v___y_752_ = v___x_789_;
goto v___jp_751_;
}
}
else
{
size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; 
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_742_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_784_, v___x_790_, v___x_791_, v_options_742_);
v___y_752_ = v___x_792_;
goto v___jp_751_;
}
}
}
}
else
{
lean_object* v___x_793_; 
lean_dec(v___x_734_);
lean_dec(v_declName_663_);
lean_inc_ref(v_options_742_);
v___x_793_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_742_);
v___y_752_ = v___x_793_;
goto v___jp_751_;
}
v___jp_670_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_688_ = l_Lean_maxRecDepth;
v___x_689_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_672_, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_690_, 0, v_fileName_673_);
lean_ctor_set(v___x_690_, 1, v_fileMap_674_);
lean_ctor_set(v___x_690_, 2, v___y_672_);
lean_ctor_set(v___x_690_, 3, v___x_689_);
lean_ctor_set(v___x_690_, 4, v_currNamespace_675_);
lean_ctor_set(v___x_690_, 5, v_openDecls_676_);
lean_ctor_set(v___x_690_, 6, v_initHeartbeats_677_);
lean_ctor_set(v___x_690_, 7, v_maxHeartbeats_678_);
lean_ctor_set(v___x_690_, 8, v_quotContext_679_);
lean_ctor_set(v___x_690_, 9, v_currMacroScope_680_);
lean_ctor_set(v___x_690_, 10, v_cancelTk_x3f_681_);
lean_ctor_set(v___x_690_, 11, v_inheritedTraceOptions_682_);
lean_inc(v_ref_684_);
lean_inc(v_currRecDepth_683_);
v___x_691_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_currRecDepth_683_);
lean_ctor_set(v___x_691_, 2, v_ref_684_);
lean_ctor_set_uint16(v___x_691_, sizeof(void*)*3, v___y_671_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3 + 2, v_suppressElabErrors_685_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3 + 3, v_isRecordingDeps_686_);
lean_inc(v___y_687_);
lean_inc(v_a_666_);
lean_inc_ref(v_a_665_);
v___x_692_ = lean_apply_5(v_act_664_, v_a_665_, v_a_666_, v___x_691_, v___y_687_, lean_box(0));
return v___x_692_;
}
v___jp_693_:
{
lean_object* v___x_697_; lean_object* v_env_698_; lean_object* v_nextMacroScope_699_; lean_object* v_ngen_700_; lean_object* v_auxDeclNGen_701_; lean_object* v_traceState_702_; lean_object* v_recordedDeps_703_; lean_object* v_messages_704_; lean_object* v_infoState_705_; lean_object* v_snapshotTasks_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_731_; 
v___x_697_ = lean_st_ref_take(v_a_668_);
v_env_698_ = lean_ctor_get(v___x_697_, 0);
v_nextMacroScope_699_ = lean_ctor_get(v___x_697_, 1);
v_ngen_700_ = lean_ctor_get(v___x_697_, 2);
v_auxDeclNGen_701_ = lean_ctor_get(v___x_697_, 3);
v_traceState_702_ = lean_ctor_get(v___x_697_, 4);
v_recordedDeps_703_ = lean_ctor_get(v___x_697_, 6);
v_messages_704_ = lean_ctor_get(v___x_697_, 7);
v_infoState_705_ = lean_ctor_get(v___x_697_, 8);
v_snapshotTasks_706_ = lean_ctor_get(v___x_697_, 9);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v___x_697_, 5);
lean_dec(v_unused_732_);
v___x_708_ = v___x_697_;
v_isShared_709_ = v_isSharedCheck_731_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_snapshotTasks_706_);
lean_inc(v_infoState_705_);
lean_inc(v_messages_704_);
lean_inc(v_recordedDeps_703_);
lean_inc(v_traceState_702_);
lean_inc(v_auxDeclNGen_701_);
lean_inc(v_ngen_700_);
lean_inc(v_nextMacroScope_699_);
lean_inc(v_env_698_);
lean_dec(v___x_697_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_731_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = l_Lean_Kernel_enableDiag(v_env_698_, v___y_694_);
v___x_711_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 5, v___x_711_);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_nextMacroScope_699_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_ngen_700_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_auxDeclNGen_701_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_traceState_702_);
lean_ctor_set(v_reuseFailAlloc_730_, 5, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_730_, 6, v_recordedDeps_703_);
lean_ctor_set(v_reuseFailAlloc_730_, 7, v_messages_704_);
lean_ctor_set(v_reuseFailAlloc_730_, 8, v_infoState_705_);
lean_ctor_set(v_reuseFailAlloc_730_, 9, v_snapshotTasks_706_);
v___x_713_ = v_reuseFailAlloc_730_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v_toCold_715_; lean_object* v_currRecDepth_716_; lean_object* v_ref_717_; uint8_t v_suppressElabErrors_718_; uint8_t v_isRecordingDeps_719_; lean_object* v_fileName_720_; lean_object* v_fileMap_721_; lean_object* v_currNamespace_722_; lean_object* v_openDecls_723_; lean_object* v_initHeartbeats_724_; lean_object* v_maxHeartbeats_725_; lean_object* v_quotContext_726_; lean_object* v_currMacroScope_727_; lean_object* v_cancelTk_x3f_728_; lean_object* v_inheritedTraceOptions_729_; 
v___x_714_ = lean_st_ref_put(v_a_668_, v___x_713_);
v_toCold_715_ = lean_ctor_get(v_a_667_, 0);
v_currRecDepth_716_ = lean_ctor_get(v_a_667_, 1);
v_ref_717_ = lean_ctor_get(v_a_667_, 2);
v_suppressElabErrors_718_ = lean_ctor_get_uint8(v_a_667_, sizeof(void*)*3 + 2);
v_isRecordingDeps_719_ = lean_ctor_get_uint8(v_a_667_, sizeof(void*)*3 + 3);
v_fileName_720_ = lean_ctor_get(v_toCold_715_, 0);
v_fileMap_721_ = lean_ctor_get(v_toCold_715_, 1);
v_currNamespace_722_ = lean_ctor_get(v_toCold_715_, 4);
v_openDecls_723_ = lean_ctor_get(v_toCold_715_, 5);
v_initHeartbeats_724_ = lean_ctor_get(v_toCold_715_, 6);
v_maxHeartbeats_725_ = lean_ctor_get(v_toCold_715_, 7);
v_quotContext_726_ = lean_ctor_get(v_toCold_715_, 8);
v_currMacroScope_727_ = lean_ctor_get(v_toCold_715_, 9);
v_cancelTk_x3f_728_ = lean_ctor_get(v_toCold_715_, 10);
v_inheritedTraceOptions_729_ = lean_ctor_get(v_toCold_715_, 11);
lean_inc_ref(v_inheritedTraceOptions_729_);
lean_inc(v_cancelTk_x3f_728_);
lean_inc(v_currMacroScope_727_);
lean_inc(v_quotContext_726_);
lean_inc(v_maxHeartbeats_725_);
lean_inc(v_initHeartbeats_724_);
lean_inc(v_openDecls_723_);
lean_inc(v_currNamespace_722_);
lean_inc_ref(v_fileMap_721_);
lean_inc_ref(v_fileName_720_);
v___y_671_ = v___y_696_;
v___y_672_ = v___y_695_;
v_fileName_673_ = v_fileName_720_;
v_fileMap_674_ = v_fileMap_721_;
v_currNamespace_675_ = v_currNamespace_722_;
v_openDecls_676_ = v_openDecls_723_;
v_initHeartbeats_677_ = v_initHeartbeats_724_;
v_maxHeartbeats_678_ = v_maxHeartbeats_725_;
v_quotContext_679_ = v_quotContext_726_;
v_currMacroScope_680_ = v_currMacroScope_727_;
v_cancelTk_x3f_681_ = v_cancelTk_x3f_728_;
v_inheritedTraceOptions_682_ = v_inheritedTraceOptions_729_;
v_currRecDepth_683_ = v_currRecDepth_716_;
v_ref_684_ = v_ref_717_;
v_suppressElabErrors_685_ = v_suppressElabErrors_718_;
v_isRecordingDeps_686_ = v_isRecordingDeps_719_;
v___y_687_ = v_a_668_;
goto v___jp_670_;
}
}
}
v___jp_751_:
{
uint16_t v___x_753_; lean_object* v___x_754_; lean_object* v_env_755_; uint8_t v___x_756_; uint16_t v___x_757_; uint16_t v___x_758_; uint16_t v___x_759_; uint8_t v___x_760_; 
v___x_753_ = l_Lean_OptionFlags_ofOptions(v___y_752_);
v___x_754_ = lean_st_ref_get(v_a_668_);
v_env_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_env_755_);
lean_dec(v___x_754_);
v___x_756_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_755_);
lean_dec_ref(v_env_755_);
v___x_757_ = 512;
v___x_758_ = lean_uint16_land(v___x_753_, v___x_757_);
v___x_759_ = 0;
v___x_760_ = lean_uint16_dec_eq(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
if (v___x_756_ == 0)
{
uint8_t v___x_761_; 
v___x_761_ = 1;
v___y_694_ = v___x_761_;
v___y_695_ = v___y_752_;
v___y_696_ = v___x_753_;
goto v___jp_693_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_750_);
lean_inc(v_cancelTk_x3f_749_);
lean_inc(v_currMacroScope_748_);
lean_inc(v_quotContext_747_);
lean_inc(v_maxHeartbeats_746_);
lean_inc(v_initHeartbeats_745_);
lean_inc(v_openDecls_744_);
lean_inc(v_currNamespace_743_);
lean_inc_ref(v_fileMap_741_);
lean_inc_ref(v_fileName_740_);
v___y_671_ = v___x_753_;
v___y_672_ = v___y_752_;
v_fileName_673_ = v_fileName_740_;
v_fileMap_674_ = v_fileMap_741_;
v_currNamespace_675_ = v_currNamespace_743_;
v_openDecls_676_ = v_openDecls_744_;
v_initHeartbeats_677_ = v_initHeartbeats_745_;
v_maxHeartbeats_678_ = v_maxHeartbeats_746_;
v_quotContext_679_ = v_quotContext_747_;
v_currMacroScope_680_ = v_currMacroScope_748_;
v_cancelTk_x3f_681_ = v_cancelTk_x3f_749_;
v_inheritedTraceOptions_682_ = v_inheritedTraceOptions_750_;
v_currRecDepth_683_ = v_currRecDepth_736_;
v_ref_684_ = v_ref_737_;
v_suppressElabErrors_685_ = v_suppressElabErrors_738_;
v_isRecordingDeps_686_ = v_isRecordingDeps_739_;
v___y_687_ = v_a_668_;
goto v___jp_670_;
}
}
else
{
if (v___x_756_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_750_);
lean_inc(v_cancelTk_x3f_749_);
lean_inc(v_currMacroScope_748_);
lean_inc(v_quotContext_747_);
lean_inc(v_maxHeartbeats_746_);
lean_inc(v_initHeartbeats_745_);
lean_inc(v_openDecls_744_);
lean_inc(v_currNamespace_743_);
lean_inc_ref(v_fileMap_741_);
lean_inc_ref(v_fileName_740_);
v___y_671_ = v___x_753_;
v___y_672_ = v___y_752_;
v_fileName_673_ = v_fileName_740_;
v_fileMap_674_ = v_fileMap_741_;
v_currNamespace_675_ = v_currNamespace_743_;
v_openDecls_676_ = v_openDecls_744_;
v_initHeartbeats_677_ = v_initHeartbeats_745_;
v_maxHeartbeats_678_ = v_maxHeartbeats_746_;
v_quotContext_679_ = v_quotContext_747_;
v_currMacroScope_680_ = v_currMacroScope_748_;
v_cancelTk_x3f_681_ = v_cancelTk_x3f_749_;
v_inheritedTraceOptions_682_ = v_inheritedTraceOptions_750_;
v_currRecDepth_683_ = v_currRecDepth_736_;
v_ref_684_ = v_ref_737_;
v_suppressElabErrors_685_ = v_suppressElabErrors_738_;
v_isRecordingDeps_686_ = v_isRecordingDeps_739_;
v___y_687_ = v_a_668_;
goto v___jp_670_;
}
else
{
uint8_t v___x_762_; 
v___x_762_ = 0;
v___y_694_ = v___x_762_;
v___y_695_ = v___y_752_;
v___y_696_ = v___x_753_;
goto v___jp_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_794_, lean_object* v_act_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_794_, v_act_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_802_, lean_object* v_declName_803_, lean_object* v_act_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_803_, v_act_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_811_, lean_object* v_declName_812_, lean_object* v_act_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_811_, v_declName_812_, v_act_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_env_824_; lean_object* v_toConstantVal_825_; lean_object* v_value_826_; lean_object* v_all_827_; uint8_t v___y_829_; lean_object* v_type_837_; uint8_t v___x_838_; 
v___x_823_ = lean_st_ref_get(v___y_821_);
v_env_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_ref_n(v_env_824_, 2);
lean_dec(v___x_823_);
v_toConstantVal_825_ = lean_ctor_get(v_thm_820_, 0);
v_value_826_ = lean_ctor_get(v_thm_820_, 1);
v_all_827_ = lean_ctor_get(v_thm_820_, 2);
v_type_837_ = lean_ctor_get(v_toConstantVal_825_, 2);
v___x_838_ = l_Lean_Environment_hasUnsafe(v_env_824_, v_type_837_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; 
v___x_839_ = l_Lean_Environment_hasUnsafe(v_env_824_, v_value_826_);
v___y_829_ = v___x_839_;
goto v___jp_828_;
}
else
{
lean_dec_ref(v_env_824_);
v___y_829_ = v___x_838_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_830_, 0, v_thm_820_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc(v_all_827_);
lean_inc_ref(v_value_826_);
lean_inc_ref(v_toConstantVal_825_);
lean_dec_ref(v_thm_820_);
v___x_832_ = lean_box(0);
v___x_833_ = 0;
v___x_834_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_834_, 0, v_toConstantVal_825_);
lean_ctor_set(v___x_834_, 1, v_value_826_);
lean_ctor_set(v___x_834_, 2, v___x_832_);
lean_ctor_set(v___x_834_, 3, v_all_827_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*4, v___x_833_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_840_, v___y_841_);
lean_dec(v___y_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_844_, v___y_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_858_, lean_object* v_b_859_, lean_object* v_c_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
v___x_866_ = lean_apply_7(v_k_858_, v_b_859_, v_c_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, lean_box(0));
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_867_, lean_object* v_b_868_, lean_object* v_c_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_867_, v_b_868_, v_c_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_876_, lean_object* v_k_877_, uint8_t v_cleanupAnnotations_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___f_884_; uint8_t v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___f_884_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_884_, 0, v_k_877_);
v___x_885_ = 1;
v___x_886_ = 0;
v___x_887_ = lean_box(0);
v___x_888_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_876_, v___x_885_, v___x_886_, v___x_885_, v___x_886_, v___x_887_, v___f_884_, v_cleanupAnnotations_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_888_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_888_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_905_, lean_object* v_k_906_, lean_object* v_cleanupAnnotations_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_913_; lean_object* v_res_914_; 
v_cleanupAnnotations_boxed_913_ = lean_unbox(v_cleanupAnnotations_907_);
v_res_914_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_905_, v_k_906_, v_cleanupAnnotations_boxed_913_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_915_, lean_object* v_e_916_, lean_object* v_k_917_, uint8_t v_cleanupAnnotations_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_916_, v_k_917_, v_cleanupAnnotations_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_925_, lean_object* v_e_926_, lean_object* v_k_927_, lean_object* v_cleanupAnnotations_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_934_; lean_object* v_res_935_; 
v_cleanupAnnotations_boxed_934_ = lean_unbox(v_cleanupAnnotations_928_);
v_res_935_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_925_, v_e_926_, v_k_927_, v_cleanupAnnotations_boxed_934_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
if (lean_obj_tag(v_a_936_) == 0)
{
lean_object* v___x_938_; 
v___x_938_ = l_List_reverse___redArg(v_a_937_);
return v___x_938_;
}
else
{
lean_object* v_head_939_; lean_object* v_tail_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_949_; 
v_head_939_ = lean_ctor_get(v_a_936_, 0);
v_tail_940_ = lean_ctor_get(v_a_936_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_949_ == 0)
{
v___x_942_ = v_a_936_;
v_isShared_943_ = v_isSharedCheck_949_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_tail_940_);
lean_inc(v_head_939_);
lean_dec(v_a_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_949_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = l_Lean_mkLevelParam(v_head_939_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v_a_937_);
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_a_937_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
v_a_936_ = v_tail_940_;
v_a_937_ = v___x_946_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_950_, lean_object* v_name_951_, lean_object* v_xs_952_, lean_object* v_body_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_name_959_; lean_object* v_levelParams_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1030_; 
v_name_959_ = lean_ctor_get(v_toConstantVal_950_, 0);
v_levelParams_960_ = lean_ctor_get(v_toConstantVal_950_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_toConstantVal_950_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v_toConstantVal_950_, 2);
lean_dec(v_unused_1031_);
v___x_962_ = v_toConstantVal_950_;
v_isShared_963_ = v_isSharedCheck_1030_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_levelParams_960_);
lean_inc(v_name_959_);
lean_dec(v_toConstantVal_950_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1030_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_lhs_967_; lean_object* v___x_968_; 
v___x_964_ = lean_box(0);
lean_inc(v_levelParams_960_);
v___x_965_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_960_, v___x_964_);
v___x_966_ = l_Lean_mkConst(v_name_959_, v___x_965_);
v_lhs_967_ = l_Lean_mkAppN(v___x_966_, v_xs_952_);
lean_inc_ref(v_lhs_967_);
v___x_968_ = l_Lean_Meta_mkEq(v_lhs_967_, v_body_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; uint8_t v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = 0;
v___x_971_ = 1;
v___x_972_ = 1;
v___x_973_ = l_Lean_Meta_mkForallFVars(v_xs_952_, v_a_969_, v___x_970_, v___x_971_, v___x_971_, v___x_972_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = l_Lean_Meta_letToHave(v_a_974_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Lean_Meta_mkEqRefl(v_lhs_967_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l_Lean_Meta_mkLambdaFVars(v_xs_952_, v_a_978_, v___x_970_, v___x_971_, v___x_970_, v___x_971_, v___x_972_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
lean_inc(v_name_951_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v_a_976_);
lean_ctor_set(v___x_962_, 0, v_name_951_);
v___x_982_ = v___x_962_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_name_951_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_levelParams_960_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_a_976_);
v___x_982_ = v_reuseFailAlloc_989_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___x_987_; 
lean_inc(v_name_951_);
v___x_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_983_, 0, v_name_951_);
lean_ctor_set(v___x_983_, 1, v___x_964_);
v___x_984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v_a_980_);
lean_ctor_set(v___x_984_, 2, v___x_983_);
v___x_985_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_984_, v___y_957_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = l_Lean_addDecl(v_a_986_, v___x_970_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v___x_988_; 
lean_dec_ref_known(v___x_987_, 1);
v___x_988_ = l_Lean_inferDefEqAttr(v_name_951_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_988_;
}
else
{
lean_dec(v_name_951_);
return v___x_987_;
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_976_);
lean_del_object(v___x_962_);
lean_dec(v_levelParams_960_);
lean_dec(v_name_951_);
v_a_990_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_979_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_979_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_976_);
lean_del_object(v___x_962_);
lean_dec(v_levelParams_960_);
lean_dec(v_name_951_);
v_a_998_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_977_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_977_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v_lhs_967_);
lean_del_object(v___x_962_);
lean_dec(v_levelParams_960_);
lean_dec(v_name_951_);
v_a_1006_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_975_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_975_);
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
lean_dec_ref(v_lhs_967_);
lean_del_object(v___x_962_);
lean_dec(v_levelParams_960_);
lean_dec(v_name_951_);
v_a_1014_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_973_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_973_);
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
lean_dec_ref(v_lhs_967_);
lean_del_object(v___x_962_);
lean_dec(v_levelParams_960_);
lean_dec(v_name_951_);
v_a_1022_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_968_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_968_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1032_, lean_object* v_name_1033_, lean_object* v_xs_1034_, lean_object* v_body_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1032_, v_name_1033_, v_xs_1034_, v_body_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_xs_1034_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1042_, lean_object* v_info_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_toConstantVal_1049_; lean_object* v_value_1050_; lean_object* v___f_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; 
v_toConstantVal_1049_ = lean_ctor_get(v_info_1043_, 0);
lean_inc_ref(v_toConstantVal_1049_);
v_value_1050_ = lean_ctor_get(v_info_1043_, 1);
lean_inc_ref(v_value_1050_);
lean_dec_ref(v_info_1043_);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1051_, 0, v_toConstantVal_1049_);
lean_closure_set(v___f_1051_, 1, v_name_1042_);
v___x_1052_ = 1;
v___x_1053_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1050_, v___f_1051_, v___x_1052_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1054_, lean_object* v_info_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1054_, v_info_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1062_, lean_object* v_name_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1072_; lean_object* v_env_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; 
v___x_1072_ = lean_st_ref_get(v_a_1067_);
v_env_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref(v_env_1073_);
lean_dec(v___x_1072_);
v___x_1074_ = 0;
lean_inc(v_declName_1062_);
v___x_1075_ = l_Lean_Environment_find_x3f(v_env_1073_, v_declName_1062_, v___x_1074_);
if (lean_obj_tag(v___x_1075_) == 1)
{
lean_object* v_val_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1103_; 
v_val_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1103_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_val_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1103_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
if (lean_obj_tag(v_val_1076_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_val_1080_ = lean_ctor_get(v_val_1076_, 0);
lean_inc_ref(v_val_1080_);
lean_dec_ref_known(v_val_1076_, 1);
lean_inc_n(v_name_1063_, 2);
v___x_1081_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1081_, 0, v_name_1063_);
lean_closure_set(v___x_1081_, 1, v_val_1080_);
lean_inc(v_declName_1062_);
v___x_1082_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1082_, 0, lean_box(0));
lean_closure_set(v___x_1082_, 1, v_declName_1062_);
lean_closure_set(v___x_1082_, 2, v___x_1081_);
v___x_1083_ = l_Lean_Meta_realizeConst(v_declName_1062_, v_name_1063_, v___x_1082_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1093_; 
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v___x_1083_, 0);
lean_dec(v_unused_1094_);
v___x_1085_ = v___x_1083_;
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v___x_1083_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_name_1063_);
v___x_1088_ = v___x_1078_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_name_1063_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1088_);
v___x_1090_ = v___x_1085_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_del_object(v___x_1078_);
lean_dec(v_name_1063_);
v_a_1095_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1083_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1083_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_del_object(v___x_1078_);
lean_dec(v_val_1076_);
lean_dec(v_name_1063_);
lean_dec(v_declName_1062_);
goto v___jp_1069_;
}
}
}
else
{
lean_dec(v___x_1075_);
lean_dec(v_name_1063_);
lean_dec(v_declName_1062_);
goto v___jp_1069_;
}
v___jp_1069_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1104_, lean_object* v_name_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1104_, v_name_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_i_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_array_get_size(v_keys_1112_);
v___x_1117_ = lean_nat_dec_lt(v_i_1114_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec(v_i_1114_);
v___x_1118_ = lean_box(0);
return v___x_1118_;
}
else
{
lean_object* v_k_x27_1119_; uint8_t v___x_1120_; 
v_k_x27_1119_ = lean_array_fget_borrowed(v_keys_1112_, v_i_1114_);
v___x_1120_ = lean_name_eq(v_k_1115_, v_k_x27_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_i_1114_, v___x_1121_);
lean_dec(v_i_1114_);
v_i_1114_ = v___x_1122_;
goto _start;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_array_fget_borrowed(v_vals_1113_, v_i_1114_);
lean_dec(v_i_1114_);
lean_inc(v___x_1124_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1126_, lean_object* v_vals_1127_, lean_object* v_i_1128_, lean_object* v_k_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1126_, v_vals_1127_, v_i_1128_, v_k_1129_);
lean_dec(v_k_1129_);
lean_dec_ref(v_vals_1127_);
lean_dec_ref(v_keys_1126_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1131_, size_t v_x_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v_es_1134_; lean_object* v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v_j_1138_; lean_object* v___x_1139_; 
v_es_1134_ = lean_ctor_get(v_x_1131_, 0);
v___x_1135_ = lean_box(2);
v___x_1136_ = ((size_t)31ULL);
v___x_1137_ = lean_usize_land(v_x_1132_, v___x_1136_);
v_j_1138_ = lean_usize_to_nat(v___x_1137_);
v___x_1139_ = lean_array_get_borrowed(v___x_1135_, v_es_1134_, v_j_1138_);
lean_dec(v_j_1138_);
switch(lean_obj_tag(v___x_1139_))
{
case 0:
{
lean_object* v_key_1140_; lean_object* v_val_1141_; uint8_t v___x_1142_; 
v_key_1140_ = lean_ctor_get(v___x_1139_, 0);
v_val_1141_ = lean_ctor_get(v___x_1139_, 1);
v___x_1142_ = lean_name_eq(v_x_1133_, v_key_1140_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
lean_inc(v_val_1141_);
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_val_1141_);
return v___x_1144_;
}
}
case 1:
{
lean_object* v_node_1145_; size_t v___x_1146_; size_t v___x_1147_; 
v_node_1145_ = lean_ctor_get(v___x_1139_, 0);
v___x_1146_ = ((size_t)5ULL);
v___x_1147_ = lean_usize_shift_right(v_x_1132_, v___x_1146_);
v_x_1131_ = v_node_1145_;
v_x_1132_ = v___x_1147_;
goto _start;
}
default: 
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
}
}
else
{
lean_object* v_ks_1150_; lean_object* v_vs_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_ks_1150_ = lean_ctor_get(v_x_1131_, 0);
v_vs_1151_ = lean_ctor_get(v_x_1131_, 1);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1150_, v_vs_1151_, v___x_1152_, v_x_1133_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
size_t v_x_344__boxed_1157_; lean_object* v_res_1158_; 
v_x_344__boxed_1157_ = lean_unbox_usize(v_x_1155_);
lean_dec(v_x_1155_);
v_res_1158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1154_, v_x_344__boxed_1157_, v_x_1156_);
lean_dec(v_x_1156_);
lean_dec_ref(v_x_1154_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
uint64_t v___y_1162_; 
if (lean_obj_tag(v_x_1160_) == 0)
{
uint64_t v___x_1165_; 
v___x_1165_ = 1723ULL;
v___y_1162_ = v___x_1165_;
goto v___jp_1161_;
}
else
{
uint64_t v_hash_1166_; 
v_hash_1166_ = lean_ctor_get_uint64(v_x_1160_, sizeof(void*)*2);
v___y_1162_ = v_hash_1166_;
goto v___jp_1161_;
}
v___jp_1161_:
{
size_t v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_uint64_to_usize(v___y_1162_);
v___x_1164_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1159_, v___x_1163_, v_x_1160_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1167_, lean_object* v_x_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1167_, v_x_1168_);
lean_dec(v_x_1168_);
lean_dec_ref(v_x_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_env_1175_; lean_object* v___x_1176_; lean_object* v_asyncMode_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1173_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1174_ = lean_st_ref_get(v_a_1171_);
v_env_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc_ref(v_env_1175_);
lean_dec(v___x_1174_);
v___x_1176_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1177_ = lean_ctor_get(v___x_1176_, 2);
v___x_1178_ = lean_box(0);
v___x_1179_ = 0;
v___x_1180_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1173_, v___x_1176_, v_env_1175_, v_asyncMode_1177_, v___x_1178_, v___x_1179_);
v___x_1181_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1180_, v_thmName_1170_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec(v_thmName_1183_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1187_, v_a_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_thmName_1192_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1198_, v_x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1201_, v_x_1202_, v_x_1203_);
lean_dec(v_x_1203_);
lean_dec_ref(v_x_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1205_, lean_object* v_x_1206_, size_t v_x_1207_, lean_object* v_x_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1206_, v_x_1207_, v_x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
size_t v_x_439__boxed_1214_; lean_object* v_res_1215_; 
v_x_439__boxed_1214_ = lean_unbox_usize(v_x_1212_);
lean_dec(v_x_1212_);
v_res_1215_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1210_, v_x_1211_, v_x_439__boxed_1214_, v_x_1213_);
lean_dec(v_x_1213_);
lean_dec_ref(v_x_1211_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1216_, lean_object* v_keys_1217_, lean_object* v_vals_1218_, lean_object* v_heq_1219_, lean_object* v_i_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1217_, v_vals_1218_, v_i_1220_, v_k_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1223_, lean_object* v_keys_1224_, lean_object* v_vals_1225_, lean_object* v_heq_1226_, lean_object* v_i_1227_, lean_object* v_k_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1223_, v_keys_1224_, v_vals_1225_, v_heq_1226_, v_i_1227_, v_k_1228_);
lean_dec(v_k_1228_);
lean_dec_ref(v_vals_1225_);
lean_dec_ref(v_keys_1224_);
return v_res_1229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1230_, lean_object* v_i_1231_, lean_object* v_k_1232_){
_start:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v_keys_1230_);
v___x_1234_ = lean_nat_dec_lt(v_i_1231_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v_i_1231_);
return v___x_1234_;
}
else
{
lean_object* v_k_x27_1235_; uint8_t v___x_1236_; 
v_k_x27_1235_ = lean_array_fget_borrowed(v_keys_1230_, v_i_1231_);
v___x_1236_ = lean_name_eq(v_k_1232_, v_k_x27_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_add(v_i_1231_, v___x_1237_);
lean_dec(v_i_1231_);
v_i_1231_ = v___x_1238_;
goto _start;
}
else
{
lean_dec(v_i_1231_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1240_, lean_object* v_i_1241_, lean_object* v_k_1242_){
_start:
{
uint8_t v_res_1243_; lean_object* v_r_1244_; 
v_res_1243_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1240_, v_i_1241_, v_k_1242_);
lean_dec(v_k_1242_);
lean_dec_ref(v_keys_1240_);
v_r_1244_ = lean_box(v_res_1243_);
return v_r_1244_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1245_, size_t v_x_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
lean_object* v_es_1248_; lean_object* v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v_j_1252_; lean_object* v___x_1253_; 
v_es_1248_ = lean_ctor_get(v_x_1245_, 0);
v___x_1249_ = lean_box(2);
v___x_1250_ = ((size_t)31ULL);
v___x_1251_ = lean_usize_land(v_x_1246_, v___x_1250_);
v_j_1252_ = lean_usize_to_nat(v___x_1251_);
v___x_1253_ = lean_array_get_borrowed(v___x_1249_, v_es_1248_, v_j_1252_);
lean_dec(v_j_1252_);
switch(lean_obj_tag(v___x_1253_))
{
case 0:
{
lean_object* v_key_1254_; uint8_t v___x_1255_; 
v_key_1254_ = lean_ctor_get(v___x_1253_, 0);
v___x_1255_ = lean_name_eq(v_x_1247_, v_key_1254_);
return v___x_1255_;
}
case 1:
{
lean_object* v_node_1256_; size_t v___x_1257_; size_t v___x_1258_; 
v_node_1256_ = lean_ctor_get(v___x_1253_, 0);
v___x_1257_ = ((size_t)5ULL);
v___x_1258_ = lean_usize_shift_right(v_x_1246_, v___x_1257_);
v_x_1245_ = v_node_1256_;
v_x_1246_ = v___x_1258_;
goto _start;
}
default: 
{
uint8_t v___x_1260_; 
v___x_1260_ = 0;
return v___x_1260_;
}
}
}
else
{
lean_object* v_ks_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_ks_1261_ = lean_ctor_get(v_x_1245_, 0);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1261_, v___x_1262_, v_x_1247_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
size_t v_x_328__boxed_1267_; uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_x_328__boxed_1267_ = lean_unbox_usize(v_x_1265_);
lean_dec(v_x_1265_);
v_res_1268_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1264_, v_x_328__boxed_1267_, v_x_1266_);
lean_dec(v_x_1266_);
lean_dec_ref(v_x_1264_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
uint64_t v___y_1273_; 
if (lean_obj_tag(v_x_1271_) == 0)
{
uint64_t v___x_1276_; 
v___x_1276_ = 1723ULL;
v___y_1273_ = v___x_1276_;
goto v___jp_1272_;
}
else
{
uint64_t v_hash_1277_; 
v_hash_1277_ = lean_ctor_get_uint64(v_x_1271_, sizeof(void*)*2);
v___y_1273_ = v_hash_1277_;
goto v___jp_1272_;
}
v___jp_1272_:
{
size_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = lean_uint64_to_usize(v___y_1273_);
v___x_1275_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1270_, v___x_1274_, v_x_1271_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1278_, v_x_1279_);
lean_dec(v_x_1279_);
lean_dec_ref(v_x_1278_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_env_1287_; lean_object* v___x_1288_; lean_object* v_asyncMode_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1285_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1286_ = lean_st_ref_get(v_a_1283_);
v_env_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc_ref(v_env_1287_);
lean_dec(v___x_1286_);
v___x_1288_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1289_ = lean_ctor_get(v___x_1288_, 2);
v___x_1290_ = lean_box(0);
v___x_1291_ = 0;
v___x_1292_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1285_, v___x_1288_, v_env_1287_, v_asyncMode_1289_, v___x_1290_, v___x_1291_);
v___x_1293_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1292_, v_thmName_1282_);
lean_dec(v___x_1292_);
v___x_1294_ = lean_box(v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec(v_thmName_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1300_, v_a_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_isEqnThm(v_thmName_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_thmName_1305_);
return v_res_1309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1311_, v_x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_res_1317_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1314_, v_x_1315_, v_x_1316_);
lean_dec(v_x_1316_);
lean_dec_ref(v_x_1315_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, size_t v_x_1321_, lean_object* v_x_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1320_, v_x_1321_, v_x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
size_t v_x_419__boxed_1328_; uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_x_419__boxed_1328_ = lean_unbox_usize(v_x_1326_);
lean_dec(v_x_1326_);
v_res_1329_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1324_, v_x_1325_, v_x_419__boxed_1328_, v_x_1327_);
lean_dec(v_x_1327_);
lean_dec_ref(v_x_1325_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1331_, lean_object* v_keys_1332_, lean_object* v_vals_1333_, lean_object* v_heq_1334_, lean_object* v_i_1335_, lean_object* v_k_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1332_, v_i_1335_, v_k_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1338_, lean_object* v_keys_1339_, lean_object* v_vals_1340_, lean_object* v_heq_1341_, lean_object* v_i_1342_, lean_object* v_k_1343_){
_start:
{
uint8_t v_res_1344_; lean_object* v_r_1345_; 
v_res_1344_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1338_, v_keys_1339_, v_vals_1340_, v_heq_1341_, v_i_1342_, v_k_1343_);
lean_dec(v_k_1343_);
lean_dec_ref(v_vals_1340_);
lean_dec_ref(v_keys_1339_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1346_, lean_object* v_msg_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_panic_fn_borrowed(v_x1_1346_, v_msg_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1349_, lean_object* v_msg_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1349_, v_msg_1350_);
lean_dec_ref(v_x1_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v_ks_1356_; lean_object* v_vs_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1381_; 
v_ks_1356_ = lean_ctor_get(v_x_1352_, 0);
v_vs_1357_ = lean_ctor_get(v_x_1352_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1359_ = v_x_1352_;
v_isShared_1360_ = v_isSharedCheck_1381_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_vs_1357_);
lean_inc(v_ks_1356_);
lean_dec(v_x_1352_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1381_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = lean_array_get_size(v_ks_1356_);
v___x_1362_ = lean_nat_dec_lt(v_x_1353_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec(v_x_1353_);
v___x_1363_ = lean_array_push(v_ks_1356_, v_x_1354_);
v___x_1364_ = lean_array_push(v_vs_1357_, v_x_1355_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1364_);
lean_ctor_set(v___x_1359_, 0, v___x_1363_);
v___x_1366_ = v___x_1359_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
else
{
lean_object* v_k_x27_1368_; uint8_t v___x_1369_; 
v_k_x27_1368_ = lean_array_fget_borrowed(v_ks_1356_, v_x_1353_);
v___x_1369_ = lean_name_eq(v_x_1354_, v_k_x27_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1371_; 
if (v_isShared_1360_ == 0)
{
v___x_1371_ = v___x_1359_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_ks_1356_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_vs_1357_);
v___x_1371_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v_x_1353_, v___x_1372_);
lean_dec(v_x_1353_);
v_x_1352_ = v___x_1371_;
v_x_1353_ = v___x_1373_;
goto _start;
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = lean_array_fset(v_ks_1356_, v_x_1353_, v_x_1354_);
v___x_1377_ = lean_array_fset(v_vs_1357_, v_x_1353_, v_x_1355_);
lean_dec(v_x_1353_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1377_);
lean_ctor_set(v___x_1359_, 0, v___x_1376_);
v___x_1379_ = v___x_1359_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1382_, lean_object* v_k_1383_, lean_object* v_v_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1382_, v___x_1385_, v_k_1383_, v_v_1384_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1388_, size_t v_x_1389_, size_t v_x_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
if (lean_obj_tag(v_x_1388_) == 0)
{
lean_object* v_es_1393_; size_t v___x_1394_; size_t v___x_1395_; lean_object* v_j_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_es_1393_ = lean_ctor_get(v_x_1388_, 0);
v___x_1394_ = ((size_t)31ULL);
v___x_1395_ = lean_usize_land(v_x_1389_, v___x_1394_);
v_j_1396_ = lean_usize_to_nat(v___x_1395_);
v___x_1397_ = lean_array_get_size(v_es_1393_);
v___x_1398_ = lean_nat_dec_lt(v_j_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_dec(v_j_1396_);
lean_dec(v_x_1392_);
lean_dec(v_x_1391_);
return v_x_1388_;
}
else
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1437_; 
lean_inc_ref(v_es_1393_);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1388_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_x_1388_, 0);
lean_dec(v_unused_1438_);
v___x_1400_ = v_x_1388_;
v_isShared_1401_ = v_isSharedCheck_1437_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_x_1388_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1437_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_v_1402_; lean_object* v___x_1403_; lean_object* v_xs_x27_1404_; lean_object* v___y_1406_; 
v_v_1402_ = lean_array_fget(v_es_1393_, v_j_1396_);
v___x_1403_ = lean_box(0);
v_xs_x27_1404_ = lean_array_fset(v_es_1393_, v_j_1396_, v___x_1403_);
switch(lean_obj_tag(v_v_1402_))
{
case 0:
{
lean_object* v_key_1411_; lean_object* v_val_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1422_; 
v_key_1411_ = lean_ctor_get(v_v_1402_, 0);
v_val_1412_ = lean_ctor_get(v_v_1402_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_v_1402_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1414_ = v_v_1402_;
v_isShared_1415_ = v_isSharedCheck_1422_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_val_1412_);
lean_inc(v_key_1411_);
lean_dec(v_v_1402_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1422_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_name_eq(v_x_1391_, v_key_1411_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_del_object(v___x_1414_);
v___x_1417_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1411_, v_val_1412_, v_x_1391_, v_x_1392_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
v___y_1406_ = v___x_1418_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1420_; 
lean_dec(v_val_1412_);
lean_dec(v_key_1411_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v_x_1392_);
lean_ctor_set(v___x_1414_, 0, v_x_1391_);
v___x_1420_ = v___x_1414_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_x_1391_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_x_1392_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
v___y_1406_ = v___x_1420_;
goto v___jp_1405_;
}
}
}
}
case 1:
{
lean_object* v_node_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1435_; 
v_node_1423_ = lean_ctor_get(v_v_1402_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_v_1402_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1425_ = v_v_1402_;
v_isShared_1426_ = v_isSharedCheck_1435_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_node_1423_);
lean_dec(v_v_1402_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1435_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
size_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1427_ = ((size_t)5ULL);
v___x_1428_ = lean_usize_shift_right(v_x_1389_, v___x_1427_);
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_add(v_x_1390_, v___x_1429_);
v___x_1431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1423_, v___x_1428_, v___x_1430_, v_x_1391_, v_x_1392_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1431_);
v___x_1433_ = v___x_1425_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
v___y_1406_ = v___x_1433_;
goto v___jp_1405_;
}
}
}
default: 
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_x_1391_);
lean_ctor_set(v___x_1436_, 1, v_x_1392_);
v___y_1406_ = v___x_1436_;
goto v___jp_1405_;
}
}
v___jp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_array_fset(v_xs_x27_1404_, v_j_1396_, v___y_1406_);
lean_dec(v_j_1396_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1407_);
v___x_1409_ = v___x_1400_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
else
{
lean_object* v_ks_1439_; lean_object* v_vs_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1458_; 
v_ks_1439_ = lean_ctor_get(v_x_1388_, 0);
v_vs_1440_ = lean_ctor_get(v_x_1388_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_x_1388_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1442_ = v_x_1388_;
v_isShared_1443_ = v_isSharedCheck_1458_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_vs_1440_);
lean_inc(v_ks_1439_);
lean_dec(v_x_1388_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1458_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_ks_1439_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_vs_1440_);
v___x_1445_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v_newNode_1446_; size_t v___x_1447_; uint8_t v___x_1448_; 
v_newNode_1446_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1445_, v_x_1391_, v_x_1392_);
v___x_1447_ = ((size_t)7ULL);
v___x_1448_ = lean_usize_dec_le(v___x_1447_, v_x_1390_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1446_);
v___x_1450_ = lean_unsigned_to_nat(4u);
v___x_1451_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
lean_dec(v___x_1449_);
if (v___x_1451_ == 0)
{
lean_object* v_ks_1452_; lean_object* v_vs_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_ks_1452_ = lean_ctor_get(v_newNode_1446_, 0);
lean_inc_ref(v_ks_1452_);
v_vs_1453_ = lean_ctor_get(v_newNode_1446_, 1);
lean_inc_ref(v_vs_1453_);
lean_dec_ref(v_newNode_1446_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1390_, v_ks_1452_, v_vs_1453_, v___x_1454_, v___x_1455_);
lean_dec_ref(v_vs_1453_);
lean_dec_ref(v_ks_1452_);
return v___x_1456_;
}
else
{
return v_newNode_1446_;
}
}
else
{
return v_newNode_1446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1459_, lean_object* v_keys_1460_, lean_object* v_vals_1461_, lean_object* v_i_1462_, lean_object* v_entries_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = lean_array_get_size(v_keys_1460_);
v___x_1465_ = lean_nat_dec_lt(v_i_1462_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_dec(v_i_1462_);
return v_entries_1463_;
}
else
{
lean_object* v_k_1466_; lean_object* v_v_1467_; uint64_t v___y_1469_; 
v_k_1466_ = lean_array_fget_borrowed(v_keys_1460_, v_i_1462_);
v_v_1467_ = lean_array_fget_borrowed(v_vals_1461_, v_i_1462_);
if (lean_obj_tag(v_k_1466_) == 0)
{
uint64_t v___x_1480_; 
v___x_1480_ = 1723ULL;
v___y_1469_ = v___x_1480_;
goto v___jp_1468_;
}
else
{
uint64_t v_hash_1481_; 
v_hash_1481_ = lean_ctor_get_uint64(v_k_1466_, sizeof(void*)*2);
v___y_1469_ = v_hash_1481_;
goto v___jp_1468_;
}
v___jp_1468_:
{
size_t v_h_1470_; size_t v___x_1471_; lean_object* v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; size_t v_h_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_h_1470_ = lean_uint64_to_usize(v___y_1469_);
v___x_1471_ = ((size_t)5ULL);
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_sub(v_depth_1459_, v___x_1473_);
v___x_1475_ = lean_usize_mul(v___x_1471_, v___x_1474_);
v_h_1476_ = lean_usize_shift_right(v_h_1470_, v___x_1475_);
v___x_1477_ = lean_nat_add(v_i_1462_, v___x_1472_);
lean_dec(v_i_1462_);
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
v___x_1478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1463_, v_h_1476_, v_depth_1459_, v_k_1466_, v_v_1467_);
v_i_1462_ = v___x_1477_;
v_entries_1463_ = v___x_1478_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1482_, lean_object* v_keys_1483_, lean_object* v_vals_1484_, lean_object* v_i_1485_, lean_object* v_entries_1486_){
_start:
{
size_t v_depth_boxed_1487_; lean_object* v_res_1488_; 
v_depth_boxed_1487_ = lean_unbox_usize(v_depth_1482_);
lean_dec(v_depth_1482_);
v_res_1488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1487_, v_keys_1483_, v_vals_1484_, v_i_1485_, v_entries_1486_);
lean_dec_ref(v_vals_1484_);
lean_dec_ref(v_keys_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
size_t v_x_909__boxed_1494_; size_t v_x_910__boxed_1495_; lean_object* v_res_1496_; 
v_x_909__boxed_1494_ = lean_unbox_usize(v_x_1490_);
lean_dec(v_x_1490_);
v_x_910__boxed_1495_ = lean_unbox_usize(v_x_1491_);
lean_dec(v_x_1491_);
v_res_1496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1489_, v_x_909__boxed_1494_, v_x_910__boxed_1495_, v_x_1492_, v_x_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
uint64_t v___y_1501_; 
if (lean_obj_tag(v_x_1498_) == 0)
{
uint64_t v___x_1505_; 
v___x_1505_ = 1723ULL;
v___y_1501_ = v___x_1505_;
goto v___jp_1500_;
}
else
{
uint64_t v_hash_1506_; 
v_hash_1506_ = lean_ctor_get_uint64(v_x_1498_, sizeof(void*)*2);
v___y_1501_ = v_hash_1506_;
goto v___jp_1500_;
}
v___jp_1500_:
{
size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_uint64_to_usize(v___y_1501_);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1497_, v___x_1502_, v___x_1503_, v_x_1498_, v_x_1499_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1512_, lean_object* v_as_1513_, size_t v_i_1514_, size_t v_stop_1515_, lean_object* v_b_1516_){
_start:
{
lean_object* v___y_1518_; uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_eq(v_i_1514_, v_stop_1515_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_array_uget_borrowed(v_as_1513_, v_i_1514_);
v___x_1524_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1516_, v___x_1523_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; 
lean_inc(v_declName_1512_);
lean_inc(v___x_1523_);
v___x_1525_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1516_, v___x_1523_, v_declName_1512_);
v___y_1518_ = v___x_1525_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1526_; uint8_t v___x_1527_; 
v_val_1526_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1527_ = lean_name_eq(v_val_1526_, v_declName_1512_);
if (v___x_1527_ == 0)
{
uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1528_ = 1;
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1531_ = lean_unsigned_to_nat(227u);
v___x_1532_ = lean_unsigned_to_nat(10u);
v___x_1533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1523_);
v___x_1534_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1523_, v___x_1528_);
v___x_1535_ = lean_string_append(v___x_1533_, v___x_1534_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1537_ = lean_string_append(v___x_1535_, v___x_1536_);
v___x_1538_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1526_, v___x_1528_);
v___x_1539_ = lean_string_append(v___x_1537_, v___x_1538_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
v___x_1542_ = l_mkPanicMessageWithDecl(v___x_1529_, v___x_1530_, v___x_1531_, v___x_1532_, v___x_1541_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = lean_panic_fn_borrowed(v_b_1516_, v___x_1542_);
lean_dec_ref(v_b_1516_);
v___y_1518_ = v___x_1543_;
goto v___jp_1517_;
}
else
{
lean_dec(v_val_1526_);
v___y_1518_ = v_b_1516_;
goto v___jp_1517_;
}
}
}
else
{
lean_dec(v_declName_1512_);
return v_b_1516_;
}
v___jp_1517_:
{
size_t v___x_1519_; size_t v___x_1520_; 
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1514_, v___x_1519_);
v_i_1514_ = v___x_1520_;
v_b_1516_ = v___y_1518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1544_, lean_object* v_as_1545_, lean_object* v_i_1546_, lean_object* v_stop_1547_, lean_object* v_b_1548_){
_start:
{
size_t v_i_boxed_1549_; size_t v_stop_boxed_1550_; lean_object* v_res_1551_; 
v_i_boxed_1549_ = lean_unbox_usize(v_i_1546_);
lean_dec(v_i_1546_);
v_stop_boxed_1550_ = lean_unbox_usize(v_stop_1547_);
lean_dec(v_stop_1547_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1544_, v_as_1545_, v_i_boxed_1549_, v_stop_boxed_1550_, v_b_1548_);
lean_dec_ref(v_as_1545_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1552_, lean_object* v_declName_1553_, lean_object* v_s_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_get_size(v_eqThms_1552_);
v___x_1557_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec(v_declName_1553_);
return v_s_1554_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_nat_dec_le(v___x_1556_, v___x_1556_);
if (v___x_1558_ == 0)
{
if (v___x_1557_ == 0)
{
lean_dec(v_declName_1553_);
return v_s_1554_;
}
else
{
size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = lean_usize_of_nat(v___x_1556_);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1553_, v_eqThms_1552_, v___x_1559_, v___x_1560_, v_s_1554_);
return v___x_1561_;
}
}
else
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_of_nat(v___x_1556_);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1553_, v_eqThms_1552_, v___x_1562_, v___x_1563_, v_s_1554_);
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1565_, lean_object* v_declName_1566_, lean_object* v_s_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1565_, v_declName_1566_, v_s_1567_);
lean_dec_ref(v_eqThms_1565_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1569_, lean_object* v_eqThms_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v_env_1575_; lean_object* v_nextMacroScope_1576_; lean_object* v_ngen_1577_; lean_object* v_auxDeclNGen_1578_; lean_object* v_traceState_1579_; lean_object* v_recordedDeps_1580_; lean_object* v_messages_1581_; lean_object* v_infoState_1582_; lean_object* v_snapshotTasks_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1599_; 
v___f_1573_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1573_, 0, v_eqThms_1570_);
lean_closure_set(v___f_1573_, 1, v_declName_1569_);
v___x_1574_ = lean_st_ref_take(v_a_1571_);
v_env_1575_ = lean_ctor_get(v___x_1574_, 0);
v_nextMacroScope_1576_ = lean_ctor_get(v___x_1574_, 1);
v_ngen_1577_ = lean_ctor_get(v___x_1574_, 2);
v_auxDeclNGen_1578_ = lean_ctor_get(v___x_1574_, 3);
v_traceState_1579_ = lean_ctor_get(v___x_1574_, 4);
v_recordedDeps_1580_ = lean_ctor_get(v___x_1574_, 6);
v_messages_1581_ = lean_ctor_get(v___x_1574_, 7);
v_infoState_1582_ = lean_ctor_get(v___x_1574_, 8);
v_snapshotTasks_1583_ = lean_ctor_get(v___x_1574_, 9);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v___x_1574_, 5);
lean_dec(v_unused_1600_);
v___x_1585_ = v___x_1574_;
v_isShared_1586_ = v_isSharedCheck_1599_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snapshotTasks_1583_);
lean_inc(v_infoState_1582_);
lean_inc(v_messages_1581_);
lean_inc(v_recordedDeps_1580_);
lean_inc(v_traceState_1579_);
lean_inc(v_auxDeclNGen_1578_);
lean_inc(v_ngen_1577_);
lean_inc(v_nextMacroScope_1576_);
lean_inc(v_env_1575_);
lean_dec(v___x_1574_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1599_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v_asyncMode_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1587_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1588_ = lean_ctor_get(v___x_1587_, 2);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_box(0);
v___x_1591_ = 1;
v___x_1592_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1587_, v_env_1575_, v___f_1573_, v_asyncMode_1588_, v___x_1590_, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 5, v___x_1593_);
lean_ctor_set(v___x_1585_, 0, v___x_1592_);
v___x_1595_ = v___x_1585_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_nextMacroScope_1576_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_ngen_1577_);
lean_ctor_set(v_reuseFailAlloc_1598_, 3, v_auxDeclNGen_1578_);
lean_ctor_set(v_reuseFailAlloc_1598_, 4, v_traceState_1579_);
lean_ctor_set(v_reuseFailAlloc_1598_, 5, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1598_, 6, v_recordedDeps_1580_);
lean_ctor_set(v_reuseFailAlloc_1598_, 7, v_messages_1581_);
lean_ctor_set(v_reuseFailAlloc_1598_, 8, v_infoState_1582_);
lean_ctor_set(v_reuseFailAlloc_1598_, 9, v_snapshotTasks_1583_);
v___x_1595_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_st_ref_put(v_a_1571_, v___x_1595_);
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1589_);
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1601_, lean_object* v_eqThms_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1601_, v_eqThms_1602_, v_a_1603_);
lean_dec(v_a_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1606_, lean_object* v_eqThms_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1606_, v_eqThms_1607_, v_a_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1612_, lean_object* v_eqThms_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1612_, v_eqThms_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1619_, v_x_1620_, v_x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1623_, lean_object* v_x_1624_, size_t v_x_1625_, size_t v_x_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1624_, v_x_1625_, v_x_1626_, v_x_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
size_t v_x_1231__boxed_1636_; size_t v_x_1232__boxed_1637_; lean_object* v_res_1638_; 
v_x_1231__boxed_1636_ = lean_unbox_usize(v_x_1632_);
lean_dec(v_x_1632_);
v_x_1232__boxed_1637_ = lean_unbox_usize(v_x_1633_);
lean_dec(v_x_1633_);
v_res_1638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1630_, v_x_1631_, v_x_1231__boxed_1636_, v_x_1232__boxed_1637_, v_x_1634_, v_x_1635_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1639_, lean_object* v_n_1640_, lean_object* v_k_1641_, lean_object* v_v_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1640_, v_k_1641_, v_v_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1644_, size_t v_depth_1645_, lean_object* v_keys_1646_, lean_object* v_vals_1647_, lean_object* v_heq_1648_, lean_object* v_i_1649_, lean_object* v_entries_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1645_, v_keys_1646_, v_vals_1647_, v_i_1649_, v_entries_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1652_, lean_object* v_depth_1653_, lean_object* v_keys_1654_, lean_object* v_vals_1655_, lean_object* v_heq_1656_, lean_object* v_i_1657_, lean_object* v_entries_1658_){
_start:
{
size_t v_depth_boxed_1659_; lean_object* v_res_1660_; 
v_depth_boxed_1659_ = lean_unbox_usize(v_depth_1653_);
lean_dec(v_depth_1653_);
v_res_1660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1652_, v_depth_boxed_1659_, v_keys_1654_, v_vals_1655_, v_heq_1656_, v_i_1657_, v_entries_1658_);
lean_dec_ref(v_vals_1655_);
lean_dec_ref(v_keys_1654_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1662_, v_x_1663_, v_x_1664_, v_x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1667_, lean_object* v_env_1668_, lean_object* v_idx_1669_, lean_object* v_eqs_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_nextEq_1677_; uint8_t v___x_1678_; 
v___x_1672_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_nat_add(v_idx_1669_, v___x_1673_);
lean_dec(v_idx_1669_);
lean_inc(v___x_1674_);
v___x_1675_ = l_Nat_reprFast(v___x_1674_);
v___x_1676_ = lean_string_append(v___x_1672_, v___x_1675_);
lean_dec_ref(v___x_1675_);
lean_inc(v_declName_1667_);
lean_inc_ref(v_env_1668_);
v_nextEq_1677_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1668_, v_declName_1667_, v___x_1676_);
v___x_1678_ = l_Lean_Environment_containsOnBranch(v_env_1668_, v_nextEq_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_nextEq_1677_);
lean_dec(v___x_1674_);
lean_dec_ref(v_env_1668_);
lean_dec(v_declName_1667_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_eqs_1670_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_array_push(v_eqs_1670_, v_nextEq_1677_);
v_idx_1669_ = v___x_1674_;
v_eqs_1670_ = v___x_1680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1682_, lean_object* v_env_1683_, lean_object* v_idx_1684_, lean_object* v_eqs_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1682_, v_env_1683_, v_idx_1684_, v_eqs_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1688_, lean_object* v_env_1689_, lean_object* v_idx_1690_, lean_object* v_eqs_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1688_, v_env_1689_, v_idx_1690_, v_eqs_1691_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1698_, lean_object* v_env_1699_, lean_object* v_idx_1700_, lean_object* v_eqs_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1698_, v_env_1699_, v_idx_1700_, v_eqs_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v_env_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; uint8_t v___x_1716_; 
v___x_1711_ = lean_st_ref_get(v_a_1709_);
v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref_n(v_env_1712_, 3);
lean_dec(v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1708_);
v___x_1714_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1712_, v_declName_1708_, v___x_1713_);
v___x_1715_ = 1;
lean_inc(v___x_1714_);
v___x_1716_ = l_Lean_Environment_contains(v_env_1712_, v___x_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v___x_1714_);
lean_dec_ref(v_env_1712_);
lean_dec(v_declName_1708_);
v___x_1717_ = lean_box(0);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1719_ = lean_unsigned_to_nat(1u);
v___x_1720_ = lean_mk_empty_array_with_capacity(v___x_1719_);
v___x_1721_ = lean_array_push(v___x_1720_, v___x_1714_);
lean_inc(v_declName_1708_);
v___x_1722_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1708_, v_env_1712_, v___x_1719_, v___x_1721_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1732_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc_n(v_a_1723_, 2);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1708_, v_a_1723_, v_a_1709_);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v___x_1724_, 0);
lean_dec(v_unused_1733_);
v___x_1726_ = v___x_1724_;
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
else
{
lean_dec(v___x_1724_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_a_1723_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1728_);
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_declName_1708_);
v_a_1734_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1722_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1722_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1742_, v_a_1743_);
lean_dec(v_a_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1746_, v_a_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1760_, lean_object* v_localInsts_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1760_, v_localInsts_1761_, v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1768_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1768_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1785_, lean_object* v_localInsts_1786_, lean_object* v_x_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1785_, v_localInsts_1786_, v_x_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1794_, lean_object* v_lctx_1795_, lean_object* v_localInsts_1796_, lean_object* v_x_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1795_, v_localInsts_1796_, v_x_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1804_, lean_object* v_lctx_1805_, lean_object* v_localInsts_1806_, lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1804_, v_lctx_1805_, v_localInsts_1806_, v_x_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1817_, lean_object* v_as_x27_1818_, lean_object* v_b_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
if (lean_obj_tag(v_as_x27_1818_) == 0)
{
lean_object* v___x_1825_; 
lean_dec(v_declName_1817_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_b_1819_);
return v___x_1825_;
}
else
{
lean_object* v_head_1826_; lean_object* v_tail_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_b_1819_);
v_head_1826_ = lean_ctor_get(v_as_x27_1818_, 0);
v_tail_1827_ = lean_ctor_get(v_as_x27_1818_, 1);
v___x_1828_ = lean_box(0);
v___x_1829_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1826_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
lean_inc(v___y_1821_);
lean_inc_ref(v___y_1820_);
lean_inc(v_declName_1817_);
v___x_1830_ = lean_apply_6(v_head_1826_, v_declName_1817_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, lean_box(0));
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
if (lean_obj_tag(v_a_1831_) == 1)
{
lean_object* v_val_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1842_; 
v_val_1832_ = lean_ctor_get(v_a_1831_, 0);
lean_inc(v_val_1832_);
v___x_1833_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1817_, v_val_1832_, v___y_1823_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v___x_1833_, 0);
lean_dec(v_unused_1843_);
v___x_1835_ = v___x_1833_;
v_isShared_1836_ = v_isSharedCheck_1842_;
goto v_resetjp_1834_;
}
else
{
lean_dec(v___x_1833_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1842_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v_a_1831_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1828_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1838_);
v___x_1840_ = v___x_1835_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_dec(v_a_1831_);
v_as_x27_1818_ = v_tail_1827_;
v_b_1819_ = v___x_1829_;
goto _start;
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_declName_1817_);
v_a_1845_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1830_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1830_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1853_, lean_object* v_as_x27_1854_, lean_object* v_b_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1853_, v_as_x27_1854_, v_b_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v_as_x27_1854_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
lean_inc(v_declName_1862_);
v___x_1868_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1906_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1906_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1906_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_unbox(v_a_1869_);
lean_dec(v_a_1869_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_dec(v_declName_1862_);
v___x_1874_ = lean_box(0);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
else
{
lean_object* v___x_1878_; 
lean_del_object(v___x_1871_);
lean_inc(v_declName_1862_);
v___x_1878_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1862_, v___y_1866_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
if (lean_obj_tag(v_a_1879_) == 1)
{
lean_dec(v_declName_1862_);
return v___x_1878_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1881_ = lean_st_ref_get(v___x_1880_);
v___x_1882_ = lean_box(0);
v___x_1883_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1884_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1862_, v___x_1881_, v___x_1883_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___x_1881_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1897_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1897_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1897_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_fst_1889_; 
v_fst_1889_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_fst_1889_);
lean_dec(v_a_1885_);
if (lean_obj_tag(v_fst_1889_) == 0)
{
lean_object* v___x_1891_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1882_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1882_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
else
{
lean_object* v_val_1893_; lean_object* v___x_1895_; 
v_val_1893_ = lean_ctor_get(v_fst_1889_, 0);
lean_inc(v_val_1893_);
lean_dec_ref_known(v_fst_1889_, 1);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v_val_1893_);
v___x_1895_ = v___x_1887_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_val_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1884_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1884_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
else
{
lean_dec(v_declName_1862_);
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_declName_1862_);
v_a_1907_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1868_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1868_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1924_ = lean_box(1);
v___x_1925_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1926_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1925_);
lean_ctor_set(v___x_1927_, 2, v___x_1924_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___f_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___f_1936_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1936_, 0, v_declName_1930_);
v___x_1937_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1938_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1939_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1937_, v___x_1938_, v___f_1936_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1947_, lean_object* v_as_1948_, lean_object* v_as_x27_1949_, lean_object* v_b_1950_, lean_object* v_a_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1947_, v_as_x27_1949_, v_b_1950_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1958_, lean_object* v_as_1959_, lean_object* v_as_x27_1960_, lean_object* v_b_1961_, lean_object* v_a_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1958_, v_as_1959_, v_as_x27_1960_, v_b_1961_, v_a_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v_as_x27_1960_);
lean_dec(v_as_1959_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1975_ = lean_unsigned_to_nat(32u);
v___x_1976_ = lean_mk_empty_array_with_capacity(v___x_1975_);
lean_dec_ref(v___x_1976_);
v___x_1977_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1978_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1969_);
v___x_1979_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1979_, 0, v_declName_1969_);
v___x_1980_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1980_, 0, lean_box(0));
lean_closure_set(v___x_1980_, 1, v_declName_1969_);
lean_closure_set(v___x_1980_, 2, v___x_1979_);
v___x_1981_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1977_, v___x_1978_, v___x_1980_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
return v_res_1988_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_1989_, lean_object* v_opt_1990_){
_start:
{
lean_object* v_name_1991_; lean_object* v_defValue_1992_; lean_object* v_map_1993_; lean_object* v___x_1994_; 
v_name_1991_ = lean_ctor_get(v_opt_1990_, 0);
v_defValue_1992_ = lean_ctor_get(v_opt_1990_, 1);
v_map_1993_ = lean_ctor_get(v_opts_1989_, 0);
v___x_1994_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1993_, v_name_1991_);
if (lean_obj_tag(v___x_1994_) == 0)
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_unbox(v_defValue_1992_);
return v___x_1995_;
}
else
{
lean_object* v_val_1996_; 
v_val_1996_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v___x_1994_, 1);
if (lean_obj_tag(v_val_1996_) == 1)
{
uint8_t v_v_1997_; 
v_v_1997_ = lean_ctor_get_uint8(v_val_1996_, 0);
lean_dec_ref_known(v_val_1996_, 0);
return v_v_1997_;
}
else
{
uint8_t v___x_1998_; 
lean_dec(v_val_1996_);
v___x_1998_ = lean_unbox(v_defValue_1992_);
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_1999_, lean_object* v_opt_2000_){
_start:
{
uint8_t v_res_2001_; lean_object* v_r_2002_; 
v_res_2001_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_1999_, v_opt_2000_);
lean_dec_ref(v_opt_2000_);
lean_dec_ref(v_opts_1999_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2003_, lean_object* v_as_2004_, size_t v_sz_2005_, size_t v_i_2006_, lean_object* v_b_2007_){
_start:
{
lean_object* v_a_2010_; uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_lt(v_i_2006_, v_sz_2005_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_b_2007_);
return v___x_2015_;
}
else
{
lean_object* v_a_2016_; lean_object* v_defValue_2017_; uint8_t v___x_2018_; uint8_t v___y_2032_; uint8_t v___x_2033_; 
v_a_2016_ = lean_array_uget(v_as_2004_, v_i_2006_);
v_defValue_2017_ = lean_ctor_get(v_a_2016_, 1);
v___x_2018_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2003_, v_a_2016_);
v___x_2033_ = lean_unbox(v_defValue_2017_);
if (v___x_2033_ == 0)
{
if (v___x_2018_ == 0)
{
v___y_2032_ = v___x_2014_;
goto v___jp_2031_;
}
else
{
goto v___jp_2019_;
}
}
else
{
v___y_2032_ = v___x_2018_;
goto v___jp_2031_;
}
v___jp_2019_:
{
lean_object* v_name_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2029_; 
v_name_2020_ = lean_ctor_get(v_a_2016_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_a_2016_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_a_2016_, 1);
lean_dec(v_unused_2030_);
v___x_2022_ = v_a_2016_;
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_name_2020_);
lean_dec(v_a_2016_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2024_, 0, v___x_2018_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 1, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_name_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_array_push(v_b_2007_, v___x_2026_);
v_a_2010_ = v___x_2027_;
goto v___jp_2009_;
}
}
}
v___jp_2031_:
{
if (v___y_2032_ == 0)
{
goto v___jp_2019_;
}
else
{
lean_dec(v_a_2016_);
v_a_2010_ = v_b_2007_;
goto v___jp_2009_;
}
}
}
v___jp_2009_:
{
size_t v___x_2011_; size_t v___x_2012_; 
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_add(v_i_2006_, v___x_2011_);
v_i_2006_ = v___x_2012_;
v_b_2007_ = v_a_2010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2034_, lean_object* v_as_2035_, lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_){
_start:
{
size_t v_sz_boxed_2040_; size_t v_i_boxed_2041_; lean_object* v_res_2042_; 
v_sz_boxed_2040_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2041_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2034_, v_as_2035_, v_sz_boxed_2040_, v_i_boxed_2041_, v_b_2038_);
lean_dec_ref(v_as_2035_);
lean_dec_ref(v___x_2034_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v_env_2050_; uint8_t v___x_2051_; lean_object* v_env_2052_; lean_object* v___x_2053_; lean_object* v_toCold_2054_; lean_object* v_mctx_2055_; lean_object* v_lctx_2056_; lean_object* v_options_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2049_ = lean_st_ref_get(v___y_2047_);
v_env_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc_ref(v_env_2050_);
lean_dec(v___x_2049_);
v___x_2051_ = 0;
v_env_2052_ = l_Lean_Environment_setRecordingDeps(v_env_2050_, v___x_2051_);
v___x_2053_ = lean_st_ref_get(v___y_2045_);
v_toCold_2054_ = lean_ctor_get(v___y_2046_, 0);
v_mctx_2055_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_ref(v_mctx_2055_);
lean_dec(v___x_2053_);
v_lctx_2056_ = lean_ctor_get(v___y_2044_, 2);
v_options_2057_ = lean_ctor_get(v_toCold_2054_, 2);
lean_inc_ref(v_options_2057_);
lean_inc_ref(v_lctx_2056_);
v___x_2058_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2058_, 0, v_env_2052_);
lean_ctor_set(v___x_2058_, 1, v_mctx_2055_);
lean_ctor_set(v___x_2058_, 2, v_lctx_2056_);
lean_ctor_set(v___x_2058_, 3, v_options_2057_);
v___x_2059_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_msgData_2043_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2068_; double v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = lean_float_of_nat(v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2073_, lean_object* v_msg_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_ref_2080_; lean_object* v___x_2081_; lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2127_; 
v_ref_2080_ = lean_ctor_get(v___y_2077_, 2);
v___x_2081_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2127_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2127_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v_traceState_2087_; lean_object* v_env_2088_; lean_object* v_nextMacroScope_2089_; lean_object* v_ngen_2090_; lean_object* v_auxDeclNGen_2091_; lean_object* v_cache_2092_; lean_object* v_recordedDeps_2093_; lean_object* v_messages_2094_; lean_object* v_infoState_2095_; lean_object* v_snapshotTasks_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2126_; 
v___x_2086_ = lean_st_ref_take(v___y_2078_);
v_traceState_2087_ = lean_ctor_get(v___x_2086_, 4);
v_env_2088_ = lean_ctor_get(v___x_2086_, 0);
v_nextMacroScope_2089_ = lean_ctor_get(v___x_2086_, 1);
v_ngen_2090_ = lean_ctor_get(v___x_2086_, 2);
v_auxDeclNGen_2091_ = lean_ctor_get(v___x_2086_, 3);
v_cache_2092_ = lean_ctor_get(v___x_2086_, 5);
v_recordedDeps_2093_ = lean_ctor_get(v___x_2086_, 6);
v_messages_2094_ = lean_ctor_get(v___x_2086_, 7);
v_infoState_2095_ = lean_ctor_get(v___x_2086_, 8);
v_snapshotTasks_2096_ = lean_ctor_get(v___x_2086_, 9);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2098_ = v___x_2086_;
v_isShared_2099_ = v_isSharedCheck_2126_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_snapshotTasks_2096_);
lean_inc(v_infoState_2095_);
lean_inc(v_messages_2094_);
lean_inc(v_recordedDeps_2093_);
lean_inc(v_cache_2092_);
lean_inc(v_traceState_2087_);
lean_inc(v_auxDeclNGen_2091_);
lean_inc(v_ngen_2090_);
lean_inc(v_nextMacroScope_2089_);
lean_inc(v_env_2088_);
lean_dec(v___x_2086_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2126_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
uint64_t v_tid_2100_; lean_object* v_traces_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2125_; 
v_tid_2100_ = lean_ctor_get_uint64(v_traceState_2087_, sizeof(void*)*1);
v_traces_2101_ = lean_ctor_get(v_traceState_2087_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_traceState_2087_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2103_ = v_traceState_2087_;
v_isShared_2104_ = v_isSharedCheck_2125_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_traces_2101_);
lean_dec(v_traceState_2087_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2125_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; double v___x_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2108_ = 0;
v___x_2109_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2110_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2110_, 0, v_cls_2073_);
lean_ctor_set(v___x_2110_, 1, v___x_2106_);
lean_ctor_set(v___x_2110_, 2, v___x_2109_);
lean_ctor_set_float(v___x_2110_, sizeof(void*)*3, v___x_2107_);
lean_ctor_set_float(v___x_2110_, sizeof(void*)*3 + 8, v___x_2107_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*3 + 16, v___x_2108_);
v___x_2111_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2112_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v_a_2082_);
lean_ctor_set(v___x_2112_, 2, v___x_2111_);
lean_inc(v_ref_2080_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v_ref_2080_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = l_Lean_PersistentArray_push___redArg(v_traces_2101_, v___x_2113_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2114_);
v___x_2116_ = v___x_2103_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2114_);
lean_ctor_set_uint64(v_reuseFailAlloc_2124_, sizeof(void*)*1, v_tid_2100_);
v___x_2116_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 4, v___x_2116_);
v___x_2118_ = v___x_2098_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_env_2088_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_nextMacroScope_2089_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_ngen_2090_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_auxDeclNGen_2091_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2123_, 5, v_cache_2092_);
lean_ctor_set(v_reuseFailAlloc_2123_, 6, v_recordedDeps_2093_);
lean_ctor_set(v_reuseFailAlloc_2123_, 7, v_messages_2094_);
lean_ctor_set(v_reuseFailAlloc_2123_, 8, v_infoState_2095_);
lean_ctor_set(v_reuseFailAlloc_2123_, 9, v_snapshotTasks_2096_);
v___x_2118_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_st_ref_put(v___y_2078_, v___x_2118_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2105_);
v___x_2121_ = v___x_2084_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2105_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2128_, lean_object* v_msg_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2128_, v_msg_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2135_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2138_; size_t v_sz_2139_; 
v___x_2138_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2139_ = lean_array_size(v___x_2138_);
return v_sz_2139_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2141_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
lean_ctor_set(v___x_2141_, 2, v___x_2140_);
lean_ctor_set(v___x_2141_, 3, v___x_2140_);
lean_ctor_set(v___x_2141_, 4, v___x_2140_);
lean_ctor_set(v___x_2141_, 5, v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2150_ = l_Lean_Name_append(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2153_ = l_Lean_stringToMessageData(v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; size_t v_sz_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2160_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2157_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2163_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2164_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2160_, v___x_2163_, v_sz_2164_, v___x_2165_, v___x_2162_);
lean_dec_ref(v___x_2160_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2230_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2230_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2230_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___y_2174_; lean_object* v___y_2175_; 
v___x_2171_ = lean_array_get_size(v_a_2167_);
v___x_2172_ = lean_nat_dec_eq(v___x_2171_, v___x_2161_);
if (v___x_2172_ == 0)
{
lean_object* v_toCold_2217_; lean_object* v_options_2218_; uint8_t v_hasTrace_2219_; 
v_toCold_2217_ = lean_ctor_get(v_a_2157_, 0);
v_options_2218_ = lean_ctor_get(v_toCold_2217_, 2);
v_hasTrace_2219_ = lean_ctor_get_uint8(v_options_2218_, sizeof(void*)*1);
if (v_hasTrace_2219_ == 0)
{
v___y_2174_ = v_a_2156_;
v___y_2175_ = v_a_2158_;
goto v___jp_2173_;
}
else
{
lean_object* v_inheritedTraceOptions_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_inheritedTraceOptions_2220_ = lean_ctor_get(v_toCold_2217_, 11);
v___x_2221_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2222_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2220_, v_options_2218_, v___x_2222_);
if (v___x_2223_ == 0)
{
v___y_2174_ = v_a_2156_;
v___y_2175_ = v_a_2158_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2224_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2154_);
v___x_2225_ = l_Lean_MessageData_ofName(v_declName_2154_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2221_, v___x_2226_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_dec_ref_known(v___x_2227_, 1);
v___y_2174_ = v_a_2156_;
v___y_2175_ = v_a_2158_;
goto v___jp_2173_;
}
else
{
lean_del_object(v___x_2169_);
lean_dec(v_a_2167_);
lean_dec(v_declName_2154_);
return v___x_2227_;
}
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_del_object(v___x_2169_);
lean_dec(v_a_2167_);
lean_dec(v_declName_2154_);
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
v___jp_2173_:
{
lean_object* v___x_2176_; lean_object* v_env_2177_; lean_object* v_nextMacroScope_2178_; lean_object* v_ngen_2179_; lean_object* v_auxDeclNGen_2180_; lean_object* v_traceState_2181_; lean_object* v_recordedDeps_2182_; lean_object* v_messages_2183_; lean_object* v_infoState_2184_; lean_object* v_snapshotTasks_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2215_; 
v___x_2176_ = lean_st_ref_take(v___y_2175_);
v_env_2177_ = lean_ctor_get(v___x_2176_, 0);
v_nextMacroScope_2178_ = lean_ctor_get(v___x_2176_, 1);
v_ngen_2179_ = lean_ctor_get(v___x_2176_, 2);
v_auxDeclNGen_2180_ = lean_ctor_get(v___x_2176_, 3);
v_traceState_2181_ = lean_ctor_get(v___x_2176_, 4);
v_recordedDeps_2182_ = lean_ctor_get(v___x_2176_, 6);
v_messages_2183_ = lean_ctor_get(v___x_2176_, 7);
v_infoState_2184_ = lean_ctor_get(v___x_2176_, 8);
v_snapshotTasks_2185_ = lean_ctor_get(v___x_2176_, 9);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v___x_2176_, 5);
lean_dec(v_unused_2216_);
v___x_2187_ = v___x_2176_;
v_isShared_2188_ = v_isSharedCheck_2215_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_snapshotTasks_2185_);
lean_inc(v_infoState_2184_);
lean_inc(v_messages_2183_);
lean_inc(v_recordedDeps_2182_);
lean_inc(v_traceState_2181_);
lean_inc(v_auxDeclNGen_2180_);
lean_inc(v_ngen_2179_);
lean_inc(v_nextMacroScope_2178_);
lean_inc(v_env_2177_);
lean_dec(v___x_2176_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2215_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2189_ = l_Lean_Meta_eqnOptionsExt;
v___x_2190_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2189_, v_env_2177_, v_declName_2154_, v_a_2167_, v___x_2172_);
v___x_2191_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 5, v___x_2191_);
lean_ctor_set(v___x_2187_, 0, v___x_2190_);
v___x_2193_ = v___x_2187_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_nextMacroScope_2178_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_ngen_2179_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_auxDeclNGen_2180_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_traceState_2181_);
lean_ctor_set(v_reuseFailAlloc_2214_, 5, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2214_, 6, v_recordedDeps_2182_);
lean_ctor_set(v_reuseFailAlloc_2214_, 7, v_messages_2183_);
lean_ctor_set(v_reuseFailAlloc_2214_, 8, v_infoState_2184_);
lean_ctor_set(v_reuseFailAlloc_2214_, 9, v_snapshotTasks_2185_);
v___x_2193_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v_mctx_2196_; lean_object* v_zetaDeltaFVarIds_2197_; lean_object* v_postponed_2198_; lean_object* v_diag_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2212_; 
v___x_2194_ = lean_st_ref_put(v___y_2175_, v___x_2193_);
v___x_2195_ = lean_st_ref_take(v___y_2174_);
v_mctx_2196_ = lean_ctor_get(v___x_2195_, 0);
v_zetaDeltaFVarIds_2197_ = lean_ctor_get(v___x_2195_, 2);
v_postponed_2198_ = lean_ctor_get(v___x_2195_, 3);
v_diag_2199_ = lean_ctor_get(v___x_2195_, 4);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2195_, 1);
lean_dec(v_unused_2213_);
v___x_2201_ = v___x_2195_;
v_isShared_2202_ = v_isSharedCheck_2212_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_diag_2199_);
lean_inc(v_postponed_2198_);
lean_inc(v_zetaDeltaFVarIds_2197_);
lean_inc(v_mctx_2196_);
lean_dec(v___x_2195_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2212_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 1, v___x_2204_);
v___x_2206_ = v___x_2201_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_mctx_2196_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_zetaDeltaFVarIds_2197_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_postponed_2198_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_diag_2199_);
v___x_2206_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = lean_st_ref_put(v___y_2174_, v___x_2206_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2203_);
v___x_2209_ = v___x_2169_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2203_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
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
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_declName_2154_);
v_a_2231_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2166_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2166_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2246_, lean_object* v_as_2247_, size_t v_sz_2248_, size_t v_i_2249_, lean_object* v_b_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2246_, v_as_2247_, v_sz_2248_, v_i_2249_, v_b_2250_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2257_, lean_object* v_as_2258_, lean_object* v_sz_2259_, lean_object* v_i_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2259_);
lean_dec(v_sz_2259_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2260_);
lean_dec(v_i_2260_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2257_, v_as_2258_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_as_2258_);
lean_dec_ref(v___x_2257_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_st_mk_ref(v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2276_){
_start:
{
uint8_t v___x_2278_; 
v___x_2278_ = l_Lean_initializing();
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v_f_2276_);
v___x_2279_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2281_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2282_ = lean_st_ref_take(v___x_2281_);
v___x_2283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2283_, 0, v_f_2276_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_st_ref_put(v___x_2281_, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2292_, lean_object* v_as_x27_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
if (lean_obj_tag(v_as_x27_2293_) == 0)
{
lean_object* v___x_2300_; 
lean_dec(v_declName_2292_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_b_2294_);
return v___x_2300_;
}
else
{
lean_object* v_head_2301_; lean_object* v_tail_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_dec_ref(v_b_2294_);
v_head_2301_ = lean_ctor_get(v_as_x27_2293_, 0);
v_tail_2302_ = lean_ctor_get(v_as_x27_2293_, 1);
v___x_2303_ = lean_box(0);
v___x_2304_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2301_);
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v_declName_2292_);
v___x_2305_ = lean_apply_6(v_head_2301_, v_declName_2292_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, lean_box(0));
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2316_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2316_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2316_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
if (lean_obj_tag(v_a_2306_) == 1)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_dec(v_declName_2292_);
v___x_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2310_, 0, v_a_2306_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v___x_2303_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2311_);
v___x_2313_ = v___x_2308_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
else
{
lean_del_object(v___x_2308_);
lean_dec(v_a_2306_);
v_as_x27_2293_ = v_tail_2302_;
v_b_2294_ = v___x_2304_;
goto _start;
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_declName_2292_);
v_a_2317_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2305_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2305_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2325_, lean_object* v_as_x27_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2325_, v_as_x27_2326_, v_b_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v_as_x27_2326_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2334_, lean_object* v_declName_2335_, uint8_t v_nonRec_2336_, lean_object* v___x_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2346_; lean_object* v_env_2347_; uint8_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2346_ = lean_st_ref_get(v___y_2341_);
v_env_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc_ref(v_env_2347_);
lean_dec(v___x_2346_);
v___x_2348_ = 1;
lean_inc(v___x_2334_);
v___x_2349_ = l_Lean_Environment_contains(v_env_2347_, v___x_2334_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec(v___x_2334_);
lean_inc(v_declName_2335_);
v___x_2350_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2335_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; uint8_t v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2352_ = lean_unbox(v_a_2351_);
lean_dec(v_a_2351_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v___x_2337_);
lean_dec(v_declName_2335_);
goto v___jp_2343_;
}
else
{
lean_object* v___x_2353_; 
lean_inc(v_declName_2335_);
v___x_2353_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2335_, v___y_2341_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; uint8_t v___x_2355_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = lean_unbox(v_a_2354_);
lean_dec(v_a_2354_);
if (v___x_2355_ == 0)
{
if (v_nonRec_2336_ == 0)
{
lean_dec_ref(v___x_2337_);
lean_dec(v_declName_2335_);
goto v___jp_2343_;
}
else
{
lean_object* v___x_2356_; lean_object* v_env_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2356_ = lean_st_ref_get(v___y_2341_);
v_env_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc_ref(v_env_2357_);
lean_dec(v___x_2356_);
lean_inc(v_declName_2335_);
v___x_2358_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2357_, v_declName_2335_, v___x_2337_);
v___x_2359_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2335_, v___x_2358_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
return v___x_2359_;
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec_ref(v___x_2337_);
v___x_2360_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2361_ = lean_st_ref_get(v___x_2360_);
v___x_2362_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2363_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2335_, v___x_2361_, v___x_2362_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___x_2361_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2373_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2373_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2373_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_fst_2368_; 
v_fst_2368_ = lean_ctor_get(v_a_2364_, 0);
lean_inc(v_fst_2368_);
lean_dec(v_a_2364_);
if (lean_obj_tag(v_fst_2368_) == 0)
{
lean_del_object(v___x_2366_);
goto v___jp_2343_;
}
else
{
lean_object* v_val_2369_; lean_object* v___x_2371_; 
v_val_2369_ = lean_ctor_get(v_fst_2368_, 0);
lean_inc(v_val_2369_);
lean_dec_ref_known(v_fst_2368_, 1);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_val_2369_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_val_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
v_a_2374_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2363_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2363_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v___x_2337_);
lean_dec(v_declName_2335_);
v_a_2382_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2353_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2353_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v___x_2337_);
lean_dec(v_declName_2335_);
v_a_2390_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2350_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2350_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
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
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec_ref(v___x_2337_);
lean_dec(v_declName_2335_);
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2334_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
v___jp_2343_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2400_, lean_object* v_declName_2401_, lean_object* v_nonRec_2402_, lean_object* v___x_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v_nonRec_boxed_2409_; lean_object* v_res_2410_; 
v_nonRec_boxed_2409_ = lean_unbox(v_nonRec_2402_);
v_res_2410_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2400_, v_declName_2401_, v_nonRec_boxed_2409_, v___x_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_ref_2417_; lean_object* v___x_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2427_; 
v_ref_2417_ = lean_ctor_get(v___y_2414_, 2);
v___x_2418_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_inc(v_ref_2417_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_ref_2417_);
lean_ctor_set(v___x_2423_, 1, v_a_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set_tag(v___x_2421_, 1);
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2435_, uint8_t v_isExporting_2436_, lean_object* v___x_2437_, lean_object* v___y_2438_, lean_object* v___x_2439_, lean_object* v_a_x3f_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v_env_2443_; lean_object* v_nextMacroScope_2444_; lean_object* v_ngen_2445_; lean_object* v_auxDeclNGen_2446_; lean_object* v_traceState_2447_; lean_object* v_recordedDeps_2448_; lean_object* v_messages_2449_; lean_object* v_infoState_2450_; lean_object* v_snapshotTasks_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2476_; 
v___x_2442_ = lean_st_ref_take(v___y_2435_);
v_env_2443_ = lean_ctor_get(v___x_2442_, 0);
v_nextMacroScope_2444_ = lean_ctor_get(v___x_2442_, 1);
v_ngen_2445_ = lean_ctor_get(v___x_2442_, 2);
v_auxDeclNGen_2446_ = lean_ctor_get(v___x_2442_, 3);
v_traceState_2447_ = lean_ctor_get(v___x_2442_, 4);
v_recordedDeps_2448_ = lean_ctor_get(v___x_2442_, 6);
v_messages_2449_ = lean_ctor_get(v___x_2442_, 7);
v_infoState_2450_ = lean_ctor_get(v___x_2442_, 8);
v_snapshotTasks_2451_ = lean_ctor_get(v___x_2442_, 9);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2442_, 5);
lean_dec(v_unused_2477_);
v___x_2453_ = v___x_2442_;
v_isShared_2454_ = v_isSharedCheck_2476_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_snapshotTasks_2451_);
lean_inc(v_infoState_2450_);
lean_inc(v_messages_2449_);
lean_inc(v_recordedDeps_2448_);
lean_inc(v_traceState_2447_);
lean_inc(v_auxDeclNGen_2446_);
lean_inc(v_ngen_2445_);
lean_inc(v_nextMacroScope_2444_);
lean_inc(v_env_2443_);
lean_dec(v___x_2442_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2476_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = l_Lean_Environment_setExporting(v_env_2443_, v_isExporting_2436_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 5, v___x_2437_);
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_nextMacroScope_2444_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_ngen_2445_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_auxDeclNGen_2446_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_traceState_2447_);
lean_ctor_set(v_reuseFailAlloc_2475_, 5, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2475_, 6, v_recordedDeps_2448_);
lean_ctor_set(v_reuseFailAlloc_2475_, 7, v_messages_2449_);
lean_ctor_set(v_reuseFailAlloc_2475_, 8, v_infoState_2450_);
lean_ctor_set(v_reuseFailAlloc_2475_, 9, v_snapshotTasks_2451_);
v___x_2457_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_mctx_2460_; lean_object* v_zetaDeltaFVarIds_2461_; lean_object* v_postponed_2462_; lean_object* v_diag_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2473_; 
v___x_2458_ = lean_st_ref_put(v___y_2435_, v___x_2457_);
v___x_2459_ = lean_st_ref_take(v___y_2438_);
v_mctx_2460_ = lean_ctor_get(v___x_2459_, 0);
v_zetaDeltaFVarIds_2461_ = lean_ctor_get(v___x_2459_, 2);
v_postponed_2462_ = lean_ctor_get(v___x_2459_, 3);
v_diag_2463_ = lean_ctor_get(v___x_2459_, 4);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2459_, 1);
lean_dec(v_unused_2474_);
v___x_2465_ = v___x_2459_;
v_isShared_2466_ = v_isSharedCheck_2473_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_diag_2463_);
lean_inc(v_postponed_2462_);
lean_inc(v_zetaDeltaFVarIds_2461_);
lean_inc(v_mctx_2460_);
lean_dec(v___x_2459_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2473_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_box(0);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2439_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_mctx_2460_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_zetaDeltaFVarIds_2461_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_postponed_2462_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_diag_2463_);
v___x_2469_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_st_ref_put(v___y_2438_, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2467_);
return v___x_2471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2478_, lean_object* v_isExporting_2479_, lean_object* v___x_2480_, lean_object* v___y_2481_, lean_object* v___x_2482_, lean_object* v_a_x3f_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v_isExporting_boxed_2485_; lean_object* v_res_2486_; 
v_isExporting_boxed_2485_ = lean_unbox(v_isExporting_2479_);
v_res_2486_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2478_, v_isExporting_boxed_2485_, v___x_2480_, v___y_2481_, v___x_2482_, v_a_x3f_2483_);
lean_dec(v_a_x3f_2483_);
lean_dec(v___y_2481_);
lean_dec(v___y_2478_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2487_, uint8_t v_isExporting_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; lean_object* v_env_2495_; lean_object* v___x_2496_; uint8_t v_isModule_2497_; 
v___x_2494_ = lean_st_ref_get(v___y_2492_);
v_env_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc_ref(v_env_2495_);
lean_dec(v___x_2494_);
v___x_2496_ = l_Lean_Environment_header(v_env_2495_);
v_isModule_2497_ = lean_ctor_get_uint8(v___x_2496_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2496_);
if (v_isModule_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref(v_env_2495_);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
v___x_2498_ = lean_apply_5(v_x_2487_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, lean_box(0));
return v___x_2498_;
}
else
{
uint8_t v_isExporting_2499_; 
v_isExporting_2499_ = lean_ctor_get_uint8(v_env_2495_, sizeof(void*)*13);
lean_dec_ref(v_env_2495_);
if (v_isExporting_2488_ == 0)
{
if (v_isExporting_2499_ == 0)
{
lean_object* v___x_2566_; 
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
v___x_2566_ = lean_apply_5(v_x_2487_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, lean_box(0));
return v___x_2566_;
}
else
{
goto v___jp_2500_;
}
}
else
{
if (v_isExporting_2499_ == 0)
{
goto v___jp_2500_;
}
else
{
lean_object* v___x_2567_; 
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
v___x_2567_ = lean_apply_5(v_x_2487_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, lean_box(0));
return v___x_2567_;
}
}
v___jp_2500_:
{
lean_object* v___x_2501_; lean_object* v_env_2502_; lean_object* v_nextMacroScope_2503_; lean_object* v_ngen_2504_; lean_object* v_auxDeclNGen_2505_; lean_object* v_traceState_2506_; lean_object* v_recordedDeps_2507_; lean_object* v_messages_2508_; lean_object* v_infoState_2509_; lean_object* v_snapshotTasks_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2564_; 
v___x_2501_ = lean_st_ref_take(v___y_2492_);
v_env_2502_ = lean_ctor_get(v___x_2501_, 0);
v_nextMacroScope_2503_ = lean_ctor_get(v___x_2501_, 1);
v_ngen_2504_ = lean_ctor_get(v___x_2501_, 2);
v_auxDeclNGen_2505_ = lean_ctor_get(v___x_2501_, 3);
v_traceState_2506_ = lean_ctor_get(v___x_2501_, 4);
v_recordedDeps_2507_ = lean_ctor_get(v___x_2501_, 6);
v_messages_2508_ = lean_ctor_get(v___x_2501_, 7);
v_infoState_2509_ = lean_ctor_get(v___x_2501_, 8);
v_snapshotTasks_2510_ = lean_ctor_get(v___x_2501_, 9);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2501_, 5);
lean_dec(v_unused_2565_);
v___x_2512_ = v___x_2501_;
v_isShared_2513_ = v_isSharedCheck_2564_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_snapshotTasks_2510_);
lean_inc(v_infoState_2509_);
lean_inc(v_messages_2508_);
lean_inc(v_recordedDeps_2507_);
lean_inc(v_traceState_2506_);
lean_inc(v_auxDeclNGen_2505_);
lean_inc(v_ngen_2504_);
lean_inc(v_nextMacroScope_2503_);
lean_inc(v_env_2502_);
lean_dec(v___x_2501_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2564_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2514_ = l_Lean_Environment_setExporting(v_env_2502_, v_isExporting_2488_);
v___x_2515_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 5, v___x_2515_);
lean_ctor_set(v___x_2512_, 0, v___x_2514_);
v___x_2517_ = v___x_2512_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_nextMacroScope_2503_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_ngen_2504_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_auxDeclNGen_2505_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_traceState_2506_);
lean_ctor_set(v_reuseFailAlloc_2563_, 5, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_recordedDeps_2507_);
lean_ctor_set(v_reuseFailAlloc_2563_, 7, v_messages_2508_);
lean_ctor_set(v_reuseFailAlloc_2563_, 8, v_infoState_2509_);
lean_ctor_set(v_reuseFailAlloc_2563_, 9, v_snapshotTasks_2510_);
v___x_2517_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v_mctx_2520_; lean_object* v_zetaDeltaFVarIds_2521_; lean_object* v_postponed_2522_; lean_object* v_diag_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2561_; 
v___x_2518_ = lean_st_ref_put(v___y_2492_, v___x_2517_);
v___x_2519_ = lean_st_ref_take(v___y_2490_);
v_mctx_2520_ = lean_ctor_get(v___x_2519_, 0);
v_zetaDeltaFVarIds_2521_ = lean_ctor_get(v___x_2519_, 2);
v_postponed_2522_ = lean_ctor_get(v___x_2519_, 3);
v_diag_2523_ = lean_ctor_get(v___x_2519_, 4);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v___x_2519_, 1);
lean_dec(v_unused_2562_);
v___x_2525_ = v___x_2519_;
v_isShared_2526_ = v_isSharedCheck_2561_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_diag_2523_);
lean_inc(v_postponed_2522_);
lean_inc(v_zetaDeltaFVarIds_2521_);
lean_inc(v_mctx_2520_);
lean_dec(v___x_2519_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2561_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v___x_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_mctx_2520_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_zetaDeltaFVarIds_2521_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v_postponed_2522_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v_diag_2523_);
v___x_2529_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; lean_object* v_r_2531_; 
v___x_2530_ = lean_st_ref_put(v___y_2490_, v___x_2529_);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
v_r_2531_ = lean_apply_5(v_x_2487_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, lean_box(0));
if (lean_obj_tag(v_r_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2548_; 
v_a_2532_ = lean_ctor_get(v_r_2531_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_r_2531_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2534_ = v_r_2531_;
v_isShared_2535_ = v_isSharedCheck_2548_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v_r_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2548_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
lean_inc(v_a_2532_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 1);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v___x_2538_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2492_, v_isExporting_2499_, v___x_2515_, v___y_2490_, v___x_2527_, v___x_2537_);
lean_dec_ref(v___x_2537_);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; 
v_unused_2546_ = lean_ctor_get(v___x_2538_, 0);
lean_dec(v_unused_2546_);
v___x_2540_ = v___x_2538_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_dec(v___x_2538_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v_a_2532_);
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2532_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2549_ = lean_ctor_get(v_r_2531_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v_r_2531_, 1);
v___x_2550_ = lean_box(0);
v___x_2551_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2492_, v_isExporting_2499_, v___x_2515_, v___y_2490_, v___x_2527_, v___x_2550_);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v___x_2551_, 0);
lean_dec(v_unused_2559_);
v___x_2553_ = v___x_2551_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_dec(v___x_2551_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set_tag(v___x_2553_, 1);
lean_ctor_set(v___x_2553_, 0, v_a_2549_);
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2549_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2568_, lean_object* v_isExporting_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
uint8_t v_isExporting_boxed_2575_; lean_object* v_res_2576_; 
v_isExporting_boxed_2575_ = lean_unbox(v_isExporting_2569_);
v_res_2576_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2568_, v_isExporting_boxed_2575_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2577_, uint8_t v_when_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
if (v_when_2578_ == 0)
{
lean_object* v___x_2584_; 
lean_inc(v___y_2582_);
lean_inc_ref(v___y_2581_);
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
v___x_2584_ = lean_apply_5(v_x_2577_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, lean_box(0));
return v___x_2584_;
}
else
{
uint8_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = 0;
v___x_2586_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2577_, v___x_2585_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2587_, lean_object* v_when_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
uint8_t v_when_boxed_2594_; lean_object* v_res_2595_; 
v_when_boxed_2594_ = lean_unbox(v_when_2588_);
v_res_2595_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2587_, v_when_boxed_2594_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2595_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2598_ = l_Lean_stringToMessageData(v___x_2597_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2601_ = l_Lean_stringToMessageData(v___x_2600_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2603_ = l_Lean_stringToMessageData(v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2604_, uint8_t v_nonRec_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; lean_object* v_env_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___f_2616_; uint8_t v___x_2617_; lean_object* v___x_2618_; 
v___x_2611_ = lean_st_ref_get(v___y_2609_);
v_env_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc_ref(v_env_2612_);
lean_dec(v___x_2611_);
v___x_2613_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2604_);
v___x_2614_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2612_, v_declName_2604_, v___x_2613_);
v___x_2615_ = lean_box(v_nonRec_2605_);
lean_inc(v___x_2614_);
v___f_2616_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2616_, 0, v___x_2614_);
lean_closure_set(v___f_2616_, 1, v_declName_2604_);
lean_closure_set(v___f_2616_, 2, v___x_2615_);
lean_closure_set(v___f_2616_, 3, v___x_2613_);
v___x_2617_ = 1;
v___x_2618_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2616_, v___x_2617_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
if (lean_obj_tag(v_a_2619_) == 1)
{
lean_object* v_val_2620_; uint8_t v___x_2621_; 
v_val_2620_ = lean_ctor_get(v_a_2619_, 0);
v___x_2621_ = lean_name_eq(v_val_2620_, v___x_2614_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_inc(v_val_2620_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2622_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2623_ = l_Lean_MessageData_ofName(v_val_2620_);
v___x_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2624_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = l_Lean_MessageData_ofName(v___x_2614_);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2630_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
else
{
lean_dec(v___x_2614_);
return v___x_2618_;
}
}
else
{
lean_dec(v___x_2614_);
return v___x_2618_;
}
}
else
{
lean_dec(v___x_2614_);
return v___x_2618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2640_, lean_object* v_nonRec_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
uint8_t v_nonRec_boxed_2647_; lean_object* v_res_2648_; 
v_nonRec_boxed_2647_ = lean_unbox(v_nonRec_2641_);
v_res_2648_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2640_, v_nonRec_boxed_2647_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2649_, uint8_t v_nonRec_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2656_ = lean_box(v_nonRec_2650_);
v___f_2657_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2657_, 0, v_declName_2649_);
lean_closure_set(v___f_2657_, 1, v___x_2656_);
v___x_2658_ = lean_unsigned_to_nat(32u);
v___x_2659_ = lean_mk_empty_array_with_capacity(v___x_2658_);
lean_dec_ref(v___x_2659_);
v___x_2660_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2661_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2662_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2660_, v___x_2661_, v___f_2657_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2663_, lean_object* v_nonRec_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
uint8_t v_nonRec_boxed_2670_; lean_object* v_res_2671_; 
v_nonRec_boxed_2670_ = lean_unbox(v_nonRec_2664_);
v_res_2671_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2663_, v_nonRec_boxed_2670_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2672_, lean_object* v_as_2673_, lean_object* v_as_x27_2674_, lean_object* v_b_2675_, lean_object* v_a_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2672_, v_as_x27_2674_, v_b_2675_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2683_, lean_object* v_as_2684_, lean_object* v_as_x27_2685_, lean_object* v_b_2686_, lean_object* v_a_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2683_, v_as_2684_, v_as_x27_2685_, v_b_2686_, v_a_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v_as_x27_2685_);
lean_dec(v_as_2684_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2694_, lean_object* v_x_2695_, uint8_t v_isExporting_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2695_, v_isExporting_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_x_2704_, lean_object* v_isExporting_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
uint8_t v_isExporting_boxed_2711_; lean_object* v_res_2712_; 
v_isExporting_boxed_2711_ = lean_unbox(v_isExporting_2705_);
v_res_2712_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2703_, v_x_2704_, v_isExporting_boxed_2711_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2713_, lean_object* v_x_2714_, uint8_t v_when_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2714_, v_when_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_x_2723_, lean_object* v_when_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
uint8_t v_when_boxed_2730_; lean_object* v_res_2731_; 
v_when_boxed_2730_ = lean_unbox(v_when_2724_);
v_res_2731_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2722_, v_x_2723_, v_when_boxed_2730_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2732_, lean_object* v_msg_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2740_, lean_object* v_msg_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2740_, v_msg_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = lean_unsigned_to_nat(32u);
v___x_2749_ = lean_mk_empty_array_with_capacity(v___x_2748_);
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2751_ = ((size_t)5ULL);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_unsigned_to_nat(32u);
v___x_2754_ = lean_mk_empty_array_with_capacity(v___x_2753_);
v___x_2755_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2756_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___x_2754_);
lean_ctor_set(v___x_2756_, 2, v___x_2752_);
lean_ctor_set(v___x_2756_, 3, v___x_2752_);
lean_ctor_set_usize(v___x_2756_, 4, v___x_2751_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; lean_object* v_traceState_2760_; lean_object* v_traces_2761_; lean_object* v___x_2762_; lean_object* v_traceState_2763_; lean_object* v_env_2764_; lean_object* v_nextMacroScope_2765_; lean_object* v_ngen_2766_; lean_object* v_auxDeclNGen_2767_; lean_object* v_cache_2768_; lean_object* v_recordedDeps_2769_; lean_object* v_messages_2770_; lean_object* v_infoState_2771_; lean_object* v_snapshotTasks_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2791_; 
v___x_2759_ = lean_st_ref_get(v___y_2757_);
v_traceState_2760_ = lean_ctor_get(v___x_2759_, 4);
lean_inc_ref(v_traceState_2760_);
lean_dec(v___x_2759_);
v_traces_2761_ = lean_ctor_get(v_traceState_2760_, 0);
lean_inc_ref(v_traces_2761_);
lean_dec_ref(v_traceState_2760_);
v___x_2762_ = lean_st_ref_take(v___y_2757_);
v_traceState_2763_ = lean_ctor_get(v___x_2762_, 4);
v_env_2764_ = lean_ctor_get(v___x_2762_, 0);
v_nextMacroScope_2765_ = lean_ctor_get(v___x_2762_, 1);
v_ngen_2766_ = lean_ctor_get(v___x_2762_, 2);
v_auxDeclNGen_2767_ = lean_ctor_get(v___x_2762_, 3);
v_cache_2768_ = lean_ctor_get(v___x_2762_, 5);
v_recordedDeps_2769_ = lean_ctor_get(v___x_2762_, 6);
v_messages_2770_ = lean_ctor_get(v___x_2762_, 7);
v_infoState_2771_ = lean_ctor_get(v___x_2762_, 8);
v_snapshotTasks_2772_ = lean_ctor_get(v___x_2762_, 9);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2774_ = v___x_2762_;
v_isShared_2775_ = v_isSharedCheck_2791_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_snapshotTasks_2772_);
lean_inc(v_infoState_2771_);
lean_inc(v_messages_2770_);
lean_inc(v_recordedDeps_2769_);
lean_inc(v_cache_2768_);
lean_inc(v_traceState_2763_);
lean_inc(v_auxDeclNGen_2767_);
lean_inc(v_ngen_2766_);
lean_inc(v_nextMacroScope_2765_);
lean_inc(v_env_2764_);
lean_dec(v___x_2762_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2791_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint64_t v_tid_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2789_; 
v_tid_2776_ = lean_ctor_get_uint64(v_traceState_2763_, sizeof(void*)*1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_traceState_2763_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v_traceState_2763_, 0);
lean_dec(v_unused_2790_);
v___x_2778_ = v_traceState_2763_;
v_isShared_2779_ = v_isSharedCheck_2789_;
goto v_resetjp_2777_;
}
else
{
lean_dec(v_traceState_2763_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2789_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2780_);
v___x_2782_ = v___x_2778_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2780_);
lean_ctor_set_uint64(v_reuseFailAlloc_2788_, sizeof(void*)*1, v_tid_2776_);
v___x_2782_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2784_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 4, v___x_2782_);
v___x_2784_ = v___x_2774_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_env_2764_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_nextMacroScope_2765_);
lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_ngen_2766_);
lean_ctor_set(v_reuseFailAlloc_2787_, 3, v_auxDeclNGen_2767_);
lean_ctor_set(v_reuseFailAlloc_2787_, 4, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2787_, 5, v_cache_2768_);
lean_ctor_set(v_reuseFailAlloc_2787_, 6, v_recordedDeps_2769_);
lean_ctor_set(v_reuseFailAlloc_2787_, 7, v_messages_2770_);
lean_ctor_set(v_reuseFailAlloc_2787_, 8, v_infoState_2771_);
lean_ctor_set(v_reuseFailAlloc_2787_, 9, v_snapshotTasks_2772_);
v___x_2784_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_st_ref_put(v___y_2757_, v___x_2784_);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v_traces_2761_);
return v___x_2786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2792_);
lean_dec(v___y_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = 0;
v___x_2808_ = lean_box(v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2814_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2817_ = l_Lean_stringToMessageData(v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2818_, lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2823_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2824_ = l_Lean_MessageData_ofName(v_name_2818_);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2827_, lean_object* v_x_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2827_, v_x_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v_x_2828_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2833_){
_start:
{
if (lean_obj_tag(v_x_2833_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
v_a_2835_ = lean_ctor_get(v_x_2833_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_x_2833_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v_x_2833_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v_x_2833_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set_tag(v___x_2837_, 1);
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v_x_2833_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_x_2833_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v_x_2833_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v_x_2833_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 0);
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2854_){
_start:
{
if (lean_obj_tag(v_e_2854_) == 0)
{
uint8_t v___x_2855_; 
v___x_2855_ = 2;
return v___x_2855_;
}
else
{
lean_object* v_a_2856_; uint8_t v___x_2857_; 
v_a_2856_ = lean_ctor_get(v_e_2854_, 0);
v___x_2857_ = lean_unbox(v_a_2856_);
if (v___x_2857_ == 0)
{
uint8_t v___x_2858_; 
v___x_2858_ = 1;
return v___x_2858_;
}
else
{
uint8_t v___x_2859_; 
v___x_2859_ = 0;
return v___x_2859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2860_){
_start:
{
uint8_t v_res_2861_; lean_object* v_r_2862_; 
v_res_2861_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2860_);
lean_dec_ref(v_e_2860_);
v_r_2862_ = lean_box(v_res_2861_);
return v_r_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2863_, size_t v_i_2864_, lean_object* v_bs_2865_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_usize_dec_lt(v_i_2864_, v_sz_2863_);
if (v___x_2866_ == 0)
{
return v_bs_2865_;
}
else
{
lean_object* v_v_2867_; lean_object* v_msg_2868_; lean_object* v___x_2869_; lean_object* v_bs_x27_2870_; size_t v___x_2871_; size_t v___x_2872_; lean_object* v___x_2873_; 
v_v_2867_ = lean_array_uget_borrowed(v_bs_2865_, v_i_2864_);
v_msg_2868_ = lean_ctor_get(v_v_2867_, 1);
lean_inc_ref(v_msg_2868_);
v___x_2869_ = lean_unsigned_to_nat(0u);
v_bs_x27_2870_ = lean_array_uset(v_bs_2865_, v_i_2864_, v___x_2869_);
v___x_2871_ = ((size_t)1ULL);
v___x_2872_ = lean_usize_add(v_i_2864_, v___x_2871_);
v___x_2873_ = lean_array_uset(v_bs_x27_2870_, v_i_2864_, v_msg_2868_);
v_i_2864_ = v___x_2872_;
v_bs_2865_ = v___x_2873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2875_, lean_object* v_i_2876_, lean_object* v_bs_2877_){
_start:
{
size_t v_sz_boxed_2878_; size_t v_i_boxed_2879_; lean_object* v_res_2880_; 
v_sz_boxed_2878_ = lean_unbox_usize(v_sz_2875_);
lean_dec(v_sz_2875_);
v_i_boxed_2879_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2878_, v_i_boxed_2879_, v_bs_2877_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2881_, lean_object* v_data_2882_, lean_object* v_ref_2883_, lean_object* v_msg_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_toCold_2888_; lean_object* v_currRecDepth_2889_; lean_object* v_ref_2890_; uint16_t v_optionFlags_2891_; uint8_t v_suppressElabErrors_2892_; uint8_t v_isRecordingDeps_2893_; lean_object* v_ref_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_traceState_2897_; lean_object* v_traces_2898_; lean_object* v___x_2899_; size_t v_sz_2900_; size_t v___x_2901_; lean_object* v___x_2902_; lean_object* v_msg_2903_; lean_object* v___x_2904_; lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2943_; 
v_toCold_2888_ = lean_ctor_get(v___y_2885_, 0);
v_currRecDepth_2889_ = lean_ctor_get(v___y_2885_, 1);
v_ref_2890_ = lean_ctor_get(v___y_2885_, 2);
v_optionFlags_2891_ = lean_ctor_get_uint16(v___y_2885_, sizeof(void*)*3);
v_suppressElabErrors_2892_ = lean_ctor_get_uint8(v___y_2885_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2893_ = lean_ctor_get_uint8(v___y_2885_, sizeof(void*)*3 + 3);
v_ref_2894_ = l_Lean_replaceRef(v_ref_2883_, v_ref_2890_);
lean_inc(v_currRecDepth_2889_);
lean_inc_ref(v_toCold_2888_);
v___x_2895_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2895_, 0, v_toCold_2888_);
lean_ctor_set(v___x_2895_, 1, v_currRecDepth_2889_);
lean_ctor_set(v___x_2895_, 2, v_ref_2894_);
lean_ctor_set_uint16(v___x_2895_, sizeof(void*)*3, v_optionFlags_2891_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*3 + 2, v_suppressElabErrors_2892_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*3 + 3, v_isRecordingDeps_2893_);
v___x_2896_ = lean_st_ref_get(v___y_2886_);
v_traceState_2897_ = lean_ctor_get(v___x_2896_, 4);
lean_inc_ref(v_traceState_2897_);
lean_dec(v___x_2896_);
v_traces_2898_ = lean_ctor_get(v_traceState_2897_, 0);
lean_inc_ref(v_traces_2898_);
lean_dec_ref(v_traceState_2897_);
v___x_2899_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2898_);
lean_dec_ref(v_traces_2898_);
v_sz_2900_ = lean_array_size(v___x_2899_);
v___x_2901_ = ((size_t)0ULL);
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2900_, v___x_2901_, v___x_2899_);
v_msg_2903_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2903_, 0, v_data_2882_);
lean_ctor_set(v_msg_2903_, 1, v_msg_2884_);
lean_ctor_set(v_msg_2903_, 2, v___x_2902_);
v___x_2904_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2903_, v___x_2895_, v___y_2886_);
lean_dec_ref_known(v___x_2895_, 3);
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2943_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2943_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v_traceState_2910_; lean_object* v_env_2911_; lean_object* v_nextMacroScope_2912_; lean_object* v_ngen_2913_; lean_object* v_auxDeclNGen_2914_; lean_object* v_cache_2915_; lean_object* v_recordedDeps_2916_; lean_object* v_messages_2917_; lean_object* v_infoState_2918_; lean_object* v_snapshotTasks_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2942_; 
v___x_2909_ = lean_st_ref_take(v___y_2886_);
v_traceState_2910_ = lean_ctor_get(v___x_2909_, 4);
v_env_2911_ = lean_ctor_get(v___x_2909_, 0);
v_nextMacroScope_2912_ = lean_ctor_get(v___x_2909_, 1);
v_ngen_2913_ = lean_ctor_get(v___x_2909_, 2);
v_auxDeclNGen_2914_ = lean_ctor_get(v___x_2909_, 3);
v_cache_2915_ = lean_ctor_get(v___x_2909_, 5);
v_recordedDeps_2916_ = lean_ctor_get(v___x_2909_, 6);
v_messages_2917_ = lean_ctor_get(v___x_2909_, 7);
v_infoState_2918_ = lean_ctor_get(v___x_2909_, 8);
v_snapshotTasks_2919_ = lean_ctor_get(v___x_2909_, 9);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2921_ = v___x_2909_;
v_isShared_2922_ = v_isSharedCheck_2942_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_snapshotTasks_2919_);
lean_inc(v_infoState_2918_);
lean_inc(v_messages_2917_);
lean_inc(v_recordedDeps_2916_);
lean_inc(v_cache_2915_);
lean_inc(v_traceState_2910_);
lean_inc(v_auxDeclNGen_2914_);
lean_inc(v_ngen_2913_);
lean_inc(v_nextMacroScope_2912_);
lean_inc(v_env_2911_);
lean_dec(v___x_2909_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2942_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
uint64_t v_tid_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2940_; 
v_tid_2923_ = lean_ctor_get_uint64(v_traceState_2910_, sizeof(void*)*1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_traceState_2910_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v_traceState_2910_, 0);
lean_dec(v_unused_2941_);
v___x_2925_ = v_traceState_2910_;
v_isShared_2926_ = v_isSharedCheck_2940_;
goto v_resetjp_2924_;
}
else
{
lean_dec(v_traceState_2910_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2940_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v_ref_2883_);
lean_ctor_set(v___x_2928_, 1, v_a_2905_);
v___x_2929_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2881_, v___x_2928_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2929_);
v___x_2931_ = v___x_2925_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2929_);
lean_ctor_set_uint64(v_reuseFailAlloc_2939_, sizeof(void*)*1, v_tid_2923_);
v___x_2931_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
lean_object* v___x_2933_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 4, v___x_2931_);
v___x_2933_ = v___x_2921_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_env_2911_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_nextMacroScope_2912_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_ngen_2913_);
lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_auxDeclNGen_2914_);
lean_ctor_set(v_reuseFailAlloc_2938_, 4, v___x_2931_);
lean_ctor_set(v_reuseFailAlloc_2938_, 5, v_cache_2915_);
lean_ctor_set(v_reuseFailAlloc_2938_, 6, v_recordedDeps_2916_);
lean_ctor_set(v_reuseFailAlloc_2938_, 7, v_messages_2917_);
lean_ctor_set(v_reuseFailAlloc_2938_, 8, v_infoState_2918_);
lean_ctor_set(v_reuseFailAlloc_2938_, 9, v_snapshotTasks_2919_);
v___x_2933_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2934_ = lean_st_ref_put(v___y_2886_, v___x_2933_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2927_);
v___x_2936_ = v___x_2907_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2927_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2944_, lean_object* v_data_2945_, lean_object* v_ref_2946_, lean_object* v_msg_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2944_, v_data_2945_, v_ref_2946_, v_msg_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2951_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2955_; double v___x_2956_; 
v___x_2955_ = lean_unsigned_to_nat(1000u);
v___x_2956_ = lean_float_of_nat(v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2957_, uint8_t v_collapsed_2958_, lean_object* v_tag_2959_, lean_object* v_opts_2960_, uint8_t v_clsEnabled_2961_, lean_object* v_oldTraces_2962_, lean_object* v_msg_2963_, lean_object* v_resStartStop_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_fst_2968_; lean_object* v_snd_2969_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v_data_2973_; lean_object* v_fst_2984_; lean_object* v_snd_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; lean_object* v___y_2989_; lean_object* v_a_2990_; uint8_t v___y_3005_; double v___y_3037_; 
v_fst_2968_ = lean_ctor_get(v_resStartStop_2964_, 0);
lean_inc(v_fst_2968_);
v_snd_2969_ = lean_ctor_get(v_resStartStop_2964_, 1);
lean_inc(v_snd_2969_);
lean_dec_ref(v_resStartStop_2964_);
v_fst_2984_ = lean_ctor_get(v_snd_2969_, 0);
lean_inc(v_fst_2984_);
v_snd_2985_ = lean_ctor_get(v_snd_2969_, 1);
lean_inc(v_snd_2985_);
lean_dec(v_snd_2969_);
v___x_2986_ = l_Lean_trace_profiler;
v___x_2987_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2960_, v___x_2986_);
if (v___x_2987_ == 0)
{
v___y_3005_ = v___x_2987_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3043_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2960_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; double v___x_3046_; double v___x_3047_; double v___x_3048_; 
v___x_3044_ = l_Lean_trace_profiler_threshold;
v___x_3045_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2960_, v___x_3044_);
v___x_3046_ = lean_float_of_nat(v___x_3045_);
v___x_3047_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3048_ = lean_float_div(v___x_3046_, v___x_3047_);
v___y_3037_ = v___x_3048_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; double v___x_3051_; 
v___x_3049_ = l_Lean_trace_profiler_threshold;
v___x_3050_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2960_, v___x_3049_);
v___x_3051_ = lean_float_of_nat(v___x_3050_);
v___y_3037_ = v___x_3051_;
goto v___jp_3036_;
}
}
v___jp_2970_:
{
lean_object* v___x_2974_; 
lean_inc(v___y_2971_);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2962_, v_data_2973_, v___y_2971_, v___y_2972_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v___x_2975_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2968_);
return v___x_2975_;
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_fst_2968_);
v_a_2976_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2974_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
v___jp_2988_:
{
uint8_t v_result_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; double v___x_2994_; lean_object* v_data_2995_; 
v_result_2991_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2968_);
v___x_2992_ = lean_box(v_result_2991_);
v___x_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
v___x_2994_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_2959_);
lean_inc_ref(v___x_2993_);
lean_inc(v_cls_2957_);
v_data_2995_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2995_, 0, v_cls_2957_);
lean_ctor_set(v_data_2995_, 1, v___x_2993_);
lean_ctor_set(v_data_2995_, 2, v_tag_2959_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3, v___x_2994_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3 + 8, v___x_2994_);
lean_ctor_set_uint8(v_data_2995_, sizeof(void*)*3 + 16, v_collapsed_2958_);
if (v___x_2987_ == 0)
{
lean_dec_ref_known(v___x_2993_, 1);
lean_dec(v_snd_2985_);
lean_dec(v_fst_2984_);
lean_dec_ref(v_tag_2959_);
lean_dec(v_cls_2957_);
v___y_2971_ = v___y_2989_;
v___y_2972_ = v_a_2990_;
v_data_2973_ = v_data_2995_;
goto v___jp_2970_;
}
else
{
lean_object* v_data_2996_; double v___x_2997_; double v___x_2998_; 
lean_dec_ref_known(v_data_2995_, 3);
v_data_2996_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2996_, 0, v_cls_2957_);
lean_ctor_set(v_data_2996_, 1, v___x_2993_);
lean_ctor_set(v_data_2996_, 2, v_tag_2959_);
v___x_2997_ = lean_unbox_float(v_fst_2984_);
lean_dec(v_fst_2984_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3, v___x_2997_);
v___x_2998_ = lean_unbox_float(v_snd_2985_);
lean_dec(v_snd_2985_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3 + 8, v___x_2998_);
lean_ctor_set_uint8(v_data_2996_, sizeof(void*)*3 + 16, v_collapsed_2958_);
v___y_2971_ = v___y_2989_;
v___y_2972_ = v_a_2990_;
v_data_2973_ = v_data_2996_;
goto v___jp_2970_;
}
}
v___jp_2999_:
{
lean_object* v_ref_3000_; lean_object* v___x_3001_; 
v_ref_3000_ = lean_ctor_get(v___y_2965_, 2);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v_fst_2968_);
v___x_3001_ = lean_apply_4(v_msg_2963_, v_fst_2968_, v___y_2965_, v___y_2966_, lean_box(0));
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___y_2989_ = v_ref_3000_;
v_a_2990_ = v_a_3002_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3003_; 
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2989_ = v_ref_3000_;
v_a_2990_ = v___x_3003_;
goto v___jp_2988_;
}
}
v___jp_3004_:
{
if (v_clsEnabled_2961_ == 0)
{
if (v___y_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v_traceState_3007_; lean_object* v_env_3008_; lean_object* v_nextMacroScope_3009_; lean_object* v_ngen_3010_; lean_object* v_auxDeclNGen_3011_; lean_object* v_cache_3012_; lean_object* v_recordedDeps_3013_; lean_object* v_messages_3014_; lean_object* v_infoState_3015_; lean_object* v_snapshotTasks_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_snd_2985_);
lean_dec(v_fst_2984_);
lean_dec_ref(v_msg_2963_);
lean_dec_ref(v_tag_2959_);
lean_dec(v_cls_2957_);
v___x_3006_ = lean_st_ref_take(v___y_2966_);
v_traceState_3007_ = lean_ctor_get(v___x_3006_, 4);
v_env_3008_ = lean_ctor_get(v___x_3006_, 0);
v_nextMacroScope_3009_ = lean_ctor_get(v___x_3006_, 1);
v_ngen_3010_ = lean_ctor_get(v___x_3006_, 2);
v_auxDeclNGen_3011_ = lean_ctor_get(v___x_3006_, 3);
v_cache_3012_ = lean_ctor_get(v___x_3006_, 5);
v_recordedDeps_3013_ = lean_ctor_get(v___x_3006_, 6);
v_messages_3014_ = lean_ctor_get(v___x_3006_, 7);
v_infoState_3015_ = lean_ctor_get(v___x_3006_, 8);
v_snapshotTasks_3016_ = lean_ctor_get(v___x_3006_, 9);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3018_ = v___x_3006_;
v_isShared_3019_ = v_isSharedCheck_3035_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_snapshotTasks_3016_);
lean_inc(v_infoState_3015_);
lean_inc(v_messages_3014_);
lean_inc(v_recordedDeps_3013_);
lean_inc(v_cache_3012_);
lean_inc(v_traceState_3007_);
lean_inc(v_auxDeclNGen_3011_);
lean_inc(v_ngen_3010_);
lean_inc(v_nextMacroScope_3009_);
lean_inc(v_env_3008_);
lean_dec(v___x_3006_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3035_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
uint64_t v_tid_3020_; lean_object* v_traces_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3034_; 
v_tid_3020_ = lean_ctor_get_uint64(v_traceState_3007_, sizeof(void*)*1);
v_traces_3021_ = lean_ctor_get(v_traceState_3007_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_traceState_3007_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3023_ = v_traceState_3007_;
v_isShared_3024_ = v_isSharedCheck_3034_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_traces_3021_);
lean_dec(v_traceState_3007_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3034_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___x_3025_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2962_, v_traces_3021_);
lean_dec_ref(v_traces_3021_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3025_);
v___x_3027_ = v___x_3023_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3025_);
lean_ctor_set_uint64(v_reuseFailAlloc_3033_, sizeof(void*)*1, v_tid_3020_);
v___x_3027_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3029_; 
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 4, v___x_3027_);
v___x_3029_ = v___x_3018_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_env_3008_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_nextMacroScope_3009_);
lean_ctor_set(v_reuseFailAlloc_3032_, 2, v_ngen_3010_);
lean_ctor_set(v_reuseFailAlloc_3032_, 3, v_auxDeclNGen_3011_);
lean_ctor_set(v_reuseFailAlloc_3032_, 4, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3032_, 5, v_cache_3012_);
lean_ctor_set(v_reuseFailAlloc_3032_, 6, v_recordedDeps_3013_);
lean_ctor_set(v_reuseFailAlloc_3032_, 7, v_messages_3014_);
lean_ctor_set(v_reuseFailAlloc_3032_, 8, v_infoState_3015_);
lean_ctor_set(v_reuseFailAlloc_3032_, 9, v_snapshotTasks_3016_);
v___x_3029_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = lean_st_ref_put(v___y_2966_, v___x_3029_);
v___x_3031_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2968_);
return v___x_3031_;
}
}
}
}
}
else
{
goto v___jp_2999_;
}
}
else
{
goto v___jp_2999_;
}
}
v___jp_3036_:
{
double v___x_3038_; double v___x_3039_; double v___x_3040_; uint8_t v___x_3041_; 
v___x_3038_ = lean_unbox_float(v_snd_2985_);
v___x_3039_ = lean_unbox_float(v_fst_2984_);
v___x_3040_ = lean_float_sub(v___x_3038_, v___x_3039_);
v___x_3041_ = lean_float_decLt(v___y_3037_, v___x_3040_);
v___y_3005_ = v___x_3041_;
goto v___jp_3004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3052_, lean_object* v_collapsed_3053_, lean_object* v_tag_3054_, lean_object* v_opts_3055_, lean_object* v_clsEnabled_3056_, lean_object* v_oldTraces_3057_, lean_object* v_msg_3058_, lean_object* v_resStartStop_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v_collapsed_boxed_3063_; uint8_t v_clsEnabled_boxed_3064_; lean_object* v_res_3065_; 
v_collapsed_boxed_3063_ = lean_unbox(v_collapsed_3053_);
v_clsEnabled_boxed_3064_ = lean_unbox(v_clsEnabled_3056_);
v_res_3065_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3052_, v_collapsed_boxed_3063_, v_tag_3054_, v_opts_3055_, v_clsEnabled_boxed_3064_, v_oldTraces_3057_, v_msg_3058_, v_resStartStop_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v_opts_3055_);
return v_res_3065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3068_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3069_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3070_ = lean_unsigned_to_nat(0u);
v___x_3071_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
lean_ctor_set(v___x_3071_, 3, v___x_3070_);
lean_ctor_set(v___x_3071_, 4, v___x_3069_);
lean_ctor_set(v___x_3071_, 5, v___x_3069_);
lean_ctor_set(v___x_3071_, 6, v___x_3069_);
lean_ctor_set(v___x_3071_, 7, v___x_3069_);
lean_ctor_set(v___x_3071_, 8, v___x_3069_);
lean_ctor_set(v___x_3071_, 9, v___x_3069_);
lean_ctor_set(v___x_3071_, 10, v___x_3069_);
lean_ctor_set(v___x_3071_, 11, v___x_3068_);
return v___x_3071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3073_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
lean_ctor_set(v___x_3073_, 2, v___x_3072_);
lean_ctor_set(v___x_3073_, 3, v___x_3072_);
lean_ctor_set(v___x_3073_, 4, v___x_3072_);
lean_ctor_set(v___x_3073_, 5, v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
lean_ctor_set(v___x_3075_, 2, v___x_3074_);
lean_ctor_set(v___x_3075_, 3, v___x_3074_);
lean_ctor_set(v___x_3075_, 4, v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3081_ = l_Lean_Name_append(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3082_; double v___x_3083_; 
v___x_3082_ = lean_unsigned_to_nat(1000000000u);
v___x_3083_ = lean_float_of_nat(v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3084_, lean_object* v___f_3085_, lean_object* v_name_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_toCold_3090_; lean_object* v_options_3091_; uint8_t v_hasTrace_3092_; 
v_toCold_3090_ = lean_ctor_get(v___y_3087_, 0);
v_options_3091_ = lean_ctor_get(v_toCold_3090_, 2);
v_hasTrace_3092_ = lean_ctor_get_uint8(v_options_3091_, sizeof(void*)*1);
if (v_hasTrace_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v_env_3094_; lean_object* v___x_3095_; 
lean_dec_ref(v___f_3085_);
v___x_3093_ = lean_st_ref_get(v___y_3088_);
v_env_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc_ref(v_env_3094_);
lean_dec(v___x_3093_);
lean_inc(v_name_3086_);
v___x_3095_ = l_Lean_Meta_declFromEqLikeName(v_env_3094_, v_name_3086_);
if (lean_obj_tag(v___x_3095_) == 1)
{
lean_object* v_val_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3201_; 
v_val_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3201_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_val_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3201_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_fst_3100_; lean_object* v_snd_3101_; lean_object* v___x_3102_; lean_object* v_env_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v_fst_3100_ = lean_ctor_get(v_val_3096_, 0);
lean_inc_n(v_fst_3100_, 2);
v_snd_3101_ = lean_ctor_get(v_val_3096_, 1);
lean_inc_n(v_snd_3101_, 2);
lean_dec(v_val_3096_);
v___x_3102_ = lean_st_ref_get(v___y_3088_);
v_env_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc_ref(v_env_3103_);
lean_dec(v___x_3102_);
v___x_3104_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3103_, v_fst_3100_, v_snd_3101_);
v___x_3105_ = lean_name_eq(v_name_3086_, v___x_3104_);
lean_dec(v___x_3104_);
lean_dec(v_name_3086_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
lean_dec(v_snd_3101_);
lean_dec(v_fst_3100_);
lean_dec(v___x_3084_);
v___x_3106_ = lean_box(v_hasTrace_3092_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set_tag(v___x_3098_, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3106_);
v___x_3108_ = v___x_3098_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
else
{
uint8_t v___x_3110_; lean_object* v_a_3112_; 
lean_inc(v_snd_3101_);
v___x_3110_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3101_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v_a_3129_; 
lean_del_object(v___x_3098_);
v___x_3126_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3127_ = lean_string_dec_eq(v_snd_3101_, v___x_3126_);
lean_dec(v_snd_3101_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec(v_fst_3100_);
lean_dec(v___x_3084_);
v___x_3141_ = lean_box(v_hasTrace_3092_);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
else
{
uint8_t v___x_3143_; uint8_t v___x_3144_; uint8_t v___x_3145_; lean_object* v___x_3146_; uint64_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3143_ = 1;
v___x_3144_ = 0;
v___x_3145_ = 2;
v___x_3146_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3146_, 0, v___x_3110_);
lean_ctor_set_uint8(v___x_3146_, 1, v___x_3110_);
lean_ctor_set_uint8(v___x_3146_, 2, v___x_3110_);
lean_ctor_set_uint8(v___x_3146_, 3, v___x_3110_);
lean_ctor_set_uint8(v___x_3146_, 4, v___x_3110_);
lean_ctor_set_uint8(v___x_3146_, 5, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 6, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 7, v___x_3110_);
lean_ctor_set_uint8(v___x_3146_, 8, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 9, v___x_3143_);
lean_ctor_set_uint8(v___x_3146_, 10, v___x_3144_);
lean_ctor_set_uint8(v___x_3146_, 11, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 12, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 13, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 14, v___x_3145_);
lean_ctor_set_uint8(v___x_3146_, 15, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 16, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 17, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 18, v___x_3127_);
lean_ctor_set_uint8(v___x_3146_, 19, v___x_3110_);
v___x_3147_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3146_);
v___x_3148_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3148_, 0, v___x_3146_);
lean_ctor_set_uint64(v___x_3148_, sizeof(void*)*1, v___x_3147_);
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3151_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3152_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3153_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3154_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3154_, 0, v___x_3148_);
lean_ctor_set(v___x_3154_, 1, v___x_3084_);
lean_ctor_set(v___x_3154_, 2, v___x_3151_);
lean_ctor_set(v___x_3154_, 3, v___x_3152_);
lean_ctor_set(v___x_3154_, 4, v___x_3153_);
lean_ctor_set(v___x_3154_, 5, v___x_3149_);
lean_ctor_set(v___x_3154_, 6, v___x_3153_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*7, v___x_3110_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*7 + 1, v___x_3110_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*7 + 2, v___x_3110_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*7 + 3, v___x_3105_);
v___x_3155_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3156_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3157_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3155_);
lean_ctor_set(v___x_3158_, 1, v___x_3156_);
lean_ctor_set(v___x_3158_, 2, v___x_3084_);
lean_ctor_set(v___x_3158_, 3, v___x_3150_);
lean_ctor_set(v___x_3158_, 4, v___x_3157_);
v___x_3159_ = lean_st_mk_ref(v___x_3158_);
v___x_3160_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3100_, v___x_3105_, v___x_3154_, v___x_3159_, v___y_3087_, v___y_3088_);
lean_dec_ref_known(v___x_3154_, 7);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3162_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v___x_3162_ = lean_st_ref_get(v___x_3159_);
lean_dec(v___x_3159_);
lean_dec(v___x_3162_);
v_a_3129_ = v_a_3161_;
goto v___jp_3128_;
}
else
{
lean_dec(v___x_3159_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3163_; 
v_a_3163_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3160_, 1);
v_a_3129_ = v_a_3163_;
goto v___jp_3128_;
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_a_3164_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3160_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3160_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
v___jp_3128_:
{
if (lean_obj_tag(v_a_3129_) == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_box(v___x_3110_);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
else
{
lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3139_; 
v_isSharedCheck_3139_ = !lean_is_exclusive(v_a_3129_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v_a_3129_, 0);
lean_dec(v_unused_3140_);
v___x_3133_ = v_a_3129_;
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v_a_3129_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = lean_box(v___x_3127_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set_tag(v___x_3133_, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
else
{
uint8_t v___x_3172_; uint8_t v___x_3173_; uint8_t v___x_3174_; lean_object* v___x_3175_; uint64_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_dec(v_snd_3101_);
v___x_3172_ = 1;
v___x_3173_ = 0;
v___x_3174_ = 2;
v___x_3175_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3175_, 0, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3175_, 1, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3175_, 2, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3175_, 3, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3175_, 4, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3175_, 5, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 6, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 7, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3175_, 8, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 9, v___x_3172_);
lean_ctor_set_uint8(v___x_3175_, 10, v___x_3173_);
lean_ctor_set_uint8(v___x_3175_, 11, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 12, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 13, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 14, v___x_3174_);
lean_ctor_set_uint8(v___x_3175_, 15, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 16, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 17, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 18, v___x_3110_);
lean_ctor_set_uint8(v___x_3175_, 19, v_hasTrace_3092_);
v___x_3176_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3175_);
v___x_3177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set_uint64(v___x_3177_, sizeof(void*)*1, v___x_3176_);
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3180_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3181_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3182_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3183_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3183_, 0, v___x_3177_);
lean_ctor_set(v___x_3183_, 1, v___x_3084_);
lean_ctor_set(v___x_3183_, 2, v___x_3180_);
lean_ctor_set(v___x_3183_, 3, v___x_3181_);
lean_ctor_set(v___x_3183_, 4, v___x_3182_);
lean_ctor_set(v___x_3183_, 5, v___x_3178_);
lean_ctor_set(v___x_3183_, 6, v___x_3182_);
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*7, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*7 + 1, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*7 + 2, v_hasTrace_3092_);
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*7 + 3, v___x_3105_);
v___x_3184_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3185_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3186_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3184_);
lean_ctor_set(v___x_3187_, 1, v___x_3185_);
lean_ctor_set(v___x_3187_, 2, v___x_3084_);
lean_ctor_set(v___x_3187_, 3, v___x_3179_);
lean_ctor_set(v___x_3187_, 4, v___x_3186_);
v___x_3188_ = lean_st_mk_ref(v___x_3187_);
v___x_3189_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3100_, v___x_3183_, v___x_3188_, v___y_3087_, v___y_3088_);
lean_dec_ref_known(v___x_3183_, 7);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3191_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3189_, 1);
v___x_3191_ = lean_st_ref_get(v___x_3188_);
lean_dec(v___x_3188_);
lean_dec(v___x_3191_);
v_a_3112_ = v_a_3190_;
goto v___jp_3111_;
}
else
{
lean_dec(v___x_3188_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3192_; 
v_a_3192_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3189_, 1);
v_a_3112_ = v_a_3192_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_del_object(v___x_3098_);
v_a_3193_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3189_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3189_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
v___jp_3111_:
{
if (lean_obj_tag(v_a_3112_) == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3113_ = lean_box(v_hasTrace_3092_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set_tag(v___x_3098_, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3113_);
v___x_3115_ = v___x_3098_;
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
lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3124_; 
lean_del_object(v___x_3098_);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_3112_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_a_3112_, 0);
lean_dec(v_unused_3125_);
v___x_3118_ = v_a_3112_;
v_isShared_3119_ = v_isSharedCheck_3124_;
goto v_resetjp_3117_;
}
else
{
lean_dec(v_a_3112_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3124_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = lean_box(v___x_3110_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3120_);
v___x_3122_ = v___x_3118_;
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
}
}
}
}
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_dec(v___x_3095_);
lean_dec(v_name_3086_);
lean_dec(v___x_3084_);
v___x_3202_ = lean_box(v_hasTrace_3092_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3204_; lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v_a_3213_; lean_object* v___y_3226_; lean_object* v___y_3227_; uint8_t v_a_3228_; lean_object* v___y_3232_; lean_object* v___y_3233_; uint8_t v___y_3234_; uint8_t v___y_3235_; lean_object* v_a_3236_; lean_object* v___y_3238_; uint8_t v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v_a_3242_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v_a_3246_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v_a_3251_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v_a_3263_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v_a_3268_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v_a_3282_; lean_object* v___y_3285_; lean_object* v___y_3286_; uint8_t v___y_3287_; uint8_t v___y_3288_; lean_object* v_a_3289_; 
v_inheritedTraceOptions_3204_ = lean_ctor_get(v_toCold_3090_, 11);
lean_inc(v_name_3086_);
v___f_3205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3205_, 0, v_name_3086_);
v___x_3206_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3207_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3208_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3209_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3204_, v_options_3091_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3418_ = l_Lean_trace_profiler;
v___x_3419_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3091_, v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v_env_3421_; lean_object* v___x_3422_; 
lean_dec_ref(v___f_3205_);
lean_dec_ref(v___f_3085_);
v___x_3420_ = lean_st_ref_get(v___y_3088_);
v_env_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc_ref(v_env_3421_);
lean_dec(v___x_3420_);
lean_inc(v_name_3086_);
v___x_3422_ = l_Lean_Meta_declFromEqLikeName(v_env_3421_, v_name_3086_);
if (lean_obj_tag(v___x_3422_) == 1)
{
lean_object* v_val_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3528_; 
v_val_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3528_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_val_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3528_;
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
v___x_3429_ = lean_st_ref_get(v___y_3088_);
v_env_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc_ref(v_env_3430_);
lean_dec(v___x_3429_);
v___x_3431_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3430_, v_fst_3427_, v_snd_3428_);
v___x_3432_ = lean_name_eq(v_name_3086_, v___x_3431_);
lean_dec(v___x_3431_);
lean_dec(v_name_3086_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v___x_3084_);
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
uint8_t v___x_3437_; lean_object* v_a_3439_; 
lean_inc(v_snd_3428_);
v___x_3437_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3428_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3453_; uint8_t v___x_3454_; lean_object* v_a_3456_; 
lean_del_object(v___x_3425_);
v___x_3453_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3454_ = lean_string_dec_eq(v_snd_3428_, v___x_3453_);
lean_dec(v_snd_3428_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_dec(v_fst_3427_);
lean_dec(v___x_3084_);
v___x_3468_ = lean_box(v___x_3419_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
else
{
uint8_t v___x_3470_; uint8_t v___x_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; uint64_t v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3470_ = 1;
v___x_3471_ = 0;
v___x_3472_ = 2;
v___x_3473_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3473_, 0, v___x_3437_);
lean_ctor_set_uint8(v___x_3473_, 1, v___x_3437_);
lean_ctor_set_uint8(v___x_3473_, 2, v___x_3437_);
lean_ctor_set_uint8(v___x_3473_, 3, v___x_3437_);
lean_ctor_set_uint8(v___x_3473_, 4, v___x_3437_);
lean_ctor_set_uint8(v___x_3473_, 5, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 6, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 7, v___x_3437_);
lean_ctor_set_uint8(v___x_3473_, 8, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 9, v___x_3470_);
lean_ctor_set_uint8(v___x_3473_, 10, v___x_3471_);
lean_ctor_set_uint8(v___x_3473_, 11, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 12, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 13, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 14, v___x_3472_);
lean_ctor_set_uint8(v___x_3473_, 15, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 16, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 17, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 18, v___x_3454_);
lean_ctor_set_uint8(v___x_3473_, 19, v___x_3437_);
v___x_3474_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3473_);
v___x_3475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set_uint64(v___x_3475_, sizeof(void*)*1, v___x_3474_);
v___x_3476_ = lean_unsigned_to_nat(0u);
v___x_3477_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3478_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3479_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3480_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3481_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3481_, 0, v___x_3475_);
lean_ctor_set(v___x_3481_, 1, v___x_3084_);
lean_ctor_set(v___x_3481_, 2, v___x_3478_);
lean_ctor_set(v___x_3481_, 3, v___x_3479_);
lean_ctor_set(v___x_3481_, 4, v___x_3480_);
lean_ctor_set(v___x_3481_, 5, v___x_3476_);
lean_ctor_set(v___x_3481_, 6, v___x_3480_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7, v___x_3437_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7 + 1, v___x_3437_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7 + 2, v___x_3437_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*7 + 3, v_hasTrace_3092_);
v___x_3482_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3483_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3482_);
lean_ctor_set(v___x_3485_, 1, v___x_3483_);
lean_ctor_set(v___x_3485_, 2, v___x_3084_);
lean_ctor_set(v___x_3485_, 3, v___x_3477_);
lean_ctor_set(v___x_3485_, 4, v___x_3484_);
v___x_3486_ = lean_st_mk_ref(v___x_3485_);
v___x_3487_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3427_, v_hasTrace_3092_, v___x_3481_, v___x_3486_, v___y_3087_, v___y_3088_);
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
v_a_3456_ = v_a_3488_;
goto v___jp_3455_;
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
v_a_3456_ = v_a_3490_;
goto v___jp_3455_;
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
v_a_3491_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3487_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3487_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
v___jp_3455_:
{
if (lean_obj_tag(v_a_3456_) == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = lean_box(v___x_3437_);
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
else
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3466_; 
v_isSharedCheck_3466_ = !lean_is_exclusive(v_a_3456_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v_a_3456_, 0);
lean_dec(v_unused_3467_);
v___x_3460_ = v_a_3456_;
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v_a_3456_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3462_ = lean_box(v___x_3454_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set_tag(v___x_3460_, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3462_);
v___x_3464_ = v___x_3460_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
else
{
uint8_t v___x_3499_; uint8_t v___x_3500_; uint8_t v___x_3501_; lean_object* v___x_3502_; uint64_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
lean_dec(v_snd_3428_);
v___x_3499_ = 1;
v___x_3500_ = 0;
v___x_3501_ = 2;
v___x_3502_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3502_, 0, v___x_3419_);
lean_ctor_set_uint8(v___x_3502_, 1, v___x_3419_);
lean_ctor_set_uint8(v___x_3502_, 2, v___x_3419_);
lean_ctor_set_uint8(v___x_3502_, 3, v___x_3419_);
lean_ctor_set_uint8(v___x_3502_, 4, v___x_3419_);
lean_ctor_set_uint8(v___x_3502_, 5, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 6, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 7, v___x_3419_);
lean_ctor_set_uint8(v___x_3502_, 8, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 9, v___x_3499_);
lean_ctor_set_uint8(v___x_3502_, 10, v___x_3500_);
lean_ctor_set_uint8(v___x_3502_, 11, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 12, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 13, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 14, v___x_3501_);
lean_ctor_set_uint8(v___x_3502_, 15, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 16, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 17, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 18, v___x_3437_);
lean_ctor_set_uint8(v___x_3502_, 19, v___x_3419_);
v___x_3503_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3502_);
v___x_3504_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3504_, 0, v___x_3502_);
lean_ctor_set_uint64(v___x_3504_, sizeof(void*)*1, v___x_3503_);
v___x_3505_ = lean_unsigned_to_nat(0u);
v___x_3506_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3507_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3509_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3510_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3510_, 0, v___x_3504_);
lean_ctor_set(v___x_3510_, 1, v___x_3084_);
lean_ctor_set(v___x_3510_, 2, v___x_3507_);
lean_ctor_set(v___x_3510_, 3, v___x_3508_);
lean_ctor_set(v___x_3510_, 4, v___x_3509_);
lean_ctor_set(v___x_3510_, 5, v___x_3505_);
lean_ctor_set(v___x_3510_, 6, v___x_3509_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7, v___x_3419_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7 + 1, v___x_3419_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7 + 2, v___x_3419_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7 + 3, v_hasTrace_3092_);
v___x_3511_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3512_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3513_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3511_);
lean_ctor_set(v___x_3514_, 1, v___x_3512_);
lean_ctor_set(v___x_3514_, 2, v___x_3084_);
lean_ctor_set(v___x_3514_, 3, v___x_3506_);
lean_ctor_set(v___x_3514_, 4, v___x_3513_);
v___x_3515_ = lean_st_mk_ref(v___x_3514_);
v___x_3516_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3427_, v___x_3510_, v___x_3515_, v___y_3087_, v___y_3088_);
lean_dec_ref_known(v___x_3510_, 7);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
v___x_3518_ = lean_st_ref_get(v___x_3515_);
lean_dec(v___x_3515_);
lean_dec(v___x_3518_);
v_a_3439_ = v_a_3517_;
goto v___jp_3438_;
}
else
{
lean_dec(v___x_3515_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3519_; 
v_a_3519_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3516_, 1);
v_a_3439_ = v_a_3519_;
goto v___jp_3438_;
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_del_object(v___x_3425_);
v_a_3520_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3516_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3516_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
v___jp_3438_:
{
if (lean_obj_tag(v_a_3439_) == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
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
lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3451_; 
lean_del_object(v___x_3425_);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_a_3439_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; 
v_unused_3452_ = lean_ctor_get(v_a_3439_, 0);
lean_dec(v_unused_3452_);
v___x_3445_ = v_a_3439_;
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
else
{
lean_dec(v_a_3439_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3447_ = lean_box(v___x_3437_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set_tag(v___x_3445_, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v___x_3422_);
lean_dec(v_name_3086_);
lean_dec(v___x_3084_);
v___x_3529_ = lean_box(v___x_3419_);
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
}
else
{
goto v___jp_3290_;
}
}
else
{
goto v___jp_3290_;
}
v___jp_3210_:
{
lean_object* v___x_3214_; double v___x_3215_; double v___x_3216_; double v___x_3217_; double v___x_3218_; double v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3214_ = lean_io_mono_nanos_now();
v___x_3215_ = lean_float_of_nat(v___y_3212_);
v___x_3216_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3217_ = lean_float_div(v___x_3215_, v___x_3216_);
v___x_3218_ = lean_float_of_nat(v___x_3214_);
v___x_3219_ = lean_float_div(v___x_3218_, v___x_3216_);
v___x_3220_ = lean_box_float(v___x_3217_);
v___x_3221_ = lean_box_float(v___x_3219_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v_a_3213_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3206_, v_hasTrace_3092_, v___x_3207_, v_options_3091_, v___x_3209_, v___y_3211_, v___f_3205_, v___x_3223_, v___y_3087_, v___y_3088_);
return v___x_3224_;
}
v___jp_3225_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_box(v_a_3228_);
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
v___y_3211_ = v___y_3226_;
v___y_3212_ = v___y_3227_;
v_a_3213_ = v___x_3230_;
goto v___jp_3210_;
}
v___jp_3231_:
{
if (lean_obj_tag(v_a_3236_) == 0)
{
v___y_3226_ = v___y_3232_;
v___y_3227_ = v___y_3233_;
v_a_3228_ = v___y_3234_;
goto v___jp_3225_;
}
else
{
lean_dec_ref_known(v_a_3236_, 1);
v___y_3226_ = v___y_3232_;
v___y_3227_ = v___y_3233_;
v_a_3228_ = v___y_3235_;
goto v___jp_3225_;
}
}
v___jp_3237_:
{
if (lean_obj_tag(v_a_3242_) == 0)
{
v___y_3226_ = v___y_3238_;
v___y_3227_ = v___y_3240_;
v_a_3228_ = v___y_3241_;
goto v___jp_3225_;
}
else
{
lean_dec_ref_known(v_a_3242_, 1);
v___y_3226_ = v___y_3238_;
v___y_3227_ = v___y_3240_;
v_a_3228_ = v___y_3239_;
goto v___jp_3225_;
}
}
v___jp_3243_:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_a_3246_);
v___y_3211_ = v___y_3244_;
v___y_3212_ = v___y_3245_;
v_a_3213_ = v___x_3247_;
goto v___jp_3210_;
}
v___jp_3248_:
{
lean_object* v___x_3252_; double v___x_3253_; double v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3252_ = lean_io_get_num_heartbeats();
v___x_3253_ = lean_float_of_nat(v___y_3250_);
v___x_3254_ = lean_float_of_nat(v___x_3252_);
v___x_3255_ = lean_box_float(v___x_3253_);
v___x_3256_ = lean_box_float(v___x_3254_);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v_a_3251_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3206_, v_hasTrace_3092_, v___x_3207_, v_options_3091_, v___x_3209_, v___y_3249_, v___f_3205_, v___x_3258_, v___y_3087_, v___y_3088_);
return v___x_3259_;
}
v___jp_3260_:
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_a_3263_);
v___y_3249_ = v___y_3261_;
v___y_3250_ = v___y_3262_;
v_a_3251_ = v___x_3264_;
goto v___jp_3248_;
}
v___jp_3265_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_box(v_a_3268_);
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
v___y_3249_ = v___y_3266_;
v___y_3250_ = v___y_3267_;
v_a_3251_ = v___x_3270_;
goto v___jp_3248_;
}
v___jp_3271_:
{
if (lean_obj_tag(v___y_3274_) == 0)
{
lean_object* v_a_3275_; uint8_t v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___y_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___y_3274_, 1);
v___x_3276_ = lean_unbox(v_a_3275_);
lean_dec(v_a_3275_);
v___y_3266_ = v___y_3272_;
v___y_3267_ = v___y_3273_;
v_a_3268_ = v___x_3276_;
goto v___jp_3265_;
}
else
{
lean_object* v_a_3277_; 
v_a_3277_ = lean_ctor_get(v___y_3274_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___y_3274_, 1);
v___y_3261_ = v___y_3272_;
v___y_3262_ = v___y_3273_;
v_a_3263_ = v_a_3277_;
goto v___jp_3260_;
}
}
v___jp_3278_:
{
if (lean_obj_tag(v_a_3282_) == 0)
{
uint8_t v___x_3283_; 
v___x_3283_ = 0;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v_a_3268_ = v___x_3283_;
goto v___jp_3265_;
}
else
{
lean_dec_ref_known(v_a_3282_, 1);
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v_a_3268_ = v___y_3281_;
goto v___jp_3265_;
}
}
v___jp_3284_:
{
if (lean_obj_tag(v_a_3289_) == 0)
{
v___y_3266_ = v___y_3285_;
v___y_3267_ = v___y_3286_;
v_a_3268_ = v___y_3288_;
goto v___jp_3265_;
}
else
{
lean_dec_ref_known(v_a_3289_, 1);
v___y_3266_ = v___y_3285_;
v___y_3267_ = v___y_3286_;
v_a_3268_ = v___y_3287_;
goto v___jp_3265_;
}
}
v___jp_3290_:
{
lean_object* v___x_3291_; lean_object* v_a_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v___x_3291_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3088_);
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref(v___x_3291_);
v___x_3293_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3294_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3091_, v___x_3293_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v_env_3297_; lean_object* v___x_3298_; 
lean_dec_ref(v___f_3085_);
v___x_3295_ = lean_io_mono_nanos_now();
v___x_3296_ = lean_st_ref_get(v___y_3088_);
v_env_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc_ref(v_env_3297_);
lean_dec(v___x_3296_);
lean_inc(v_name_3086_);
v___x_3298_ = l_Lean_Meta_declFromEqLikeName(v_env_3297_, v_name_3086_);
if (lean_obj_tag(v___x_3298_) == 1)
{
lean_object* v_val_3299_; lean_object* v_fst_3300_; lean_object* v_snd_3301_; lean_object* v___x_3302_; lean_object* v_env_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_val_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v_fst_3300_ = lean_ctor_get(v_val_3299_, 0);
lean_inc_n(v_fst_3300_, 2);
v_snd_3301_ = lean_ctor_get(v_val_3299_, 1);
lean_inc_n(v_snd_3301_, 2);
lean_dec(v_val_3299_);
v___x_3302_ = lean_st_ref_get(v___y_3088_);
v_env_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc_ref(v_env_3303_);
lean_dec(v___x_3302_);
v___x_3304_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3303_, v_fst_3300_, v_snd_3301_);
v___x_3305_ = lean_name_eq(v_name_3086_, v___x_3304_);
lean_dec(v___x_3304_);
lean_dec(v_name_3086_);
if (v___x_3305_ == 0)
{
lean_dec(v_snd_3301_);
lean_dec(v_fst_3300_);
lean_dec(v___x_3084_);
v___y_3226_ = v_a_3292_;
v___y_3227_ = v___x_3295_;
v_a_3228_ = v___x_3294_;
goto v___jp_3225_;
}
else
{
uint8_t v___x_3306_; 
lean_inc(v_snd_3301_);
v___x_3306_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3301_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3308_ = lean_string_dec_eq(v_snd_3301_, v___x_3307_);
lean_dec(v_snd_3301_);
if (v___x_3308_ == 0)
{
lean_dec(v_fst_3300_);
lean_dec(v___x_3084_);
v___y_3226_ = v_a_3292_;
v___y_3227_ = v___x_3295_;
v_a_3228_ = v___x_3294_;
goto v___jp_3225_;
}
else
{
uint8_t v___x_3309_; uint8_t v___x_3310_; uint8_t v___x_3311_; lean_object* v___x_3312_; uint64_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3309_ = 1;
v___x_3310_ = 0;
v___x_3311_ = 2;
v___x_3312_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3312_, 0, v___x_3306_);
lean_ctor_set_uint8(v___x_3312_, 1, v___x_3306_);
lean_ctor_set_uint8(v___x_3312_, 2, v___x_3306_);
lean_ctor_set_uint8(v___x_3312_, 3, v___x_3306_);
lean_ctor_set_uint8(v___x_3312_, 4, v___x_3306_);
lean_ctor_set_uint8(v___x_3312_, 5, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 6, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 7, v___x_3306_);
lean_ctor_set_uint8(v___x_3312_, 8, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 9, v___x_3309_);
lean_ctor_set_uint8(v___x_3312_, 10, v___x_3310_);
lean_ctor_set_uint8(v___x_3312_, 11, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 12, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 13, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 14, v___x_3311_);
lean_ctor_set_uint8(v___x_3312_, 15, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 16, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 17, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 18, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, 19, v___x_3306_);
v___x_3313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3312_);
v___x_3314_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set_uint64(v___x_3314_, sizeof(void*)*1, v___x_3313_);
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3317_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3319_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3320_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3320_, 0, v___x_3314_);
lean_ctor_set(v___x_3320_, 1, v___x_3084_);
lean_ctor_set(v___x_3320_, 2, v___x_3317_);
lean_ctor_set(v___x_3320_, 3, v___x_3318_);
lean_ctor_set(v___x_3320_, 4, v___x_3319_);
lean_ctor_set(v___x_3320_, 5, v___x_3315_);
lean_ctor_set(v___x_3320_, 6, v___x_3319_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7, v___x_3306_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7 + 1, v___x_3306_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7 + 2, v___x_3306_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7 + 3, v_hasTrace_3092_);
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3322_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3323_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3321_);
lean_ctor_set(v___x_3324_, 1, v___x_3322_);
lean_ctor_set(v___x_3324_, 2, v___x_3084_);
lean_ctor_set(v___x_3324_, 3, v___x_3316_);
lean_ctor_set(v___x_3324_, 4, v___x_3323_);
v___x_3325_ = lean_st_mk_ref(v___x_3324_);
v___x_3326_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3300_, v_hasTrace_3092_, v___x_3320_, v___x_3325_, v___y_3087_, v___y_3088_);
lean_dec_ref_known(v___x_3320_, 7);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = lean_st_ref_get(v___x_3325_);
lean_dec(v___x_3325_);
lean_dec(v___x_3328_);
v___y_3232_ = v_a_3292_;
v___y_3233_ = v___x_3295_;
v___y_3234_ = v___x_3306_;
v___y_3235_ = v___x_3308_;
v_a_3236_ = v_a_3327_;
goto v___jp_3231_;
}
else
{
lean_dec(v___x_3325_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3329_; 
v_a_3329_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3326_, 1);
v___y_3232_ = v_a_3292_;
v___y_3233_ = v___x_3295_;
v___y_3234_ = v___x_3306_;
v___y_3235_ = v___x_3308_;
v_a_3236_ = v_a_3329_;
goto v___jp_3231_;
}
else
{
lean_object* v_a_3330_; 
v_a_3330_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3326_, 1);
v___y_3244_ = v_a_3292_;
v___y_3245_ = v___x_3295_;
v_a_3246_ = v_a_3330_;
goto v___jp_3243_;
}
}
}
}
else
{
uint8_t v___x_3331_; uint8_t v___x_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; uint64_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v_snd_3301_);
v___x_3331_ = 1;
v___x_3332_ = 0;
v___x_3333_ = 2;
v___x_3334_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3334_, 0, v___x_3294_);
lean_ctor_set_uint8(v___x_3334_, 1, v___x_3294_);
lean_ctor_set_uint8(v___x_3334_, 2, v___x_3294_);
lean_ctor_set_uint8(v___x_3334_, 3, v___x_3294_);
lean_ctor_set_uint8(v___x_3334_, 4, v___x_3294_);
lean_ctor_set_uint8(v___x_3334_, 5, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 6, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 7, v___x_3294_);
lean_ctor_set_uint8(v___x_3334_, 8, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 9, v___x_3331_);
lean_ctor_set_uint8(v___x_3334_, 10, v___x_3332_);
lean_ctor_set_uint8(v___x_3334_, 11, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 12, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 13, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 14, v___x_3333_);
lean_ctor_set_uint8(v___x_3334_, 15, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 16, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 17, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 18, v___x_3306_);
lean_ctor_set_uint8(v___x_3334_, 19, v___x_3294_);
v___x_3335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3334_);
v___x_3336_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set_uint64(v___x_3336_, sizeof(void*)*1, v___x_3335_);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3339_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3340_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3341_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3342_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3342_, 0, v___x_3336_);
lean_ctor_set(v___x_3342_, 1, v___x_3084_);
lean_ctor_set(v___x_3342_, 2, v___x_3339_);
lean_ctor_set(v___x_3342_, 3, v___x_3340_);
lean_ctor_set(v___x_3342_, 4, v___x_3341_);
lean_ctor_set(v___x_3342_, 5, v___x_3337_);
lean_ctor_set(v___x_3342_, 6, v___x_3341_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7, v___x_3294_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7 + 1, v___x_3294_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7 + 2, v___x_3294_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7 + 3, v_hasTrace_3092_);
v___x_3343_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3344_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3345_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3343_);
lean_ctor_set(v___x_3346_, 1, v___x_3344_);
lean_ctor_set(v___x_3346_, 2, v___x_3084_);
lean_ctor_set(v___x_3346_, 3, v___x_3338_);
lean_ctor_set(v___x_3346_, 4, v___x_3345_);
v___x_3347_ = lean_st_mk_ref(v___x_3346_);
v___x_3348_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3300_, v___x_3342_, v___x_3347_, v___y_3087_, v___y_3088_);
lean_dec_ref_known(v___x_3342_, 7);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v___x_3350_ = lean_st_ref_get(v___x_3347_);
lean_dec(v___x_3347_);
lean_dec(v___x_3350_);
v___y_3238_ = v_a_3292_;
v___y_3239_ = v___x_3306_;
v___y_3240_ = v___x_3295_;
v___y_3241_ = v___x_3294_;
v_a_3242_ = v_a_3349_;
goto v___jp_3237_;
}
else
{
lean_dec(v___x_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3351_; 
v_a_3351_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3348_, 1);
v___y_3238_ = v_a_3292_;
v___y_3239_ = v___x_3306_;
v___y_3240_ = v___x_3295_;
v___y_3241_ = v___x_3294_;
v_a_3242_ = v_a_3351_;
goto v___jp_3237_;
}
else
{
lean_object* v_a_3352_; 
v_a_3352_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3348_, 1);
v___y_3244_ = v_a_3292_;
v___y_3245_ = v___x_3295_;
v_a_3246_ = v_a_3352_;
goto v___jp_3243_;
}
}
}
}
}
else
{
lean_dec(v___x_3298_);
lean_dec(v_name_3086_);
lean_dec(v___x_3084_);
v___y_3226_ = v_a_3292_;
v___y_3227_ = v___x_3295_;
v_a_3228_ = v___x_3294_;
goto v___jp_3225_;
}
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v_env_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_io_get_num_heartbeats();
v___x_3354_ = lean_st_ref_get(v___y_3088_);
v_env_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc_ref(v_env_3355_);
lean_dec(v___x_3354_);
lean_inc(v_name_3086_);
v___x_3356_ = l_Lean_Meta_declFromEqLikeName(v_env_3355_, v_name_3086_);
if (lean_obj_tag(v___x_3356_) == 1)
{
lean_object* v_val_3357_; lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v___x_3360_; lean_object* v_env_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_val_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v_fst_3358_ = lean_ctor_get(v_val_3357_, 0);
lean_inc_n(v_fst_3358_, 2);
v_snd_3359_ = lean_ctor_get(v_val_3357_, 1);
lean_inc_n(v_snd_3359_, 2);
lean_dec(v_val_3357_);
v___x_3360_ = lean_st_ref_get(v___y_3088_);
v_env_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc_ref(v_env_3361_);
lean_dec(v___x_3360_);
v___x_3362_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3361_, v_fst_3358_, v_snd_3359_);
v___x_3363_ = lean_name_eq(v_name_3086_, v___x_3362_);
lean_dec(v___x_3362_);
lean_dec(v_name_3086_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec(v_snd_3359_);
lean_dec(v_fst_3358_);
lean_dec(v___x_3084_);
v___x_3364_ = lean_box(0);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3087_);
v___x_3365_ = lean_apply_4(v___f_3085_, v___x_3364_, v___y_3087_, v___y_3088_, lean_box(0));
v___y_3272_ = v_a_3292_;
v___y_3273_ = v___x_3353_;
v___y_3274_ = v___x_3365_;
goto v___jp_3271_;
}
else
{
uint8_t v___x_3366_; 
lean_inc(v_snd_3359_);
v___x_3366_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3359_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3367_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3368_ = lean_string_dec_eq(v_snd_3359_, v___x_3367_);
lean_dec(v_snd_3359_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec(v_fst_3358_);
lean_dec(v___x_3084_);
v___x_3369_ = lean_box(0);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3087_);
v___x_3370_ = lean_apply_4(v___f_3085_, v___x_3369_, v___y_3087_, v___y_3088_, lean_box(0));
v___y_3272_ = v_a_3292_;
v___y_3273_ = v___x_3353_;
v___y_3274_ = v___x_3370_;
goto v___jp_3271_;
}
else
{
uint8_t v___x_3371_; uint8_t v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; uint64_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec_ref(v___f_3085_);
v___x_3371_ = 1;
v___x_3372_ = 0;
v___x_3373_ = 2;
v___x_3374_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3374_, 0, v___x_3366_);
lean_ctor_set_uint8(v___x_3374_, 1, v___x_3366_);
lean_ctor_set_uint8(v___x_3374_, 2, v___x_3366_);
lean_ctor_set_uint8(v___x_3374_, 3, v___x_3366_);
lean_ctor_set_uint8(v___x_3374_, 4, v___x_3366_);
lean_ctor_set_uint8(v___x_3374_, 5, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 6, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 7, v___x_3366_);
lean_ctor_set_uint8(v___x_3374_, 8, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 9, v___x_3371_);
lean_ctor_set_uint8(v___x_3374_, 10, v___x_3372_);
lean_ctor_set_uint8(v___x_3374_, 11, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 12, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 13, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 14, v___x_3373_);
lean_ctor_set_uint8(v___x_3374_, 15, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 16, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 17, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 18, v___x_3368_);
lean_ctor_set_uint8(v___x_3374_, 19, v___x_3366_);
v___x_3375_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3374_);
v___x_3376_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set_uint64(v___x_3376_, sizeof(void*)*1, v___x_3375_);
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3379_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3381_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3382_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3382_, 0, v___x_3376_);
lean_ctor_set(v___x_3382_, 1, v___x_3084_);
lean_ctor_set(v___x_3382_, 2, v___x_3379_);
lean_ctor_set(v___x_3382_, 3, v___x_3380_);
lean_ctor_set(v___x_3382_, 4, v___x_3381_);
lean_ctor_set(v___x_3382_, 5, v___x_3377_);
lean_ctor_set(v___x_3382_, 6, v___x_3381_);
lean_ctor_set_uint8(v___x_3382_, sizeof(void*)*7, v___x_3366_);
lean_ctor_set_uint8(v___x_3382_, sizeof(void*)*7 + 1, v___x_3366_);
lean_ctor_set_uint8(v___x_3382_, sizeof(void*)*7 + 2, v___x_3366_);
lean_ctor_set_uint8(v___x_3382_, sizeof(void*)*7 + 3, v___x_3294_);
v___x_3383_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3384_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3385_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3383_);
lean_ctor_set(v___x_3386_, 1, v___x_3384_);
lean_ctor_set(v___x_3386_, 2, v___x_3084_);
lean_ctor_set(v___x_3386_, 3, v___x_3378_);
lean_ctor_set(v___x_3386_, 4, v___x_3385_);
v___x_3387_ = lean_st_mk_ref(v___x_3386_);
v___x_3388_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3358_, v___x_3294_, v___x_3382_, v___x_3387_, v___y_3087_, v___y_3088_);
lean_dec_ref_known(v___x_3382_, 7);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = lean_st_ref_get(v___x_3387_);
lean_dec(v___x_3387_);
lean_dec(v___x_3390_);
v___y_3285_ = v_a_3292_;
v___y_3286_ = v___x_3353_;
v___y_3287_ = v___x_3368_;
v___y_3288_ = v___x_3366_;
v_a_3289_ = v_a_3389_;
goto v___jp_3284_;
}
else
{
lean_dec(v___x_3387_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3388_, 1);
v___y_3285_ = v_a_3292_;
v___y_3286_ = v___x_3353_;
v___y_3287_ = v___x_3368_;
v___y_3288_ = v___x_3366_;
v_a_3289_ = v_a_3391_;
goto v___jp_3284_;
}
else
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3388_, 1);
v___y_3261_ = v_a_3292_;
v___y_3262_ = v___x_3353_;
v_a_3263_ = v_a_3392_;
goto v___jp_3260_;
}
}
}
}
else
{
uint8_t v___x_3393_; uint8_t v___x_3394_; uint8_t v___x_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; uint64_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec(v_snd_3359_);
lean_dec_ref(v___f_3085_);
v___x_3393_ = 0;
v___x_3394_ = 1;
v___x_3395_ = 0;
v___x_3396_ = 2;
v___x_3397_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3397_, 0, v___x_3393_);
lean_ctor_set_uint8(v___x_3397_, 1, v___x_3393_);
lean_ctor_set_uint8(v___x_3397_, 2, v___x_3393_);
lean_ctor_set_uint8(v___x_3397_, 3, v___x_3393_);
lean_ctor_set_uint8(v___x_3397_, 4, v___x_3393_);
lean_ctor_set_uint8(v___x_3397_, 5, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 6, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 7, v___x_3393_);
lean_ctor_set_uint8(v___x_3397_, 8, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 9, v___x_3394_);
lean_ctor_set_uint8(v___x_3397_, 10, v___x_3395_);
lean_ctor_set_uint8(v___x_3397_, 11, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 12, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 13, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 14, v___x_3396_);
lean_ctor_set_uint8(v___x_3397_, 15, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 16, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 17, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 18, v___x_3366_);
lean_ctor_set_uint8(v___x_3397_, 19, v___x_3393_);
v___x_3398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3397_);
v___x_3399_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set_uint64(v___x_3399_, sizeof(void*)*1, v___x_3398_);
v___x_3400_ = lean_unsigned_to_nat(0u);
v___x_3401_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3403_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3404_ = lean_box(0);
lean_inc(v___x_3084_);
v___x_3405_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3405_, 0, v___x_3399_);
lean_ctor_set(v___x_3405_, 1, v___x_3084_);
lean_ctor_set(v___x_3405_, 2, v___x_3402_);
lean_ctor_set(v___x_3405_, 3, v___x_3403_);
lean_ctor_set(v___x_3405_, 4, v___x_3404_);
lean_ctor_set(v___x_3405_, 5, v___x_3400_);
lean_ctor_set(v___x_3405_, 6, v___x_3404_);
lean_ctor_set_uint8(v___x_3405_, sizeof(void*)*7, v___x_3393_);
lean_ctor_set_uint8(v___x_3405_, sizeof(void*)*7 + 1, v___x_3393_);
lean_ctor_set_uint8(v___x_3405_, sizeof(void*)*7 + 2, v___x_3393_);
lean_ctor_set_uint8(v___x_3405_, sizeof(void*)*7 + 3, v___x_3294_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3408_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3406_);
lean_ctor_set(v___x_3409_, 1, v___x_3407_);
lean_ctor_set(v___x_3409_, 2, v___x_3084_);
lean_ctor_set(v___x_3409_, 3, v___x_3401_);
lean_ctor_set(v___x_3409_, 4, v___x_3408_);
v___x_3410_ = lean_st_mk_ref(v___x_3409_);
v___x_3411_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3358_, v___x_3405_, v___x_3410_, v___y_3087_, v___y_3088_);
lean_dec_ref_known(v___x_3405_, 7);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3413_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v___x_3413_ = lean_st_ref_get(v___x_3410_);
lean_dec(v___x_3410_);
lean_dec(v___x_3413_);
v___y_3279_ = v_a_3292_;
v___y_3280_ = v___x_3353_;
v___y_3281_ = v___x_3366_;
v_a_3282_ = v_a_3412_;
goto v___jp_3278_;
}
else
{
lean_dec(v___x_3410_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3414_; 
v_a_3414_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3411_, 1);
v___y_3279_ = v_a_3292_;
v___y_3280_ = v___x_3353_;
v___y_3281_ = v___x_3366_;
v_a_3282_ = v_a_3414_;
goto v___jp_3278_;
}
else
{
lean_object* v_a_3415_; 
v_a_3415_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3411_, 1);
v___y_3261_ = v_a_3292_;
v___y_3262_ = v___x_3353_;
v_a_3263_ = v_a_3415_;
goto v___jp_3260_;
}
}
}
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec(v___x_3356_);
lean_dec(v_name_3086_);
lean_dec(v___x_3084_);
v___x_3416_ = lean_box(0);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3087_);
v___x_3417_ = lean_apply_4(v___f_3085_, v___x_3416_, v___y_3087_, v___y_3088_, lean_box(0));
v___y_3272_ = v_a_3292_;
v___y_3273_ = v___x_3353_;
v___y_3274_ = v___x_3417_;
goto v___jp_3271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3531_, lean_object* v___f_3532_, lean_object* v_name_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3531_, v___f_3532_, v_name_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = lean_unsigned_to_nat(3137104340u);
v___x_3583_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3584_ = l_Lean_Name_num___override(v___x_3583_, v___x_3582_);
return v___x_3584_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3586_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3587_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3588_ = l_Lean_Name_str___override(v___x_3587_, v___x_3586_);
return v___x_3588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3591_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3592_ = l_Lean_Name_str___override(v___x_3591_, v___x_3590_);
return v___x_3592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = lean_unsigned_to_nat(2u);
v___x_3594_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3595_ = l_Lean_Name_num___override(v___x_3594_, v___x_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3597_; lean_object* v___x_3598_; 
v___f_3597_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3598_ = l_Lean_registerReservedNameAction(v___f_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v___x_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_dec_ref_known(v___x_3598_, 1);
v___x_3599_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3600_ = 0;
v___x_3601_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3602_ = l_Lean_registerTraceClass(v___x_3599_, v___x_3600_, v___x_3601_);
return v___x_3602_;
}
else
{
return v___x_3598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3605_, lean_object* v_x_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3606_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3611_, lean_object* v_x_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3611_, v_x_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
return v_res_3616_;
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
