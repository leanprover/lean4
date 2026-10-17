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
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_withEqnOptions___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_withEqnOptions___redArg___closed__5;
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
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_309_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set(v___x_311_, 3, v___x_310_);
lean_ctor_set(v___x_311_, 4, v___x_309_);
lean_ctor_set(v___x_311_, 5, v___x_309_);
lean_ctor_set(v___x_311_, 6, v___x_309_);
lean_ctor_set(v___x_311_, 7, v___x_309_);
lean_ctor_set(v___x_311_, 8, v___x_309_);
lean_ctor_set(v___x_311_, 9, v___x_309_);
lean_ctor_set(v___x_311_, 10, v___x_309_);
lean_ctor_set(v___x_311_, 11, v___x_308_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_unsigned_to_nat(32u);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_315_ = ((size_t)5ULL);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_unsigned_to_nat(32u);
v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
v___x_319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_320_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_316_);
lean_ctor_set(v___x_320_, 3, v___x_316_);
lean_ctor_set_usize(v___x_320_, 4, v___x_315_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_321_ = lean_box(1);
v___x_322_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_323_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
lean_ctor_set(v___x_324_, 2, v___x_321_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_toCold_330_; lean_object* v_env_331_; lean_object* v_options_332_; uint8_t v___x_333_; lean_object* v_env_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_329_ = lean_st_ref_get(v___y_327_);
v_toCold_330_ = lean_ctor_get(v___y_326_, 0);
v_env_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_331_);
lean_dec(v___x_329_);
v_options_332_ = lean_ctor_get(v_toCold_330_, 2);
v___x_333_ = 0;
v_env_334_ = l_Lean_Environment_setRecordingDeps(v_env_331_, v___x_333_);
v___x_335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_332_);
v___x_337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_337_, 0, v_env_334_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v_options_332_);
v___x_338_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_msgData_325_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_ref_349_; lean_object* v___x_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
v_ref_349_ = lean_ctor_get(v___y_346_, 2);
v___x_350_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_345_, v___y_346_, v___y_347_);
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_359_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_inc(v_ref_349_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v_ref_349_);
lean_ctor_set(v___x_355_, 1, v_a_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 1);
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_364_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_374_, lean_object* v_reservedName_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_379_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_380_ = 0;
v___x_381_ = l_Lean_MessageData_ofConstName(v_declName_374_, v___x_380_);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_379_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = 1;
v___x_386_ = l_Lean_MessageData_ofConstName(v_reservedName_375_, v___x_385_);
v___x_387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_384_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_389_, v___y_376_, v___y_377_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_391_, lean_object* v_reservedName_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_391_, v_reservedName_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_397_, lean_object* v_suffix_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_reservedName_402_; lean_object* v___x_403_; lean_object* v_env_404_; uint8_t v___x_405_; uint8_t v___x_406_; 
lean_inc(v_declName_397_);
v_reservedName_402_ = l_Lean_Name_str___override(v_declName_397_, v_suffix_398_);
v___x_403_ = lean_st_ref_get(v___y_400_);
v_env_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_env_404_);
lean_dec(v___x_403_);
v___x_405_ = 1;
lean_inc(v_reservedName_402_);
v___x_406_ = l_Lean_Environment_contains(v_env_404_, v_reservedName_402_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec(v_reservedName_402_);
lean_dec(v_declName_397_);
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_397_, v_reservedName_402_, v___y_399_, v___y_400_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_410_, lean_object* v_suffix_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_410_, v_suffix_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_416_);
v___x_421_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_416_, v___x_420_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref_known(v___x_421_, 1);
v___x_422_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_416_);
v___x_423_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_416_, v___x_422_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref_known(v___x_423_, 1);
v___x_424_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_425_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_416_, v___x_424_, v_a_417_, v_a_418_);
return v___x_425_;
}
else
{
lean_dec(v_declName_416_);
return v___x_423_;
}
}
else
{
lean_dec(v_declName_416_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_431_, lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_432_, v___y_433_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_437_, v_msg_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_442_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_443_, lean_object* v_n_444_){
_start:
{
lean_object* v___x_445_; 
lean_inc(v_n_444_);
lean_inc_ref(v_env_443_);
v___x_445_ = l_Lean_Meta_declFromEqLikeName(v_env_443_, v_n_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_val_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_val_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_445_, 1);
v_fst_447_ = lean_ctor_get(v_val_446_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v_val_446_, 1);
lean_inc(v_snd_448_);
lean_dec(v_val_446_);
v___x_449_ = l_Lean_Meta_mkEqLikeNameFor(v_env_443_, v_fst_447_, v_snd_448_);
v___x_450_ = lean_name_eq(v_n_444_, v___x_449_);
lean_dec(v___x_449_);
lean_dec(v_n_444_);
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
lean_dec(v___x_445_);
lean_dec(v_n_444_);
lean_dec_ref(v_env_443_);
v___x_451_ = 0;
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_452_, lean_object* v_n_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_452_, v_n_453_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_458_; lean_object* v___x_459_; 
v___f_458_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_459_ = l_Lean_registerReservedNamePredicate(v___f_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_st_mk_ref(v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_470_ = lean_mk_io_user_error(v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_471_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_initializing();
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref(v_f_471_);
v___x_474_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_477_ = lean_st_ref_take(v___x_476_);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v_f_471_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = lean_st_ref_put(v___x_476_, v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_registerGetEqnsFn(v_f_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_494_; lean_object* v_env_495_; uint8_t v___x_496_; lean_object* v___x_497_; 
v___x_494_ = lean_st_ref_get(v_a_488_);
v_env_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc_ref(v_env_495_);
lean_dec(v___x_494_);
v___x_496_ = 0;
lean_inc(v_declName_484_);
v___x_497_ = l_Lean_Environment_findAsync_x3f(v_env_495_, v_declName_484_, v___x_496_);
if (lean_obj_tag(v___x_497_) == 1)
{
lean_object* v_val_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_529_; 
v_val_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_529_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_529_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_val_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_529_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v_kind_502_; 
v_kind_502_ = lean_ctor_get_uint8(v_val_498_, sizeof(void*)*3);
if (v_kind_502_ == 0)
{
lean_object* v_sig_503_; lean_object* v___x_504_; lean_object* v_env_505_; uint8_t v___x_506_; 
v_sig_503_ = lean_ctor_get(v_val_498_, 1);
lean_inc_ref(v_sig_503_);
lean_dec(v_val_498_);
v___x_504_ = lean_st_ref_get(v_a_488_);
v_env_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc_ref(v_env_505_);
lean_dec(v___x_504_);
v___x_506_ = l_Lean_Meta_isMatcherCore(v_env_505_, v_declName_484_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v_type_508_; lean_object* v___x_509_; 
lean_del_object(v___x_500_);
v___x_507_ = lean_task_get_own(v_sig_503_);
v_type_508_ = lean_ctor_get(v___x_507_, 2);
lean_inc_ref(v_type_508_);
lean_dec(v___x_507_);
v___x_509_ = l_Lean_Meta_isProp(v_type_508_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_524_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_524_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_524_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_524_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = lean_unbox(v_a_510_);
lean_dec(v_a_510_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = 1;
v___x_516_ = lean_box(v___x_515_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_box(v___x_506_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_520_);
v___x_522_ = v___x_512_;
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
}
}
else
{
return v___x_509_;
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec_ref(v_sig_503_);
v___x_525_ = lean_box(v___x_496_);
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 0);
lean_ctor_set(v___x_500_, 0, v___x_525_);
v___x_527_ = v___x_500_;
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
}
else
{
lean_del_object(v___x_500_);
lean_dec(v_val_498_);
lean_dec(v_declName_484_);
goto v___jp_490_;
}
}
}
else
{
lean_dec(v___x_497_);
lean_dec(v_declName_484_);
goto v___jp_490_;
}
v___jp_490_:
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = 0;
v___x_492_ = lean_box(v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_536_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(lean_object* v___x_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v___x_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(v___x_544_);
return v_res_546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_547_; lean_object* v___f_548_; 
v___x_547_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_548_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_548_, 0, v___x_547_);
return v___f_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___f_555_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_box(1);
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_));
v___x_559_ = 0;
v___x_560_ = 1;
v___x_561_ = l_Lean_registerEnvExtension___redArg(v___f_555_, v___x_556_, v___x_557_, v___x_558_, v___x_559_, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2____boxed(lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_222358314____hygCtx___hyg_2_();
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_564_, lean_object* v_opt_565_){
_start:
{
lean_object* v_name_566_; lean_object* v_defValue_567_; lean_object* v_map_568_; lean_object* v___x_569_; 
v_name_566_ = lean_ctor_get(v_opt_565_, 0);
v_defValue_567_ = lean_ctor_get(v_opt_565_, 1);
v_map_568_ = lean_ctor_get(v_opts_564_, 0);
v___x_569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_568_, v_name_566_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_inc(v_defValue_567_);
return v_defValue_567_;
}
else
{
lean_object* v_val_570_; 
v_val_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v___x_569_, 1);
if (lean_obj_tag(v_val_570_) == 3)
{
lean_object* v_v_571_; 
v_v_571_ = lean_ctor_get(v_val_570_, 0);
lean_inc(v_v_571_);
lean_dec_ref_known(v_val_570_, 1);
return v_v_571_;
}
else
{
lean_dec(v_val_570_);
lean_inc(v_defValue_567_);
return v_defValue_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_572_, lean_object* v_opt_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_572_, v_opt_573_);
lean_dec_ref(v_opt_573_);
lean_dec_ref(v_opts_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_578_, size_t v_sz_579_, size_t v_i_580_, lean_object* v_b_581_){
_start:
{
lean_object* v_a_583_; uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_lt(v_i_580_, v_sz_579_);
if (v___x_587_ == 0)
{
return v_b_581_;
}
else
{
lean_object* v_a_588_; lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v_map_591_; uint8_t v_hasTrace_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_605_; 
v_a_588_ = lean_array_uget_borrowed(v_as_578_, v_i_580_);
v_fst_589_ = lean_ctor_get(v_a_588_, 0);
v_snd_590_ = lean_ctor_get(v_a_588_, 1);
v_map_591_ = lean_ctor_get(v_b_581_, 0);
v_hasTrace_592_ = lean_ctor_get_uint8(v_b_581_, sizeof(void*)*1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_b_581_);
if (v_isSharedCheck_605_ == 0)
{
v___x_594_ = v_b_581_;
v_isShared_595_ = v_isSharedCheck_605_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_map_591_);
lean_dec(v_b_581_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_605_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; 
lean_inc(v_snd_590_);
lean_inc(v_fst_589_);
v___x_596_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_589_, v_snd_590_, v_map_591_);
if (v_hasTrace_592_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_600_; 
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_598_ = l_Lean_Name_isPrefixOf(v___x_597_, v_fst_589_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_600_ = v___x_594_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_596_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*1, v___x_598_);
v_a_583_ = v___x_600_;
goto v___jp_582_;
}
}
else
{
lean_object* v___x_603_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_603_ = v___x_594_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_596_);
lean_ctor_set_uint8(v_reuseFailAlloc_604_, sizeof(void*)*1, v_hasTrace_592_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
v_a_583_ = v___x_603_;
goto v___jp_582_;
}
}
}
}
v___jp_582_:
{
size_t v___x_584_; size_t v___x_585_; 
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_add(v_i_580_, v___x_584_);
v_i_580_ = v___x_585_;
v_b_581_ = v_a_583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_606_, lean_object* v_sz_607_, lean_object* v_i_608_, lean_object* v_b_609_){
_start:
{
size_t v_sz_boxed_610_; size_t v_i_boxed_611_; lean_object* v_res_612_; 
v_sz_boxed_610_ = lean_unbox_usize(v_sz_607_);
lean_dec(v_sz_607_);
v_i_boxed_611_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_606_, v_sz_boxed_610_, v_i_boxed_611_, v_b_609_);
lean_dec_ref(v_as_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_613_, lean_object* v_k_614_, uint8_t v_v_615_){
_start:
{
lean_object* v_map_616_; uint8_t v_hasTrace_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_631_; 
v_map_616_ = lean_ctor_get(v_o_613_, 0);
v_hasTrace_617_ = lean_ctor_get_uint8(v_o_613_, sizeof(void*)*1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_o_613_);
if (v_isSharedCheck_631_ == 0)
{
v___x_619_ = v_o_613_;
v_isShared_620_ = v_isSharedCheck_631_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_map_616_);
lean_dec(v_o_613_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_631_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_621_, 0, v_v_615_);
lean_inc(v_k_614_);
v___x_622_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_614_, v___x_621_, v_map_616_);
if (v_hasTrace_617_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; lean_object* v___x_626_; 
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_624_ = l_Lean_Name_isPrefixOf(v___x_623_, v_k_614_);
lean_dec(v_k_614_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_622_);
v___x_626_ = v___x_619_;
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
return v___x_626_;
}
}
else
{
lean_object* v___x_629_; 
lean_dec(v_k_614_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_622_);
v___x_629_ = v___x_619_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_622_);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, sizeof(void*)*1, v_hasTrace_617_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_632_, lean_object* v_k_633_, lean_object* v_v_634_){
_start:
{
uint8_t v_v_boxed_635_; lean_object* v_res_636_; 
v_v_boxed_635_ = lean_unbox(v_v_634_);
v_res_636_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_632_, v_k_633_, v_v_boxed_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_637_, lean_object* v_opt_638_, uint8_t v_val_639_){
_start:
{
lean_object* v_name_640_; lean_object* v___x_641_; 
v_name_640_ = lean_ctor_get(v_opt_638_, 0);
lean_inc(v_name_640_);
lean_dec_ref(v_opt_638_);
v___x_641_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_637_, v_name_640_, v_val_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_642_, lean_object* v_opt_643_, lean_object* v_val_644_){
_start:
{
uint8_t v_val_boxed_645_; lean_object* v_res_646_; 
v_val_boxed_645_ = lean_unbox(v_val_644_);
v_res_646_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_642_, v_opt_643_, v_val_boxed_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_647_, size_t v_i_648_, size_t v_stop_649_, lean_object* v_b_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_eq(v_i_648_, v_stop_649_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v_defValue_653_; uint8_t v___x_654_; lean_object* v___x_655_; size_t v___x_656_; size_t v___x_657_; 
v___x_652_ = lean_array_uget_borrowed(v_as_647_, v_i_648_);
v_defValue_653_ = lean_ctor_get(v___x_652_, 1);
v___x_654_ = lean_unbox(v_defValue_653_);
lean_inc(v___x_652_);
v___x_655_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_650_, v___x_652_, v___x_654_);
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_add(v_i_648_, v___x_656_);
v_i_648_ = v___x_657_;
v_b_650_ = v___x_655_;
goto _start;
}
else
{
return v_b_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_659_, lean_object* v_i_660_, lean_object* v_stop_661_, lean_object* v_b_662_){
_start:
{
size_t v_i_boxed_663_; size_t v_stop_boxed_664_; lean_object* v_res_665_; 
v_i_boxed_663_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_stop_boxed_664_ = lean_unbox_usize(v_stop_661_);
lean_dec(v_stop_661_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_659_, v_i_boxed_663_, v_stop_boxed_664_, v_b_662_);
lean_dec_ref(v_as_659_);
return v_res_665_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Array_instInhabited___redArg();
return v___x_670_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = l_Lean_Meta_eqnAffectingOptions;
v___x_672_ = lean_array_get_size(v___x_671_);
return v___x_672_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_nat_dec_lt(v___x_674_, v___x_673_);
return v___x_675_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_676_; size_t v___x_677_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_677_ = lean_usize_of_nat(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_678_, lean_object* v_act_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
uint16_t v___y_686_; lean_object* v___y_687_; lean_object* v_fileName_688_; lean_object* v_fileMap_689_; lean_object* v_currNamespace_690_; lean_object* v_openDecls_691_; lean_object* v_initHeartbeats_692_; lean_object* v_maxHeartbeats_693_; lean_object* v_quotContext_694_; lean_object* v_currMacroScope_695_; lean_object* v_cancelTk_x3f_696_; lean_object* v_inheritedTraceOptions_697_; lean_object* v_currRecDepth_698_; lean_object* v_ref_699_; uint8_t v_suppressElabErrors_700_; uint8_t v_isRecordingDeps_701_; lean_object* v___y_702_; uint16_t v___y_709_; uint8_t v___y_710_; lean_object* v___y_711_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_toCold_750_; lean_object* v_currRecDepth_751_; lean_object* v_ref_752_; uint8_t v_suppressElabErrors_753_; uint8_t v_isRecordingDeps_754_; lean_object* v_fileName_755_; lean_object* v_fileMap_756_; lean_object* v_options_757_; lean_object* v_currNamespace_758_; lean_object* v_openDecls_759_; lean_object* v_initHeartbeats_760_; lean_object* v_maxHeartbeats_761_; lean_object* v_quotContext_762_; lean_object* v_currMacroScope_763_; lean_object* v_cancelTk_x3f_764_; lean_object* v_inheritedTraceOptions_765_; lean_object* v___y_767_; 
v___x_748_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_749_ = lean_st_ref_get(v_a_683_);
v_toCold_750_ = lean_ctor_get(v_a_682_, 0);
v_currRecDepth_751_ = lean_ctor_get(v_a_682_, 1);
v_ref_752_ = lean_ctor_get(v_a_682_, 2);
v_suppressElabErrors_753_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 2);
v_isRecordingDeps_754_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 3);
v_fileName_755_ = lean_ctor_get(v_toCold_750_, 0);
v_fileMap_756_ = lean_ctor_get(v_toCold_750_, 1);
v_options_757_ = lean_ctor_get(v_toCold_750_, 2);
v_currNamespace_758_ = lean_ctor_get(v_toCold_750_, 4);
v_openDecls_759_ = lean_ctor_get(v_toCold_750_, 5);
v_initHeartbeats_760_ = lean_ctor_get(v_toCold_750_, 6);
v_maxHeartbeats_761_ = lean_ctor_get(v_toCold_750_, 7);
v_quotContext_762_ = lean_ctor_get(v_toCold_750_, 8);
v_currMacroScope_763_ = lean_ctor_get(v_toCold_750_, 9);
v_cancelTk_x3f_764_ = lean_ctor_get(v_toCold_750_, 10);
v_inheritedTraceOptions_765_ = lean_ctor_get(v_toCold_750_, 11);
if (v_isRecordingDeps_754_ == 0)
{
lean_object* v_env_778_; lean_object* v___x_779_; lean_object* v_toEnvExtension_780_; lean_object* v_asyncMode_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v_env_778_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_env_778_);
lean_dec(v___x_749_);
v___x_779_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_780_ = lean_ctor_get(v___x_779_, 0);
v_asyncMode_781_ = lean_ctor_get(v_toEnvExtension_780_, 2);
v___x_782_ = 0;
v___x_783_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_748_, v___x_779_, v_env_778_, v_declName_678_, v_asyncMode_781_, v___x_782_);
if (lean_obj_tag(v___x_783_) == 1)
{
lean_object* v_val_784_; lean_object* v___y_786_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_val_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_790_ = l_Lean_Meta_eqnAffectingOptions;
v___x_791_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
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
v___x_793_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
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
v___x_796_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
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
v___x_798_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
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
lean_dec(v___x_749_);
lean_dec(v_declName_678_);
lean_inc_ref(v_options_757_);
v___x_800_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_757_);
v___y_767_ = v___x_800_;
goto v___jp_766_;
}
v___jp_685_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_703_ = l_Lean_maxRecDepth;
v___x_704_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_687_, v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_705_, 0, v_fileName_688_);
lean_ctor_set(v___x_705_, 1, v_fileMap_689_);
lean_ctor_set(v___x_705_, 2, v___y_687_);
lean_ctor_set(v___x_705_, 3, v___x_704_);
lean_ctor_set(v___x_705_, 4, v_currNamespace_690_);
lean_ctor_set(v___x_705_, 5, v_openDecls_691_);
lean_ctor_set(v___x_705_, 6, v_initHeartbeats_692_);
lean_ctor_set(v___x_705_, 7, v_maxHeartbeats_693_);
lean_ctor_set(v___x_705_, 8, v_quotContext_694_);
lean_ctor_set(v___x_705_, 9, v_currMacroScope_695_);
lean_ctor_set(v___x_705_, 10, v_cancelTk_x3f_696_);
lean_ctor_set(v___x_705_, 11, v_inheritedTraceOptions_697_);
lean_inc(v_ref_699_);
lean_inc(v_currRecDepth_698_);
v___x_706_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_currRecDepth_698_);
lean_ctor_set(v___x_706_, 2, v_ref_699_);
lean_ctor_set_uint16(v___x_706_, sizeof(void*)*3, v___y_686_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3 + 2, v_suppressElabErrors_700_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3 + 3, v_isRecordingDeps_701_);
lean_inc(v___y_702_);
lean_inc(v_a_681_);
lean_inc_ref(v_a_680_);
v___x_707_ = lean_apply_5(v_act_679_, v_a_680_, v_a_681_, v___x_706_, v___y_702_, lean_box(0));
return v___x_707_;
}
v___jp_708_:
{
lean_object* v___x_712_; lean_object* v_env_713_; lean_object* v_nextMacroScope_714_; lean_object* v_ngen_715_; lean_object* v_auxDeclNGen_716_; lean_object* v_traceState_717_; lean_object* v_recordedDeps_718_; lean_object* v_messages_719_; lean_object* v_infoState_720_; lean_object* v_snapshotTasks_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_746_; 
v___x_712_ = lean_st_ref_take(v_a_683_);
v_env_713_ = lean_ctor_get(v___x_712_, 0);
v_nextMacroScope_714_ = lean_ctor_get(v___x_712_, 1);
v_ngen_715_ = lean_ctor_get(v___x_712_, 2);
v_auxDeclNGen_716_ = lean_ctor_get(v___x_712_, 3);
v_traceState_717_ = lean_ctor_get(v___x_712_, 4);
v_recordedDeps_718_ = lean_ctor_get(v___x_712_, 6);
v_messages_719_ = lean_ctor_get(v___x_712_, 7);
v_infoState_720_ = lean_ctor_get(v___x_712_, 8);
v_snapshotTasks_721_ = lean_ctor_get(v___x_712_, 9);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v___x_712_, 5);
lean_dec(v_unused_747_);
v___x_723_ = v___x_712_;
v_isShared_724_ = v_isSharedCheck_746_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snapshotTasks_721_);
lean_inc(v_infoState_720_);
lean_inc(v_messages_719_);
lean_inc(v_recordedDeps_718_);
lean_inc(v_traceState_717_);
lean_inc(v_auxDeclNGen_716_);
lean_inc(v_ngen_715_);
lean_inc(v_nextMacroScope_714_);
lean_inc(v_env_713_);
lean_dec(v___x_712_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_746_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = l_Lean_Kernel_enableDiag(v_env_713_, v___y_710_);
v___x_726_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 5, v___x_726_);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_nextMacroScope_714_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_ngen_715_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_auxDeclNGen_716_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_traceState_717_);
lean_ctor_set(v_reuseFailAlloc_745_, 5, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_745_, 6, v_recordedDeps_718_);
lean_ctor_set(v_reuseFailAlloc_745_, 7, v_messages_719_);
lean_ctor_set(v_reuseFailAlloc_745_, 8, v_infoState_720_);
lean_ctor_set(v_reuseFailAlloc_745_, 9, v_snapshotTasks_721_);
v___x_728_ = v_reuseFailAlloc_745_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v_toCold_730_; lean_object* v_currRecDepth_731_; lean_object* v_ref_732_; uint8_t v_suppressElabErrors_733_; uint8_t v_isRecordingDeps_734_; lean_object* v_fileName_735_; lean_object* v_fileMap_736_; lean_object* v_currNamespace_737_; lean_object* v_openDecls_738_; lean_object* v_initHeartbeats_739_; lean_object* v_maxHeartbeats_740_; lean_object* v_quotContext_741_; lean_object* v_currMacroScope_742_; lean_object* v_cancelTk_x3f_743_; lean_object* v_inheritedTraceOptions_744_; 
v___x_729_ = lean_st_ref_put(v_a_683_, v___x_728_);
v_toCold_730_ = lean_ctor_get(v_a_682_, 0);
v_currRecDepth_731_ = lean_ctor_get(v_a_682_, 1);
v_ref_732_ = lean_ctor_get(v_a_682_, 2);
v_suppressElabErrors_733_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 2);
v_isRecordingDeps_734_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 3);
v_fileName_735_ = lean_ctor_get(v_toCold_730_, 0);
v_fileMap_736_ = lean_ctor_get(v_toCold_730_, 1);
v_currNamespace_737_ = lean_ctor_get(v_toCold_730_, 4);
v_openDecls_738_ = lean_ctor_get(v_toCold_730_, 5);
v_initHeartbeats_739_ = lean_ctor_get(v_toCold_730_, 6);
v_maxHeartbeats_740_ = lean_ctor_get(v_toCold_730_, 7);
v_quotContext_741_ = lean_ctor_get(v_toCold_730_, 8);
v_currMacroScope_742_ = lean_ctor_get(v_toCold_730_, 9);
v_cancelTk_x3f_743_ = lean_ctor_get(v_toCold_730_, 10);
v_inheritedTraceOptions_744_ = lean_ctor_get(v_toCold_730_, 11);
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
v___y_686_ = v___y_709_;
v___y_687_ = v___y_711_;
v_fileName_688_ = v_fileName_735_;
v_fileMap_689_ = v_fileMap_736_;
v_currNamespace_690_ = v_currNamespace_737_;
v_openDecls_691_ = v_openDecls_738_;
v_initHeartbeats_692_ = v_initHeartbeats_739_;
v_maxHeartbeats_693_ = v_maxHeartbeats_740_;
v_quotContext_694_ = v_quotContext_741_;
v_currMacroScope_695_ = v_currMacroScope_742_;
v_cancelTk_x3f_696_ = v_cancelTk_x3f_743_;
v_inheritedTraceOptions_697_ = v_inheritedTraceOptions_744_;
v_currRecDepth_698_ = v_currRecDepth_731_;
v_ref_699_ = v_ref_732_;
v_suppressElabErrors_700_ = v_suppressElabErrors_733_;
v_isRecordingDeps_701_ = v_isRecordingDeps_734_;
v___y_702_ = v_a_683_;
goto v___jp_685_;
}
}
}
v___jp_766_:
{
uint16_t v___x_768_; lean_object* v___x_769_; lean_object* v_env_770_; uint8_t v___x_771_; uint16_t v___x_772_; uint16_t v___x_773_; uint16_t v___x_774_; uint8_t v___x_775_; 
v___x_768_ = l_Lean_OptionFlags_ofOptions(v___y_767_);
v___x_769_ = lean_st_ref_get(v_a_683_);
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
v___y_709_ = v___x_768_;
v___y_710_ = v___x_776_;
v___y_711_ = v___y_767_;
goto v___jp_708_;
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
v___y_686_ = v___x_768_;
v___y_687_ = v___y_767_;
v_fileName_688_ = v_fileName_755_;
v_fileMap_689_ = v_fileMap_756_;
v_currNamespace_690_ = v_currNamespace_758_;
v_openDecls_691_ = v_openDecls_759_;
v_initHeartbeats_692_ = v_initHeartbeats_760_;
v_maxHeartbeats_693_ = v_maxHeartbeats_761_;
v_quotContext_694_ = v_quotContext_762_;
v_currMacroScope_695_ = v_currMacroScope_763_;
v_cancelTk_x3f_696_ = v_cancelTk_x3f_764_;
v_inheritedTraceOptions_697_ = v_inheritedTraceOptions_765_;
v_currRecDepth_698_ = v_currRecDepth_751_;
v_ref_699_ = v_ref_752_;
v_suppressElabErrors_700_ = v_suppressElabErrors_753_;
v_isRecordingDeps_701_ = v_isRecordingDeps_754_;
v___y_702_ = v_a_683_;
goto v___jp_685_;
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
v___y_686_ = v___x_768_;
v___y_687_ = v___y_767_;
v_fileName_688_ = v_fileName_755_;
v_fileMap_689_ = v_fileMap_756_;
v_currNamespace_690_ = v_currNamespace_758_;
v_openDecls_691_ = v_openDecls_759_;
v_initHeartbeats_692_ = v_initHeartbeats_760_;
v_maxHeartbeats_693_ = v_maxHeartbeats_761_;
v_quotContext_694_ = v_quotContext_762_;
v_currMacroScope_695_ = v_currMacroScope_763_;
v_cancelTk_x3f_696_ = v_cancelTk_x3f_764_;
v_inheritedTraceOptions_697_ = v_inheritedTraceOptions_765_;
v_currRecDepth_698_ = v_currRecDepth_751_;
v_ref_699_ = v_ref_752_;
v_suppressElabErrors_700_ = v_suppressElabErrors_753_;
v_isRecordingDeps_701_ = v_isRecordingDeps_754_;
v___y_702_ = v_a_683_;
goto v___jp_685_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = 0;
v___y_709_ = v___x_768_;
v___y_710_ = v___x_777_;
v___y_711_ = v___y_767_;
goto v___jp_708_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1710_, lean_object* v_a_1711_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1744_, v_a_1745_);
lean_dec(v_a_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1748_, v_a_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
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
v___x_1880_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1864_, v___y_1868_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; lean_object* v_env_2051_; uint8_t v___x_2052_; lean_object* v_env_2053_; lean_object* v___x_2054_; lean_object* v_toCold_2055_; lean_object* v_mctx_2056_; lean_object* v_lctx_2057_; lean_object* v_options_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2050_ = lean_st_ref_get(v___y_2048_);
v_env_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc_ref(v_env_2051_);
lean_dec(v___x_2050_);
v___x_2052_ = 0;
v_env_2053_ = l_Lean_Environment_setRecordingDeps(v_env_2051_, v___x_2052_);
v___x_2054_ = lean_st_ref_get(v___y_2046_);
v_toCold_2055_ = lean_ctor_get(v___y_2047_, 0);
v_mctx_2056_ = lean_ctor_get(v___x_2054_, 0);
lean_inc_ref(v_mctx_2056_);
lean_dec(v___x_2054_);
v_lctx_2057_ = lean_ctor_get(v___y_2045_, 2);
v_options_2058_ = lean_ctor_get(v_toCold_2055_, 2);
lean_inc_ref(v_options_2058_);
lean_inc_ref(v_lctx_2057_);
v___x_2059_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2059_, 0, v_env_2053_);
lean_ctor_set(v___x_2059_, 1, v_mctx_2056_);
lean_ctor_set(v___x_2059_, 2, v_lctx_2057_);
lean_ctor_set(v___x_2059_, 3, v_options_2058_);
v___x_2060_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v_msgData_2044_);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2068_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2069_; double v___x_2070_; 
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_float_of_nat(v___x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2074_, lean_object* v_msg_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_ref_2081_; lean_object* v___x_2082_; lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2128_; 
v_ref_2081_ = lean_ctor_get(v___y_2078_, 2);
v___x_2082_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2128_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2128_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v_traceState_2088_; lean_object* v_env_2089_; lean_object* v_nextMacroScope_2090_; lean_object* v_ngen_2091_; lean_object* v_auxDeclNGen_2092_; lean_object* v_cache_2093_; lean_object* v_recordedDeps_2094_; lean_object* v_messages_2095_; lean_object* v_infoState_2096_; lean_object* v_snapshotTasks_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2127_; 
v___x_2087_ = lean_st_ref_take(v___y_2079_);
v_traceState_2088_ = lean_ctor_get(v___x_2087_, 4);
v_env_2089_ = lean_ctor_get(v___x_2087_, 0);
v_nextMacroScope_2090_ = lean_ctor_get(v___x_2087_, 1);
v_ngen_2091_ = lean_ctor_get(v___x_2087_, 2);
v_auxDeclNGen_2092_ = lean_ctor_get(v___x_2087_, 3);
v_cache_2093_ = lean_ctor_get(v___x_2087_, 5);
v_recordedDeps_2094_ = lean_ctor_get(v___x_2087_, 6);
v_messages_2095_ = lean_ctor_get(v___x_2087_, 7);
v_infoState_2096_ = lean_ctor_get(v___x_2087_, 8);
v_snapshotTasks_2097_ = lean_ctor_get(v___x_2087_, 9);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2099_ = v___x_2087_;
v_isShared_2100_ = v_isSharedCheck_2127_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_snapshotTasks_2097_);
lean_inc(v_infoState_2096_);
lean_inc(v_messages_2095_);
lean_inc(v_recordedDeps_2094_);
lean_inc(v_cache_2093_);
lean_inc(v_traceState_2088_);
lean_inc(v_auxDeclNGen_2092_);
lean_inc(v_ngen_2091_);
lean_inc(v_nextMacroScope_2090_);
lean_inc(v_env_2089_);
lean_dec(v___x_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2127_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
uint64_t v_tid_2101_; lean_object* v_traces_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2126_; 
v_tid_2101_ = lean_ctor_get_uint64(v_traceState_2088_, sizeof(void*)*1);
v_traces_2102_ = lean_ctor_get(v_traceState_2088_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_traceState_2088_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2104_ = v_traceState_2088_;
v_isShared_2105_ = v_isSharedCheck_2126_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_traces_2102_);
lean_dec(v_traceState_2088_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2126_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; double v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_box(0);
v___x_2108_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2109_ = 0;
v___x_2110_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2111_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2111_, 0, v_cls_2074_);
lean_ctor_set(v___x_2111_, 1, v___x_2107_);
lean_ctor_set(v___x_2111_, 2, v___x_2110_);
lean_ctor_set_float(v___x_2111_, sizeof(void*)*3, v___x_2108_);
lean_ctor_set_float(v___x_2111_, sizeof(void*)*3 + 8, v___x_2108_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*3 + 16, v___x_2109_);
v___x_2112_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2113_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v_a_2083_);
lean_ctor_set(v___x_2113_, 2, v___x_2112_);
lean_inc(v_ref_2081_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_ref_2081_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_PersistentArray_push___redArg(v_traces_2102_, v___x_2114_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2115_);
v___x_2117_ = v___x_2104_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2115_);
lean_ctor_set_uint64(v_reuseFailAlloc_2125_, sizeof(void*)*1, v_tid_2101_);
v___x_2117_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2119_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v___x_2117_);
v___x_2119_ = v___x_2099_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_env_2089_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_nextMacroScope_2090_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_ngen_2091_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_auxDeclNGen_2092_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_cache_2093_);
lean_ctor_set(v_reuseFailAlloc_2124_, 6, v_recordedDeps_2094_);
lean_ctor_set(v_reuseFailAlloc_2124_, 7, v_messages_2095_);
lean_ctor_set(v_reuseFailAlloc_2124_, 8, v_infoState_2096_);
lean_ctor_set(v_reuseFailAlloc_2124_, 9, v_snapshotTasks_2097_);
v___x_2119_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_st_ref_put(v___y_2079_, v___x_2119_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2106_);
v___x_2122_ = v___x_2085_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2106_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2129_, lean_object* v_msg_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2129_, v_msg_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2136_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2139_; size_t v_sz_2140_; 
v___x_2139_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2140_ = lean_array_size(v___x_2139_);
return v_sz_2140_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2142_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
lean_ctor_set(v___x_2142_, 2, v___x_2141_);
lean_ctor_set(v___x_2142_, 3, v___x_2141_);
lean_ctor_set(v___x_2142_, 4, v___x_2141_);
lean_ctor_set(v___x_2142_, 5, v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2151_ = l_Lean_Name_append(v___x_2150_, v___x_2149_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2161_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2158_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2164_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2165_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2161_, v___x_2164_, v_sz_2165_, v___x_2166_, v___x_2163_);
lean_dec_ref(v___x_2161_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2231_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2231_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2231_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___y_2175_; lean_object* v___y_2176_; 
v___x_2172_ = lean_array_get_size(v_a_2168_);
v___x_2173_ = lean_nat_dec_eq(v___x_2172_, v___x_2162_);
if (v___x_2173_ == 0)
{
lean_object* v_toCold_2218_; lean_object* v_options_2219_; uint8_t v_hasTrace_2220_; 
v_toCold_2218_ = lean_ctor_get(v_a_2158_, 0);
v_options_2219_ = lean_ctor_get(v_toCold_2218_, 2);
v_hasTrace_2220_ = lean_ctor_get_uint8(v_options_2219_, sizeof(void*)*1);
if (v_hasTrace_2220_ == 0)
{
v___y_2175_ = v_a_2157_;
v___y_2176_ = v_a_2159_;
goto v___jp_2174_;
}
else
{
lean_object* v_inheritedTraceOptions_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_inheritedTraceOptions_2221_ = lean_ctor_get(v_toCold_2218_, 11);
v___x_2222_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2223_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2221_, v_options_2219_, v___x_2223_);
if (v___x_2224_ == 0)
{
v___y_2175_ = v_a_2157_;
v___y_2176_ = v_a_2159_;
goto v___jp_2174_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2155_);
v___x_2226_ = l_Lean_MessageData_ofName(v_declName_2155_);
v___x_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2222_, v___x_2227_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_dec_ref_known(v___x_2228_, 1);
v___y_2175_ = v_a_2157_;
v___y_2176_ = v_a_2159_;
goto v___jp_2174_;
}
else
{
lean_del_object(v___x_2170_);
lean_dec(v_a_2168_);
lean_dec(v_declName_2155_);
return v___x_2228_;
}
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_del_object(v___x_2170_);
lean_dec(v_a_2168_);
lean_dec(v_declName_2155_);
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
v___jp_2174_:
{
lean_object* v___x_2177_; lean_object* v_env_2178_; lean_object* v_nextMacroScope_2179_; lean_object* v_ngen_2180_; lean_object* v_auxDeclNGen_2181_; lean_object* v_traceState_2182_; lean_object* v_recordedDeps_2183_; lean_object* v_messages_2184_; lean_object* v_infoState_2185_; lean_object* v_snapshotTasks_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2216_; 
v___x_2177_ = lean_st_ref_take(v___y_2176_);
v_env_2178_ = lean_ctor_get(v___x_2177_, 0);
v_nextMacroScope_2179_ = lean_ctor_get(v___x_2177_, 1);
v_ngen_2180_ = lean_ctor_get(v___x_2177_, 2);
v_auxDeclNGen_2181_ = lean_ctor_get(v___x_2177_, 3);
v_traceState_2182_ = lean_ctor_get(v___x_2177_, 4);
v_recordedDeps_2183_ = lean_ctor_get(v___x_2177_, 6);
v_messages_2184_ = lean_ctor_get(v___x_2177_, 7);
v_infoState_2185_ = lean_ctor_get(v___x_2177_, 8);
v_snapshotTasks_2186_ = lean_ctor_get(v___x_2177_, 9);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2177_, 5);
lean_dec(v_unused_2217_);
v___x_2188_ = v___x_2177_;
v_isShared_2189_ = v_isSharedCheck_2216_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_snapshotTasks_2186_);
lean_inc(v_infoState_2185_);
lean_inc(v_messages_2184_);
lean_inc(v_recordedDeps_2183_);
lean_inc(v_traceState_2182_);
lean_inc(v_auxDeclNGen_2181_);
lean_inc(v_ngen_2180_);
lean_inc(v_nextMacroScope_2179_);
lean_inc(v_env_2178_);
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2216_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2190_ = l_Lean_Meta_eqnOptionsExt;
v___x_2191_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2190_, v_env_2178_, v_declName_2155_, v_a_2168_, v___x_2173_);
v___x_2192_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 5, v___x_2192_);
lean_ctor_set(v___x_2188_, 0, v___x_2191_);
v___x_2194_ = v___x_2188_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_nextMacroScope_2179_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_ngen_2180_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_auxDeclNGen_2181_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_traceState_2182_);
lean_ctor_set(v_reuseFailAlloc_2215_, 5, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2215_, 6, v_recordedDeps_2183_);
lean_ctor_set(v_reuseFailAlloc_2215_, 7, v_messages_2184_);
lean_ctor_set(v_reuseFailAlloc_2215_, 8, v_infoState_2185_);
lean_ctor_set(v_reuseFailAlloc_2215_, 9, v_snapshotTasks_2186_);
v___x_2194_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_mctx_2197_; lean_object* v_zetaDeltaFVarIds_2198_; lean_object* v_postponed_2199_; lean_object* v_diag_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2213_; 
v___x_2195_ = lean_st_ref_put(v___y_2176_, v___x_2194_);
v___x_2196_ = lean_st_ref_take(v___y_2175_);
v_mctx_2197_ = lean_ctor_get(v___x_2196_, 0);
v_zetaDeltaFVarIds_2198_ = lean_ctor_get(v___x_2196_, 2);
v_postponed_2199_ = lean_ctor_get(v___x_2196_, 3);
v_diag_2200_ = lean_ctor_get(v___x_2196_, 4);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v___x_2196_, 1);
lean_dec(v_unused_2214_);
v___x_2202_ = v___x_2196_;
v_isShared_2203_ = v_isSharedCheck_2213_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_diag_2200_);
lean_inc(v_postponed_2199_);
lean_inc(v_zetaDeltaFVarIds_2198_);
lean_inc(v_mctx_2197_);
lean_dec(v___x_2196_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2213_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2204_ = lean_box(0);
v___x_2205_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 1, v___x_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_mctx_2197_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_zetaDeltaFVarIds_2198_);
lean_ctor_set(v_reuseFailAlloc_2212_, 3, v_postponed_2199_);
lean_ctor_set(v_reuseFailAlloc_2212_, 4, v_diag_2200_);
v___x_2207_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_st_ref_put(v___y_2175_, v___x_2207_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2204_);
v___x_2210_ = v___x_2170_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2204_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
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
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_declName_2155_);
v_a_2232_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2167_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2167_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2247_, lean_object* v_as_2248_, size_t v_sz_2249_, size_t v_i_2250_, lean_object* v_b_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2247_, v_as_2248_, v_sz_2249_, v_i_2250_, v_b_2251_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2258_, lean_object* v_as_2259_, lean_object* v_sz_2260_, lean_object* v_i_2261_, lean_object* v_b_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
size_t v_sz_boxed_2268_; size_t v_i_boxed_2269_; lean_object* v_res_2270_; 
v_sz_boxed_2268_ = lean_unbox_usize(v_sz_2260_);
lean_dec(v_sz_2260_);
v_i_boxed_2269_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_res_2270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2258_, v_as_2259_, v_sz_boxed_2268_, v_i_boxed_2269_, v_b_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_as_2259_);
lean_dec_ref(v___x_2258_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_st_mk_ref(v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2277_){
_start:
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Lean_initializing();
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_dec_ref(v_f_2277_);
v___x_2280_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2282_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2283_ = lean_st_ref_take(v___x_2282_);
v___x_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2284_, 0, v_f_2277_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_st_ref_put(v___x_2282_, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2293_, lean_object* v_as_x27_2294_, lean_object* v_b_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
if (lean_obj_tag(v_as_x27_2294_) == 0)
{
lean_object* v___x_2301_; 
lean_dec(v_declName_2293_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_b_2295_);
return v___x_2301_;
}
else
{
lean_object* v_head_2302_; lean_object* v_tail_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec_ref(v_b_2295_);
v_head_2302_ = lean_ctor_get(v_as_x27_2294_, 0);
v_tail_2303_ = lean_ctor_get(v_as_x27_2294_, 1);
v___x_2304_ = lean_box(0);
v___x_2305_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2302_);
lean_inc(v___y_2299_);
lean_inc_ref(v___y_2298_);
lean_inc(v___y_2297_);
lean_inc_ref(v___y_2296_);
lean_inc(v_declName_2293_);
v___x_2306_ = lean_apply_6(v_head_2302_, v_declName_2293_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, lean_box(0));
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2317_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2317_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2317_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
if (lean_obj_tag(v_a_2307_) == 1)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
lean_dec(v_declName_2293_);
v___x_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2311_, 0, v_a_2307_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2304_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2312_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
else
{
lean_del_object(v___x_2309_);
lean_dec(v_a_2307_);
v_as_x27_2294_ = v_tail_2303_;
v_b_2295_ = v___x_2305_;
goto _start;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_declName_2293_);
v_a_2318_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2306_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2306_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2326_, lean_object* v_as_x27_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2326_, v_as_x27_2327_, v_b_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_as_x27_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2335_, lean_object* v_declName_2336_, uint8_t v_nonRec_2337_, lean_object* v___x_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2347_; lean_object* v_env_2348_; uint8_t v___x_2349_; uint8_t v___x_2350_; 
v___x_2347_ = lean_st_ref_get(v___y_2342_);
v_env_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc_ref(v_env_2348_);
lean_dec(v___x_2347_);
v___x_2349_ = 1;
lean_inc(v___x_2335_);
v___x_2350_ = l_Lean_Environment_contains(v_env_2348_, v___x_2335_, v___x_2349_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec(v___x_2335_);
lean_inc(v_declName_2336_);
v___x_2351_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2336_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; uint8_t v___x_2353_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = lean_unbox(v_a_2352_);
lean_dec(v_a_2352_);
if (v___x_2353_ == 0)
{
lean_dec_ref(v___x_2338_);
lean_dec(v_declName_2336_);
goto v___jp_2344_;
}
else
{
lean_object* v___x_2354_; 
lean_inc(v_declName_2336_);
v___x_2354_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2336_, v___y_2342_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; uint8_t v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = lean_unbox(v_a_2355_);
lean_dec(v_a_2355_);
if (v___x_2356_ == 0)
{
if (v_nonRec_2337_ == 0)
{
lean_dec_ref(v___x_2338_);
lean_dec(v_declName_2336_);
goto v___jp_2344_;
}
else
{
lean_object* v___x_2357_; lean_object* v_env_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2357_ = lean_st_ref_get(v___y_2342_);
v_env_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc_ref(v_env_2358_);
lean_dec(v___x_2357_);
lean_inc(v_declName_2336_);
v___x_2359_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2358_, v_declName_2336_, v___x_2338_);
v___x_2360_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2336_, v___x_2359_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2360_;
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v___x_2338_);
v___x_2361_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2362_ = lean_st_ref_get(v___x_2361_);
v___x_2363_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2364_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2336_, v___x_2362_, v___x_2363_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___x_2362_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2374_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2374_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2374_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v_fst_2369_; 
v_fst_2369_ = lean_ctor_get(v_a_2365_, 0);
lean_inc(v_fst_2369_);
lean_dec(v_a_2365_);
if (lean_obj_tag(v_fst_2369_) == 0)
{
lean_del_object(v___x_2367_);
goto v___jp_2344_;
}
else
{
lean_object* v_val_2370_; lean_object* v___x_2372_; 
v_val_2370_ = lean_ctor_get(v_fst_2369_, 0);
lean_inc(v_val_2370_);
lean_dec_ref_known(v_fst_2369_, 1);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v_val_2370_);
v___x_2372_ = v___x_2367_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_val_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v_a_2375_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2364_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2364_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v___x_2338_);
lean_dec(v_declName_2336_);
v_a_2383_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2354_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2354_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v___x_2338_);
lean_dec(v_declName_2336_);
v_a_2391_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2351_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2351_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v___x_2338_);
lean_dec(v_declName_2336_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2335_);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
v___jp_2344_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2401_, lean_object* v_declName_2402_, lean_object* v_nonRec_2403_, lean_object* v___x_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v_nonRec_boxed_2410_; lean_object* v_res_2411_; 
v_nonRec_boxed_2410_ = lean_unbox(v_nonRec_2403_);
v_res_2411_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2401_, v_declName_2402_, v_nonRec_boxed_2410_, v___x_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_ref_2418_; lean_object* v___x_2419_; lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2428_; 
v_ref_2418_ = lean_ctor_get(v___y_2415_, 2);
v___x_2419_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_inc(v_ref_2418_);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_ref_2418_);
lean_ctor_set(v___x_2424_, 1, v_a_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2424_);
v___x_2426_ = v___x_2422_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2436_, uint8_t v_isExporting_2437_, lean_object* v___x_2438_, lean_object* v___y_2439_, lean_object* v___x_2440_, lean_object* v_a_x3f_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v_env_2444_; lean_object* v_nextMacroScope_2445_; lean_object* v_ngen_2446_; lean_object* v_auxDeclNGen_2447_; lean_object* v_traceState_2448_; lean_object* v_recordedDeps_2449_; lean_object* v_messages_2450_; lean_object* v_infoState_2451_; lean_object* v_snapshotTasks_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2477_; 
v___x_2443_ = lean_st_ref_take(v___y_2436_);
v_env_2444_ = lean_ctor_get(v___x_2443_, 0);
v_nextMacroScope_2445_ = lean_ctor_get(v___x_2443_, 1);
v_ngen_2446_ = lean_ctor_get(v___x_2443_, 2);
v_auxDeclNGen_2447_ = lean_ctor_get(v___x_2443_, 3);
v_traceState_2448_ = lean_ctor_get(v___x_2443_, 4);
v_recordedDeps_2449_ = lean_ctor_get(v___x_2443_, 6);
v_messages_2450_ = lean_ctor_get(v___x_2443_, 7);
v_infoState_2451_ = lean_ctor_get(v___x_2443_, 8);
v_snapshotTasks_2452_ = lean_ctor_get(v___x_2443_, 9);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2443_, 5);
lean_dec(v_unused_2478_);
v___x_2454_ = v___x_2443_;
v_isShared_2455_ = v_isSharedCheck_2477_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_snapshotTasks_2452_);
lean_inc(v_infoState_2451_);
lean_inc(v_messages_2450_);
lean_inc(v_recordedDeps_2449_);
lean_inc(v_traceState_2448_);
lean_inc(v_auxDeclNGen_2447_);
lean_inc(v_ngen_2446_);
lean_inc(v_nextMacroScope_2445_);
lean_inc(v_env_2444_);
lean_dec(v___x_2443_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2477_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2456_ = l_Lean_Environment_setExporting(v_env_2444_, v_isExporting_2437_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 5, v___x_2438_);
lean_ctor_set(v___x_2454_, 0, v___x_2456_);
v___x_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_nextMacroScope_2445_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_ngen_2446_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_auxDeclNGen_2447_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_traceState_2448_);
lean_ctor_set(v_reuseFailAlloc_2476_, 5, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2476_, 6, v_recordedDeps_2449_);
lean_ctor_set(v_reuseFailAlloc_2476_, 7, v_messages_2450_);
lean_ctor_set(v_reuseFailAlloc_2476_, 8, v_infoState_2451_);
lean_ctor_set(v_reuseFailAlloc_2476_, 9, v_snapshotTasks_2452_);
v___x_2458_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_mctx_2461_; lean_object* v_zetaDeltaFVarIds_2462_; lean_object* v_postponed_2463_; lean_object* v_diag_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2474_; 
v___x_2459_ = lean_st_ref_put(v___y_2436_, v___x_2458_);
v___x_2460_ = lean_st_ref_take(v___y_2439_);
v_mctx_2461_ = lean_ctor_get(v___x_2460_, 0);
v_zetaDeltaFVarIds_2462_ = lean_ctor_get(v___x_2460_, 2);
v_postponed_2463_ = lean_ctor_get(v___x_2460_, 3);
v_diag_2464_ = lean_ctor_get(v___x_2460_, 4);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2460_, 1);
lean_dec(v_unused_2475_);
v___x_2466_ = v___x_2460_;
v_isShared_2467_ = v_isSharedCheck_2474_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_diag_2464_);
lean_inc(v_postponed_2463_);
lean_inc(v_zetaDeltaFVarIds_2462_);
lean_inc(v_mctx_2461_);
lean_dec(v___x_2460_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2474_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = lean_box(0);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2440_);
v___x_2470_ = v___x_2466_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_mctx_2461_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_zetaDeltaFVarIds_2462_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_postponed_2463_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v_diag_2464_);
v___x_2470_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_st_ref_put(v___y_2439_, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2468_);
return v___x_2472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2479_, lean_object* v_isExporting_2480_, lean_object* v___x_2481_, lean_object* v___y_2482_, lean_object* v___x_2483_, lean_object* v_a_x3f_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v_isExporting_boxed_2486_; lean_object* v_res_2487_; 
v_isExporting_boxed_2486_ = lean_unbox(v_isExporting_2480_);
v_res_2487_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2479_, v_isExporting_boxed_2486_, v___x_2481_, v___y_2482_, v___x_2483_, v_a_x3f_2484_);
lean_dec(v_a_x3f_2484_);
lean_dec(v___y_2482_);
lean_dec(v___y_2479_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2488_, uint8_t v_isExporting_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v_env_2496_; lean_object* v___x_2497_; uint8_t v_isModule_2498_; 
v___x_2495_ = lean_st_ref_get(v___y_2493_);
v_env_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc_ref(v_env_2496_);
lean_dec(v___x_2495_);
v___x_2497_ = l_Lean_Environment_header(v_env_2496_);
v_isModule_2498_ = lean_ctor_get_uint8(v___x_2497_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2497_);
if (v_isModule_2498_ == 0)
{
lean_object* v___x_2499_; 
lean_dec_ref(v_env_2496_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2499_ = lean_apply_5(v_x_2488_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
return v___x_2499_;
}
else
{
uint8_t v_isExporting_2500_; 
v_isExporting_2500_ = lean_ctor_get_uint8(v_env_2496_, sizeof(void*)*13);
lean_dec_ref(v_env_2496_);
if (v_isExporting_2489_ == 0)
{
if (v_isExporting_2500_ == 0)
{
lean_object* v___x_2567_; 
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2567_ = lean_apply_5(v_x_2488_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
return v___x_2567_;
}
else
{
goto v___jp_2501_;
}
}
else
{
if (v_isExporting_2500_ == 0)
{
goto v___jp_2501_;
}
else
{
lean_object* v___x_2568_; 
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2568_ = lean_apply_5(v_x_2488_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
return v___x_2568_;
}
}
v___jp_2501_:
{
lean_object* v___x_2502_; lean_object* v_env_2503_; lean_object* v_nextMacroScope_2504_; lean_object* v_ngen_2505_; lean_object* v_auxDeclNGen_2506_; lean_object* v_traceState_2507_; lean_object* v_recordedDeps_2508_; lean_object* v_messages_2509_; lean_object* v_infoState_2510_; lean_object* v_snapshotTasks_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2565_; 
v___x_2502_ = lean_st_ref_take(v___y_2493_);
v_env_2503_ = lean_ctor_get(v___x_2502_, 0);
v_nextMacroScope_2504_ = lean_ctor_get(v___x_2502_, 1);
v_ngen_2505_ = lean_ctor_get(v___x_2502_, 2);
v_auxDeclNGen_2506_ = lean_ctor_get(v___x_2502_, 3);
v_traceState_2507_ = lean_ctor_get(v___x_2502_, 4);
v_recordedDeps_2508_ = lean_ctor_get(v___x_2502_, 6);
v_messages_2509_ = lean_ctor_get(v___x_2502_, 7);
v_infoState_2510_ = lean_ctor_get(v___x_2502_, 8);
v_snapshotTasks_2511_ = lean_ctor_get(v___x_2502_, 9);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2502_, 5);
lean_dec(v_unused_2566_);
v___x_2513_ = v___x_2502_;
v_isShared_2514_ = v_isSharedCheck_2565_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_snapshotTasks_2511_);
lean_inc(v_infoState_2510_);
lean_inc(v_messages_2509_);
lean_inc(v_recordedDeps_2508_);
lean_inc(v_traceState_2507_);
lean_inc(v_auxDeclNGen_2506_);
lean_inc(v_ngen_2505_);
lean_inc(v_nextMacroScope_2504_);
lean_inc(v_env_2503_);
lean_dec(v___x_2502_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2565_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2515_ = l_Lean_Environment_setExporting(v_env_2503_, v_isExporting_2489_);
v___x_2516_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 5, v___x_2516_);
lean_ctor_set(v___x_2513_, 0, v___x_2515_);
v___x_2518_ = v___x_2513_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_nextMacroScope_2504_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_ngen_2505_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_auxDeclNGen_2506_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_traceState_2507_);
lean_ctor_set(v_reuseFailAlloc_2564_, 5, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2564_, 6, v_recordedDeps_2508_);
lean_ctor_set(v_reuseFailAlloc_2564_, 7, v_messages_2509_);
lean_ctor_set(v_reuseFailAlloc_2564_, 8, v_infoState_2510_);
lean_ctor_set(v_reuseFailAlloc_2564_, 9, v_snapshotTasks_2511_);
v___x_2518_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_mctx_2521_; lean_object* v_zetaDeltaFVarIds_2522_; lean_object* v_postponed_2523_; lean_object* v_diag_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2562_; 
v___x_2519_ = lean_st_ref_put(v___y_2493_, v___x_2518_);
v___x_2520_ = lean_st_ref_take(v___y_2491_);
v_mctx_2521_ = lean_ctor_get(v___x_2520_, 0);
v_zetaDeltaFVarIds_2522_ = lean_ctor_get(v___x_2520_, 2);
v_postponed_2523_ = lean_ctor_get(v___x_2520_, 3);
v_diag_2524_ = lean_ctor_get(v___x_2520_, 4);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2520_, 1);
lean_dec(v_unused_2563_);
v___x_2526_ = v___x_2520_;
v_isShared_2527_ = v_isSharedCheck_2562_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_diag_2524_);
lean_inc(v_postponed_2523_);
lean_inc(v_zetaDeltaFVarIds_2522_);
lean_inc(v_mctx_2521_);
lean_dec(v___x_2520_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2562_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_mctx_2521_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_zetaDeltaFVarIds_2522_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_postponed_2523_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_diag_2524_);
v___x_2530_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v_r_2532_; 
v___x_2531_ = lean_st_ref_put(v___y_2491_, v___x_2530_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v_r_2532_ = lean_apply_5(v_x_2488_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
if (lean_obj_tag(v_r_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2549_; 
v_a_2533_ = lean_ctor_get(v_r_2532_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_r_2532_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2535_ = v_r_2532_;
v_isShared_2536_ = v_isSharedCheck_2549_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v_r_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2549_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
lean_inc(v_a_2533_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 1);
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
v___x_2539_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2493_, v_isExporting_2500_, v___x_2516_, v___y_2491_, v___x_2528_, v___x_2538_);
lean_dec_ref(v___x_2538_);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v___x_2539_, 0);
lean_dec(v_unused_2547_);
v___x_2541_ = v___x_2539_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_dec(v___x_2539_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v_a_2533_);
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2533_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_a_2550_ = lean_ctor_get(v_r_2532_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v_r_2532_, 1);
v___x_2551_ = lean_box(0);
v___x_2552_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2493_, v_isExporting_2500_, v___x_2516_, v___y_2491_, v___x_2528_, v___x_2551_);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2552_, 0);
lean_dec(v_unused_2560_);
v___x_2554_ = v___x_2552_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v___x_2552_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set_tag(v___x_2554_, 1);
lean_ctor_set(v___x_2554_, 0, v_a_2550_);
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2550_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2569_, lean_object* v_isExporting_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v_isExporting_boxed_2576_; lean_object* v_res_2577_; 
v_isExporting_boxed_2576_ = lean_unbox(v_isExporting_2570_);
v_res_2577_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2569_, v_isExporting_boxed_2576_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2578_, uint8_t v_when_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
if (v_when_2579_ == 0)
{
lean_object* v___x_2585_; 
lean_inc(v___y_2583_);
lean_inc_ref(v___y_2582_);
lean_inc(v___y_2581_);
lean_inc_ref(v___y_2580_);
v___x_2585_ = lean_apply_5(v_x_2578_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, lean_box(0));
return v___x_2585_;
}
else
{
uint8_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = 0;
v___x_2587_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2578_, v___x_2586_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2588_, lean_object* v_when_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v_when_boxed_2595_; lean_object* v_res_2596_; 
v_when_boxed_2595_ = lean_unbox(v_when_2589_);
v_res_2596_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2588_, v_when_boxed_2595_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2596_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2599_ = l_Lean_stringToMessageData(v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2604_ = l_Lean_stringToMessageData(v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2605_, uint8_t v_nonRec_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v_env_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___f_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; 
v___x_2612_ = lean_st_ref_get(v___y_2610_);
v_env_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc_ref(v_env_2613_);
lean_dec(v___x_2612_);
v___x_2614_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2605_);
v___x_2615_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2613_, v_declName_2605_, v___x_2614_);
v___x_2616_ = lean_box(v_nonRec_2606_);
lean_inc(v___x_2615_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2617_, 0, v___x_2615_);
lean_closure_set(v___f_2617_, 1, v_declName_2605_);
lean_closure_set(v___f_2617_, 2, v___x_2616_);
lean_closure_set(v___f_2617_, 3, v___x_2614_);
v___x_2618_ = 1;
v___x_2619_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2617_, v___x_2618_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
if (lean_obj_tag(v_a_2620_) == 1)
{
lean_object* v_val_2621_; uint8_t v___x_2622_; 
v_val_2621_ = lean_ctor_get(v_a_2620_, 0);
v___x_2622_ = lean_name_eq(v_val_2621_, v___x_2615_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_inc(v_val_2621_);
lean_dec_ref_known(v___x_2619_, 1);
v___x_2623_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2624_ = l_Lean_MessageData_ofName(v_val_2621_);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_MessageData_ofName(v___x_2615_);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2631_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
lean_dec(v___x_2615_);
return v___x_2619_;
}
}
else
{
lean_dec(v___x_2615_);
return v___x_2619_;
}
}
else
{
lean_dec(v___x_2615_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2641_, lean_object* v_nonRec_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
uint8_t v_nonRec_boxed_2648_; lean_object* v_res_2649_; 
v_nonRec_boxed_2648_ = lean_unbox(v_nonRec_2642_);
v_res_2649_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2641_, v_nonRec_boxed_2648_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2650_, uint8_t v_nonRec_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v___x_2657_; lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2657_ = lean_box(v_nonRec_2651_);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2658_, 0, v_declName_2650_);
lean_closure_set(v___f_2658_, 1, v___x_2657_);
v___x_2659_ = lean_unsigned_to_nat(32u);
v___x_2660_ = lean_mk_empty_array_with_capacity(v___x_2659_);
lean_dec_ref(v___x_2660_);
v___x_2661_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2662_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2663_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2661_, v___x_2662_, v___f_2658_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2664_, lean_object* v_nonRec_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
uint8_t v_nonRec_boxed_2671_; lean_object* v_res_2672_; 
v_nonRec_boxed_2671_ = lean_unbox(v_nonRec_2665_);
v_res_2672_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2664_, v_nonRec_boxed_2671_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2673_, lean_object* v_as_2674_, lean_object* v_as_x27_2675_, lean_object* v_b_2676_, lean_object* v_a_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2673_, v_as_x27_2675_, v_b_2676_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2684_, lean_object* v_as_2685_, lean_object* v_as_x27_2686_, lean_object* v_b_2687_, lean_object* v_a_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2684_, v_as_2685_, v_as_x27_2686_, v_b_2687_, v_a_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v_as_x27_2686_);
lean_dec(v_as_2685_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2695_, lean_object* v_x_2696_, uint8_t v_isExporting_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2696_, v_isExporting_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_x_2705_, lean_object* v_isExporting_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
uint8_t v_isExporting_boxed_2712_; lean_object* v_res_2713_; 
v_isExporting_boxed_2712_ = lean_unbox(v_isExporting_2706_);
v_res_2713_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2704_, v_x_2705_, v_isExporting_boxed_2712_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2714_, lean_object* v_x_2715_, uint8_t v_when_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2715_, v_when_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_x_2724_, lean_object* v_when_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v_when_boxed_2731_; lean_object* v_res_2732_; 
v_when_boxed_2731_ = lean_unbox(v_when_2725_);
v_res_2732_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2723_, v_x_2724_, v_when_boxed_2731_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2733_, lean_object* v_msg_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2741_, lean_object* v_msg_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2741_, v_msg_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
return v_res_2748_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = lean_unsigned_to_nat(32u);
v___x_2750_ = lean_mk_empty_array_with_capacity(v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2752_ = ((size_t)5ULL);
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2754_ = lean_unsigned_to_nat(32u);
v___x_2755_ = lean_mk_empty_array_with_capacity(v___x_2754_);
v___x_2756_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2757_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
lean_ctor_set(v___x_2757_, 1, v___x_2755_);
lean_ctor_set(v___x_2757_, 2, v___x_2753_);
lean_ctor_set(v___x_2757_, 3, v___x_2753_);
lean_ctor_set_usize(v___x_2757_, 4, v___x_2752_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v_traceState_2761_; lean_object* v_traces_2762_; lean_object* v___x_2763_; lean_object* v_traceState_2764_; lean_object* v_env_2765_; lean_object* v_nextMacroScope_2766_; lean_object* v_ngen_2767_; lean_object* v_auxDeclNGen_2768_; lean_object* v_cache_2769_; lean_object* v_recordedDeps_2770_; lean_object* v_messages_2771_; lean_object* v_infoState_2772_; lean_object* v_snapshotTasks_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2792_; 
v___x_2760_ = lean_st_ref_get(v___y_2758_);
v_traceState_2761_ = lean_ctor_get(v___x_2760_, 4);
lean_inc_ref(v_traceState_2761_);
lean_dec(v___x_2760_);
v_traces_2762_ = lean_ctor_get(v_traceState_2761_, 0);
lean_inc_ref(v_traces_2762_);
lean_dec_ref(v_traceState_2761_);
v___x_2763_ = lean_st_ref_take(v___y_2758_);
v_traceState_2764_ = lean_ctor_get(v___x_2763_, 4);
v_env_2765_ = lean_ctor_get(v___x_2763_, 0);
v_nextMacroScope_2766_ = lean_ctor_get(v___x_2763_, 1);
v_ngen_2767_ = lean_ctor_get(v___x_2763_, 2);
v_auxDeclNGen_2768_ = lean_ctor_get(v___x_2763_, 3);
v_cache_2769_ = lean_ctor_get(v___x_2763_, 5);
v_recordedDeps_2770_ = lean_ctor_get(v___x_2763_, 6);
v_messages_2771_ = lean_ctor_get(v___x_2763_, 7);
v_infoState_2772_ = lean_ctor_get(v___x_2763_, 8);
v_snapshotTasks_2773_ = lean_ctor_get(v___x_2763_, 9);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2775_ = v___x_2763_;
v_isShared_2776_ = v_isSharedCheck_2792_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_snapshotTasks_2773_);
lean_inc(v_infoState_2772_);
lean_inc(v_messages_2771_);
lean_inc(v_recordedDeps_2770_);
lean_inc(v_cache_2769_);
lean_inc(v_traceState_2764_);
lean_inc(v_auxDeclNGen_2768_);
lean_inc(v_ngen_2767_);
lean_inc(v_nextMacroScope_2766_);
lean_inc(v_env_2765_);
lean_dec(v___x_2763_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2792_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
uint64_t v_tid_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2790_; 
v_tid_2777_ = lean_ctor_get_uint64(v_traceState_2764_, sizeof(void*)*1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_traceState_2764_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v_traceState_2764_, 0);
lean_dec(v_unused_2791_);
v___x_2779_ = v_traceState_2764_;
v_isShared_2780_ = v_isSharedCheck_2790_;
goto v_resetjp_2778_;
}
else
{
lean_dec(v_traceState_2764_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2790_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2781_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2781_);
v___x_2783_ = v___x_2779_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2781_);
lean_ctor_set_uint64(v_reuseFailAlloc_2789_, sizeof(void*)*1, v_tid_2777_);
v___x_2783_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2785_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 4, v___x_2783_);
v___x_2785_ = v___x_2775_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_env_2765_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_nextMacroScope_2766_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_ngen_2767_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_auxDeclNGen_2768_);
lean_ctor_set(v_reuseFailAlloc_2788_, 4, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2788_, 5, v_cache_2769_);
lean_ctor_set(v_reuseFailAlloc_2788_, 6, v_recordedDeps_2770_);
lean_ctor_set(v_reuseFailAlloc_2788_, 7, v_messages_2771_);
lean_ctor_set(v_reuseFailAlloc_2788_, 8, v_infoState_2772_);
lean_ctor_set(v_reuseFailAlloc_2788_, 9, v_snapshotTasks_2773_);
v___x_2785_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_st_ref_put(v___y_2758_, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_traces_2762_);
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2793_);
lean_dec(v___y_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
uint8_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = 0;
v___x_2809_ = lean_box(v___x_2808_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2818_ = l_Lean_stringToMessageData(v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2824_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2825_ = l_Lean_MessageData_ofName(v_name_2819_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2828_, lean_object* v_x_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2828_, v_x_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v_x_2829_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2834_){
_start:
{
if (lean_obj_tag(v_x_2834_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_a_2836_ = lean_ctor_get(v_x_2834_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_x_2834_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v_x_2834_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v_x_2834_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set_tag(v___x_2838_, 1);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
v_a_2844_ = lean_ctor_get(v_x_2834_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_x_2834_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v_x_2834_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v_x_2834_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set_tag(v___x_2846_, 0);
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2852_);
return v_res_2854_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2855_){
_start:
{
if (lean_obj_tag(v_e_2855_) == 0)
{
uint8_t v___x_2856_; 
v___x_2856_ = 2;
return v___x_2856_;
}
else
{
lean_object* v_a_2857_; uint8_t v___x_2858_; 
v_a_2857_ = lean_ctor_get(v_e_2855_, 0);
v___x_2858_ = lean_unbox(v_a_2857_);
if (v___x_2858_ == 0)
{
uint8_t v___x_2859_; 
v___x_2859_ = 1;
return v___x_2859_;
}
else
{
uint8_t v___x_2860_; 
v___x_2860_ = 0;
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2861_){
_start:
{
uint8_t v_res_2862_; lean_object* v_r_2863_; 
v_res_2862_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2861_);
lean_dec_ref(v_e_2861_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2864_, size_t v_i_2865_, lean_object* v_bs_2866_){
_start:
{
uint8_t v___x_2867_; 
v___x_2867_ = lean_usize_dec_lt(v_i_2865_, v_sz_2864_);
if (v___x_2867_ == 0)
{
return v_bs_2866_;
}
else
{
lean_object* v_v_2868_; lean_object* v_msg_2869_; lean_object* v___x_2870_; lean_object* v_bs_x27_2871_; size_t v___x_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
v_v_2868_ = lean_array_uget_borrowed(v_bs_2866_, v_i_2865_);
v_msg_2869_ = lean_ctor_get(v_v_2868_, 1);
lean_inc_ref(v_msg_2869_);
v___x_2870_ = lean_unsigned_to_nat(0u);
v_bs_x27_2871_ = lean_array_uset(v_bs_2866_, v_i_2865_, v___x_2870_);
v___x_2872_ = ((size_t)1ULL);
v___x_2873_ = lean_usize_add(v_i_2865_, v___x_2872_);
v___x_2874_ = lean_array_uset(v_bs_x27_2871_, v_i_2865_, v_msg_2869_);
v_i_2865_ = v___x_2873_;
v_bs_2866_ = v___x_2874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2876_, lean_object* v_i_2877_, lean_object* v_bs_2878_){
_start:
{
size_t v_sz_boxed_2879_; size_t v_i_boxed_2880_; lean_object* v_res_2881_; 
v_sz_boxed_2879_ = lean_unbox_usize(v_sz_2876_);
lean_dec(v_sz_2876_);
v_i_boxed_2880_ = lean_unbox_usize(v_i_2877_);
lean_dec(v_i_2877_);
v_res_2881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2879_, v_i_boxed_2880_, v_bs_2878_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2882_, lean_object* v_data_2883_, lean_object* v_ref_2884_, lean_object* v_msg_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_toCold_2889_; lean_object* v_currRecDepth_2890_; lean_object* v_ref_2891_; uint16_t v_optionFlags_2892_; uint8_t v_suppressElabErrors_2893_; uint8_t v_isRecordingDeps_2894_; lean_object* v_ref_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v_traceState_2898_; lean_object* v_traces_2899_; lean_object* v___x_2900_; size_t v_sz_2901_; size_t v___x_2902_; lean_object* v___x_2903_; lean_object* v_msg_2904_; lean_object* v___x_2905_; lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2944_; 
v_toCold_2889_ = lean_ctor_get(v___y_2886_, 0);
v_currRecDepth_2890_ = lean_ctor_get(v___y_2886_, 1);
v_ref_2891_ = lean_ctor_get(v___y_2886_, 2);
v_optionFlags_2892_ = lean_ctor_get_uint16(v___y_2886_, sizeof(void*)*3);
v_suppressElabErrors_2893_ = lean_ctor_get_uint8(v___y_2886_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2894_ = lean_ctor_get_uint8(v___y_2886_, sizeof(void*)*3 + 3);
v_ref_2895_ = l_Lean_replaceRef(v_ref_2884_, v_ref_2891_);
lean_inc(v_currRecDepth_2890_);
lean_inc_ref(v_toCold_2889_);
v___x_2896_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2896_, 0, v_toCold_2889_);
lean_ctor_set(v___x_2896_, 1, v_currRecDepth_2890_);
lean_ctor_set(v___x_2896_, 2, v_ref_2895_);
lean_ctor_set_uint16(v___x_2896_, sizeof(void*)*3, v_optionFlags_2892_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*3 + 2, v_suppressElabErrors_2893_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*3 + 3, v_isRecordingDeps_2894_);
v___x_2897_ = lean_st_ref_get(v___y_2887_);
v_traceState_2898_ = lean_ctor_get(v___x_2897_, 4);
lean_inc_ref(v_traceState_2898_);
lean_dec(v___x_2897_);
v_traces_2899_ = lean_ctor_get(v_traceState_2898_, 0);
lean_inc_ref(v_traces_2899_);
lean_dec_ref(v_traceState_2898_);
v___x_2900_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2899_);
lean_dec_ref(v_traces_2899_);
v_sz_2901_ = lean_array_size(v___x_2900_);
v___x_2902_ = ((size_t)0ULL);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2901_, v___x_2902_, v___x_2900_);
v_msg_2904_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2904_, 0, v_data_2883_);
lean_ctor_set(v_msg_2904_, 1, v_msg_2885_);
lean_ctor_set(v_msg_2904_, 2, v___x_2903_);
v___x_2905_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2904_, v___x_2896_, v___y_2887_);
lean_dec_ref_known(v___x_2896_, 3);
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2944_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2944_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v_traceState_2911_; lean_object* v_env_2912_; lean_object* v_nextMacroScope_2913_; lean_object* v_ngen_2914_; lean_object* v_auxDeclNGen_2915_; lean_object* v_cache_2916_; lean_object* v_recordedDeps_2917_; lean_object* v_messages_2918_; lean_object* v_infoState_2919_; lean_object* v_snapshotTasks_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2943_; 
v___x_2910_ = lean_st_ref_take(v___y_2887_);
v_traceState_2911_ = lean_ctor_get(v___x_2910_, 4);
v_env_2912_ = lean_ctor_get(v___x_2910_, 0);
v_nextMacroScope_2913_ = lean_ctor_get(v___x_2910_, 1);
v_ngen_2914_ = lean_ctor_get(v___x_2910_, 2);
v_auxDeclNGen_2915_ = lean_ctor_get(v___x_2910_, 3);
v_cache_2916_ = lean_ctor_get(v___x_2910_, 5);
v_recordedDeps_2917_ = lean_ctor_get(v___x_2910_, 6);
v_messages_2918_ = lean_ctor_get(v___x_2910_, 7);
v_infoState_2919_ = lean_ctor_get(v___x_2910_, 8);
v_snapshotTasks_2920_ = lean_ctor_get(v___x_2910_, 9);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2922_ = v___x_2910_;
v_isShared_2923_ = v_isSharedCheck_2943_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_snapshotTasks_2920_);
lean_inc(v_infoState_2919_);
lean_inc(v_messages_2918_);
lean_inc(v_recordedDeps_2917_);
lean_inc(v_cache_2916_);
lean_inc(v_traceState_2911_);
lean_inc(v_auxDeclNGen_2915_);
lean_inc(v_ngen_2914_);
lean_inc(v_nextMacroScope_2913_);
lean_inc(v_env_2912_);
lean_dec(v___x_2910_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2943_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
uint64_t v_tid_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2941_; 
v_tid_2924_ = lean_ctor_get_uint64(v_traceState_2911_, sizeof(void*)*1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_traceState_2911_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v_traceState_2911_, 0);
lean_dec(v_unused_2942_);
v___x_2926_ = v_traceState_2911_;
v_isShared_2927_ = v_isSharedCheck_2941_;
goto v_resetjp_2925_;
}
else
{
lean_dec(v_traceState_2911_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2941_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v_ref_2884_);
lean_ctor_set(v___x_2929_, 1, v_a_2906_);
v___x_2930_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2882_, v___x_2929_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2930_);
v___x_2932_ = v___x_2926_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2930_);
lean_ctor_set_uint64(v_reuseFailAlloc_2940_, sizeof(void*)*1, v_tid_2924_);
v___x_2932_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2934_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 4, v___x_2932_);
v___x_2934_ = v___x_2922_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_env_2912_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_nextMacroScope_2913_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_ngen_2914_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_auxDeclNGen_2915_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2939_, 5, v_cache_2916_);
lean_ctor_set(v_reuseFailAlloc_2939_, 6, v_recordedDeps_2917_);
lean_ctor_set(v_reuseFailAlloc_2939_, 7, v_messages_2918_);
lean_ctor_set(v_reuseFailAlloc_2939_, 8, v_infoState_2919_);
lean_ctor_set(v_reuseFailAlloc_2939_, 9, v_snapshotTasks_2920_);
v___x_2934_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = lean_st_ref_put(v___y_2887_, v___x_2934_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2928_);
v___x_2937_ = v___x_2908_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2928_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2945_, lean_object* v_data_2946_, lean_object* v_ref_2947_, lean_object* v_msg_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2945_, v_data_2946_, v_ref_2947_, v_msg_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
return v_res_2952_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2955_ = l_Lean_stringToMessageData(v___x_2954_);
return v___x_2955_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2956_; double v___x_2957_; 
v___x_2956_ = lean_unsigned_to_nat(1000u);
v___x_2957_ = lean_float_of_nat(v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2958_, uint8_t v_collapsed_2959_, lean_object* v_tag_2960_, lean_object* v_opts_2961_, uint8_t v_clsEnabled_2962_, lean_object* v_oldTraces_2963_, lean_object* v_msg_2964_, lean_object* v_resStartStop_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_fst_2969_; lean_object* v_snd_2970_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v_data_2974_; lean_object* v_fst_2985_; lean_object* v_snd_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___y_2990_; lean_object* v_a_2991_; uint8_t v___y_3006_; double v___y_3038_; 
v_fst_2969_ = lean_ctor_get(v_resStartStop_2965_, 0);
lean_inc(v_fst_2969_);
v_snd_2970_ = lean_ctor_get(v_resStartStop_2965_, 1);
lean_inc(v_snd_2970_);
lean_dec_ref(v_resStartStop_2965_);
v_fst_2985_ = lean_ctor_get(v_snd_2970_, 0);
lean_inc(v_fst_2985_);
v_snd_2986_ = lean_ctor_get(v_snd_2970_, 1);
lean_inc(v_snd_2986_);
lean_dec(v_snd_2970_);
v___x_2987_ = l_Lean_trace_profiler;
v___x_2988_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2961_, v___x_2987_);
if (v___x_2988_ == 0)
{
v___y_3006_ = v___x_2988_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3044_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2961_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; double v___x_3047_; double v___x_3048_; double v___x_3049_; 
v___x_3045_ = l_Lean_trace_profiler_threshold;
v___x_3046_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2961_, v___x_3045_);
v___x_3047_ = lean_float_of_nat(v___x_3046_);
v___x_3048_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3049_ = lean_float_div(v___x_3047_, v___x_3048_);
v___y_3038_ = v___x_3049_;
goto v___jp_3037_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; double v___x_3052_; 
v___x_3050_ = l_Lean_trace_profiler_threshold;
v___x_3051_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2961_, v___x_3050_);
v___x_3052_ = lean_float_of_nat(v___x_3051_);
v___y_3038_ = v___x_3052_;
goto v___jp_3037_;
}
}
v___jp_2971_:
{
lean_object* v___x_2975_; 
lean_inc(v___y_2973_);
v___x_2975_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2963_, v_data_2974_, v___y_2973_, v___y_2972_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v___x_2976_; 
lean_dec_ref_known(v___x_2975_, 1);
v___x_2976_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2969_);
return v___x_2976_;
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_fst_2969_);
v_a_2977_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2975_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2975_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2989_:
{
uint8_t v_result_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; double v___x_2995_; lean_object* v_data_2996_; 
v_result_2992_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2969_);
v___x_2993_ = lean_box(v_result_2992_);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
v___x_2995_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_2960_);
lean_inc_ref(v___x_2994_);
lean_inc(v_cls_2958_);
v_data_2996_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2996_, 0, v_cls_2958_);
lean_ctor_set(v_data_2996_, 1, v___x_2994_);
lean_ctor_set(v_data_2996_, 2, v_tag_2960_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3, v___x_2995_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3 + 8, v___x_2995_);
lean_ctor_set_uint8(v_data_2996_, sizeof(void*)*3 + 16, v_collapsed_2959_);
if (v___x_2988_ == 0)
{
lean_dec_ref_known(v___x_2994_, 1);
lean_dec(v_snd_2986_);
lean_dec(v_fst_2985_);
lean_dec_ref(v_tag_2960_);
lean_dec(v_cls_2958_);
v___y_2972_ = v_a_2991_;
v___y_2973_ = v___y_2990_;
v_data_2974_ = v_data_2996_;
goto v___jp_2971_;
}
else
{
lean_object* v_data_2997_; double v___x_2998_; double v___x_2999_; 
lean_dec_ref_known(v_data_2996_, 3);
v_data_2997_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2997_, 0, v_cls_2958_);
lean_ctor_set(v_data_2997_, 1, v___x_2994_);
lean_ctor_set(v_data_2997_, 2, v_tag_2960_);
v___x_2998_ = lean_unbox_float(v_fst_2985_);
lean_dec(v_fst_2985_);
lean_ctor_set_float(v_data_2997_, sizeof(void*)*3, v___x_2998_);
v___x_2999_ = lean_unbox_float(v_snd_2986_);
lean_dec(v_snd_2986_);
lean_ctor_set_float(v_data_2997_, sizeof(void*)*3 + 8, v___x_2999_);
lean_ctor_set_uint8(v_data_2997_, sizeof(void*)*3 + 16, v_collapsed_2959_);
v___y_2972_ = v_a_2991_;
v___y_2973_ = v___y_2990_;
v_data_2974_ = v_data_2997_;
goto v___jp_2971_;
}
}
v___jp_3000_:
{
lean_object* v_ref_3001_; lean_object* v___x_3002_; 
v_ref_3001_ = lean_ctor_get(v___y_2966_, 2);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
lean_inc(v_fst_2969_);
v___x_3002_ = lean_apply_4(v_msg_2964_, v_fst_2969_, v___y_2966_, v___y_2967_, lean_box(0));
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___y_2990_ = v_ref_3001_;
v_a_2991_ = v_a_3003_;
goto v___jp_2989_;
}
else
{
lean_object* v___x_3004_; 
lean_dec_ref_known(v___x_3002_, 1);
v___x_3004_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2990_ = v_ref_3001_;
v_a_2991_ = v___x_3004_;
goto v___jp_2989_;
}
}
v___jp_3005_:
{
if (v_clsEnabled_2962_ == 0)
{
if (v___y_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v_traceState_3008_; lean_object* v_env_3009_; lean_object* v_nextMacroScope_3010_; lean_object* v_ngen_3011_; lean_object* v_auxDeclNGen_3012_; lean_object* v_cache_3013_; lean_object* v_recordedDeps_3014_; lean_object* v_messages_3015_; lean_object* v_infoState_3016_; lean_object* v_snapshotTasks_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_snd_2986_);
lean_dec(v_fst_2985_);
lean_dec_ref(v_msg_2964_);
lean_dec_ref(v_tag_2960_);
lean_dec(v_cls_2958_);
v___x_3007_ = lean_st_ref_take(v___y_2967_);
v_traceState_3008_ = lean_ctor_get(v___x_3007_, 4);
v_env_3009_ = lean_ctor_get(v___x_3007_, 0);
v_nextMacroScope_3010_ = lean_ctor_get(v___x_3007_, 1);
v_ngen_3011_ = lean_ctor_get(v___x_3007_, 2);
v_auxDeclNGen_3012_ = lean_ctor_get(v___x_3007_, 3);
v_cache_3013_ = lean_ctor_get(v___x_3007_, 5);
v_recordedDeps_3014_ = lean_ctor_get(v___x_3007_, 6);
v_messages_3015_ = lean_ctor_get(v___x_3007_, 7);
v_infoState_3016_ = lean_ctor_get(v___x_3007_, 8);
v_snapshotTasks_3017_ = lean_ctor_get(v___x_3007_, 9);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3019_ = v___x_3007_;
v_isShared_3020_ = v_isSharedCheck_3036_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_snapshotTasks_3017_);
lean_inc(v_infoState_3016_);
lean_inc(v_messages_3015_);
lean_inc(v_recordedDeps_3014_);
lean_inc(v_cache_3013_);
lean_inc(v_traceState_3008_);
lean_inc(v_auxDeclNGen_3012_);
lean_inc(v_ngen_3011_);
lean_inc(v_nextMacroScope_3010_);
lean_inc(v_env_3009_);
lean_dec(v___x_3007_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3036_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
uint64_t v_tid_3021_; lean_object* v_traces_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3035_; 
v_tid_3021_ = lean_ctor_get_uint64(v_traceState_3008_, sizeof(void*)*1);
v_traces_3022_ = lean_ctor_get(v_traceState_3008_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_traceState_3008_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3024_ = v_traceState_3008_;
v_isShared_3025_ = v_isSharedCheck_3035_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_traces_3022_);
lean_dec(v_traceState_3008_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3035_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3026_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2963_, v_traces_3022_);
lean_dec_ref(v_traces_3022_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3026_);
v___x_3028_ = v___x_3024_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3026_);
lean_ctor_set_uint64(v_reuseFailAlloc_3034_, sizeof(void*)*1, v_tid_3021_);
v___x_3028_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 4, v___x_3028_);
v___x_3030_ = v___x_3019_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_env_3009_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_nextMacroScope_3010_);
lean_ctor_set(v_reuseFailAlloc_3033_, 2, v_ngen_3011_);
lean_ctor_set(v_reuseFailAlloc_3033_, 3, v_auxDeclNGen_3012_);
lean_ctor_set(v_reuseFailAlloc_3033_, 4, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3033_, 5, v_cache_3013_);
lean_ctor_set(v_reuseFailAlloc_3033_, 6, v_recordedDeps_3014_);
lean_ctor_set(v_reuseFailAlloc_3033_, 7, v_messages_3015_);
lean_ctor_set(v_reuseFailAlloc_3033_, 8, v_infoState_3016_);
lean_ctor_set(v_reuseFailAlloc_3033_, 9, v_snapshotTasks_3017_);
v___x_3030_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_st_ref_put(v___y_2967_, v___x_3030_);
v___x_3032_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2969_);
return v___x_3032_;
}
}
}
}
}
else
{
goto v___jp_3000_;
}
}
else
{
goto v___jp_3000_;
}
}
v___jp_3037_:
{
double v___x_3039_; double v___x_3040_; double v___x_3041_; uint8_t v___x_3042_; 
v___x_3039_ = lean_unbox_float(v_snd_2986_);
v___x_3040_ = lean_unbox_float(v_fst_2985_);
v___x_3041_ = lean_float_sub(v___x_3039_, v___x_3040_);
v___x_3042_ = lean_float_decLt(v___y_3038_, v___x_3041_);
v___y_3006_ = v___x_3042_;
goto v___jp_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3053_, lean_object* v_collapsed_3054_, lean_object* v_tag_3055_, lean_object* v_opts_3056_, lean_object* v_clsEnabled_3057_, lean_object* v_oldTraces_3058_, lean_object* v_msg_3059_, lean_object* v_resStartStop_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
uint8_t v_collapsed_boxed_3064_; uint8_t v_clsEnabled_boxed_3065_; lean_object* v_res_3066_; 
v_collapsed_boxed_3064_ = lean_unbox(v_collapsed_3054_);
v_clsEnabled_boxed_3065_ = lean_unbox(v_clsEnabled_3057_);
v_res_3066_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3053_, v_collapsed_boxed_3064_, v_tag_3055_, v_opts_3056_, v_clsEnabled_boxed_3065_, v_oldTraces_3058_, v_msg_3059_, v_resStartStop_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec_ref(v_opts_3056_);
return v_res_3066_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3070_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
lean_ctor_set(v___x_3072_, 2, v___x_3071_);
lean_ctor_set(v___x_3072_, 3, v___x_3071_);
lean_ctor_set(v___x_3072_, 4, v___x_3070_);
lean_ctor_set(v___x_3072_, 5, v___x_3070_);
lean_ctor_set(v___x_3072_, 6, v___x_3070_);
lean_ctor_set(v___x_3072_, 7, v___x_3070_);
lean_ctor_set(v___x_3072_, 8, v___x_3070_);
lean_ctor_set(v___x_3072_, 9, v___x_3070_);
lean_ctor_set(v___x_3072_, 10, v___x_3070_);
lean_ctor_set(v___x_3072_, 11, v___x_3069_);
return v___x_3072_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3074_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
lean_ctor_set(v___x_3074_, 2, v___x_3073_);
lean_ctor_set(v___x_3074_, 3, v___x_3073_);
lean_ctor_set(v___x_3074_, 4, v___x_3073_);
lean_ctor_set(v___x_3074_, 5, v___x_3073_);
return v___x_3074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
lean_ctor_set(v___x_3076_, 2, v___x_3075_);
lean_ctor_set(v___x_3076_, 3, v___x_3075_);
lean_ctor_set(v___x_3076_, 4, v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3082_ = l_Lean_Name_append(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3083_; double v___x_3084_; 
v___x_3083_ = lean_unsigned_to_nat(1000000000u);
v___x_3084_ = lean_float_of_nat(v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3085_, lean_object* v___f_3086_, lean_object* v_name_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_toCold_3091_; lean_object* v_options_3092_; uint8_t v_hasTrace_3093_; 
v_toCold_3091_ = lean_ctor_get(v___y_3088_, 0);
v_options_3092_ = lean_ctor_get(v_toCold_3091_, 2);
v_hasTrace_3093_ = lean_ctor_get_uint8(v_options_3092_, sizeof(void*)*1);
if (v_hasTrace_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v_env_3095_; lean_object* v___x_3096_; 
lean_dec_ref(v___f_3086_);
v___x_3094_ = lean_st_ref_get(v___y_3089_);
v_env_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc_ref(v_env_3095_);
lean_dec(v___x_3094_);
lean_inc(v_name_3087_);
v___x_3096_ = l_Lean_Meta_declFromEqLikeName(v_env_3095_, v_name_3087_);
if (lean_obj_tag(v___x_3096_) == 1)
{
lean_object* v_val_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3198_; 
v_val_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3198_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_val_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3198_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v_fst_3101_; lean_object* v_snd_3102_; lean_object* v___x_3103_; lean_object* v_env_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_fst_3101_ = lean_ctor_get(v_val_3097_, 0);
lean_inc_n(v_fst_3101_, 2);
v_snd_3102_ = lean_ctor_get(v_val_3097_, 1);
lean_inc_n(v_snd_3102_, 2);
lean_dec(v_val_3097_);
v___x_3103_ = lean_st_ref_get(v___y_3089_);
v_env_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_ref(v_env_3104_);
lean_dec(v___x_3103_);
v___x_3105_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3104_, v_fst_3101_, v_snd_3102_);
v___x_3106_ = lean_name_eq(v_name_3087_, v___x_3105_);
lean_dec(v___x_3105_);
lean_dec(v_name_3087_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
lean_dec(v_snd_3102_);
lean_dec(v_fst_3101_);
lean_dec(v___x_3085_);
v___x_3107_ = lean_box(v_hasTrace_3093_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3107_);
v___x_3109_ = v___x_3099_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
uint8_t v___x_3111_; 
lean_inc(v_snd_3102_);
v___x_3111_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3102_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3113_ = lean_string_dec_eq(v_snd_3102_, v___x_3112_);
lean_dec(v_snd_3102_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
lean_dec(v_fst_3101_);
lean_dec(v___x_3085_);
v___x_3114_ = lean_box(v_hasTrace_3093_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3114_);
v___x_3116_ = v___x_3099_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
else
{
uint8_t v___x_3118_; uint8_t v___x_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; uint64_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_del_object(v___x_3099_);
v___x_3118_ = 1;
v___x_3119_ = 0;
v___x_3120_ = 2;
v___x_3121_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3121_, 0, v___x_3111_);
lean_ctor_set_uint8(v___x_3121_, 1, v___x_3111_);
lean_ctor_set_uint8(v___x_3121_, 2, v___x_3111_);
lean_ctor_set_uint8(v___x_3121_, 3, v___x_3111_);
lean_ctor_set_uint8(v___x_3121_, 4, v___x_3111_);
lean_ctor_set_uint8(v___x_3121_, 5, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 6, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 7, v___x_3111_);
lean_ctor_set_uint8(v___x_3121_, 8, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 9, v___x_3118_);
lean_ctor_set_uint8(v___x_3121_, 10, v___x_3119_);
lean_ctor_set_uint8(v___x_3121_, 11, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 12, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 13, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 14, v___x_3120_);
lean_ctor_set_uint8(v___x_3121_, 15, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 16, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 17, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 18, v___x_3113_);
lean_ctor_set_uint8(v___x_3121_, 19, v___x_3111_);
v___x_3122_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3121_);
v___x_3123_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set_uint64(v___x_3123_, sizeof(void*)*1, v___x_3122_);
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3126_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3128_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3129_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3129_, 0, v___x_3123_);
lean_ctor_set(v___x_3129_, 1, v___x_3085_);
lean_ctor_set(v___x_3129_, 2, v___x_3126_);
lean_ctor_set(v___x_3129_, 3, v___x_3127_);
lean_ctor_set(v___x_3129_, 4, v___x_3128_);
lean_ctor_set(v___x_3129_, 5, v___x_3124_);
lean_ctor_set(v___x_3129_, 6, v___x_3128_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*7, v___x_3111_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*7 + 1, v___x_3111_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*7 + 2, v___x_3111_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*7 + 3, v___x_3106_);
v___x_3130_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3131_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3132_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3130_);
lean_ctor_set(v___x_3133_, 1, v___x_3131_);
lean_ctor_set(v___x_3133_, 2, v___x_3085_);
lean_ctor_set(v___x_3133_, 3, v___x_3125_);
lean_ctor_set(v___x_3133_, 4, v___x_3132_);
v___x_3134_ = lean_st_mk_ref(v___x_3133_);
v___x_3135_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3101_, v___x_3106_, v___x_3129_, v___x_3134_, v___y_3088_, v___y_3089_);
lean_dec_ref_known(v___x_3129_, 7);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3149_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_st_ref_get(v___x_3134_);
lean_dec(v___x_3134_);
lean_dec(v___x_3140_);
if (lean_obj_tag(v_a_3136_) == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = lean_box(v___x_3111_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3141_);
v___x_3143_ = v___x_3138_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
lean_dec_ref_known(v_a_3136_, 1);
v___x_3145_ = lean_box(v___x_3113_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3145_);
v___x_3147_ = v___x_3138_;
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
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v___x_3134_);
v_a_3150_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3135_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3135_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
else
{
uint8_t v___x_3158_; uint8_t v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; uint64_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_dec(v_snd_3102_);
lean_del_object(v___x_3099_);
v___x_3158_ = 1;
v___x_3159_ = 0;
v___x_3160_ = 2;
v___x_3161_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3161_, 0, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3161_, 1, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3161_, 2, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3161_, 3, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3161_, 4, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3161_, 5, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 6, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 7, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3161_, 8, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 9, v___x_3158_);
lean_ctor_set_uint8(v___x_3161_, 10, v___x_3159_);
lean_ctor_set_uint8(v___x_3161_, 11, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 12, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 13, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 14, v___x_3160_);
lean_ctor_set_uint8(v___x_3161_, 15, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 16, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 17, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 18, v___x_3111_);
lean_ctor_set_uint8(v___x_3161_, 19, v_hasTrace_3093_);
v___x_3162_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3161_);
v___x_3163_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set_uint64(v___x_3163_, sizeof(void*)*1, v___x_3162_);
v___x_3164_ = lean_unsigned_to_nat(0u);
v___x_3165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3166_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3167_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3168_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3169_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3169_, 0, v___x_3163_);
lean_ctor_set(v___x_3169_, 1, v___x_3085_);
lean_ctor_set(v___x_3169_, 2, v___x_3166_);
lean_ctor_set(v___x_3169_, 3, v___x_3167_);
lean_ctor_set(v___x_3169_, 4, v___x_3168_);
lean_ctor_set(v___x_3169_, 5, v___x_3164_);
lean_ctor_set(v___x_3169_, 6, v___x_3168_);
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*7, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*7 + 1, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*7 + 2, v_hasTrace_3093_);
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*7 + 3, v___x_3106_);
v___x_3170_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3171_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3172_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3170_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
lean_ctor_set(v___x_3173_, 2, v___x_3085_);
lean_ctor_set(v___x_3173_, 3, v___x_3165_);
lean_ctor_set(v___x_3173_, 4, v___x_3172_);
v___x_3174_ = lean_st_mk_ref(v___x_3173_);
v___x_3175_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3101_, v___x_3169_, v___x_3174_, v___y_3088_, v___y_3089_);
lean_dec_ref_known(v___x_3169_, 7);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3189_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3189_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3189_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_st_ref_get(v___x_3174_);
lean_dec(v___x_3174_);
lean_dec(v___x_3180_);
if (lean_obj_tag(v_a_3176_) == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3181_ = lean_box(v_hasTrace_3093_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3181_);
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_dec_ref_known(v_a_3176_, 1);
v___x_3185_ = lean_box(v___x_3111_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3185_);
v___x_3187_ = v___x_3178_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v___x_3174_);
v_a_3190_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3175_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3175_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
lean_dec(v___x_3096_);
lean_dec(v_name_3087_);
lean_dec(v___x_3085_);
v___x_3199_ = lean_box(v_hasTrace_3093_);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
return v___x_3200_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3201_; lean_object* v___f_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v_a_3210_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v_a_3225_; lean_object* v___y_3228_; lean_object* v___y_3229_; uint8_t v_a_3230_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v_a_3248_; lean_object* v___y_3251_; lean_object* v___y_3252_; uint8_t v_a_3253_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; 
v_inheritedTraceOptions_3201_ = lean_ctor_get(v_toCold_3091_, 11);
lean_inc(v_name_3087_);
v___f_3202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3202_, 0, v_name_3087_);
v___x_3203_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3204_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3205_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3201_, v_options_3092_, v___x_3205_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = l_Lean_trace_profiler;
v___x_3388_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3092_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v_env_3390_; lean_object* v___x_3391_; 
lean_dec_ref(v___f_3202_);
lean_dec_ref(v___f_3086_);
v___x_3389_ = lean_st_ref_get(v___y_3089_);
v_env_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_ref(v_env_3390_);
lean_dec(v___x_3389_);
lean_inc(v_name_3087_);
v___x_3391_ = l_Lean_Meta_declFromEqLikeName(v_env_3390_, v_name_3087_);
if (lean_obj_tag(v___x_3391_) == 1)
{
lean_object* v_val_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3493_; 
v_val_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3493_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_val_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3493_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v_fst_3396_; lean_object* v_snd_3397_; lean_object* v___x_3398_; lean_object* v_env_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_fst_3396_ = lean_ctor_get(v_val_3392_, 0);
lean_inc_n(v_fst_3396_, 2);
v_snd_3397_ = lean_ctor_get(v_val_3392_, 1);
lean_inc_n(v_snd_3397_, 2);
lean_dec(v_val_3392_);
v___x_3398_ = lean_st_ref_get(v___y_3089_);
v_env_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc_ref(v_env_3399_);
lean_dec(v___x_3398_);
v___x_3400_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3399_, v_fst_3396_, v_snd_3397_);
v___x_3401_ = lean_name_eq(v_name_3087_, v___x_3400_);
lean_dec(v___x_3400_);
lean_dec(v_name_3087_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
lean_dec(v_snd_3397_);
lean_dec(v_fst_3396_);
lean_dec(v___x_3085_);
v___x_3402_ = lean_box(v___x_3388_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3402_);
v___x_3404_ = v___x_3394_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
else
{
uint8_t v___x_3406_; 
lean_inc(v_snd_3397_);
v___x_3406_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3397_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3408_ = lean_string_dec_eq(v_snd_3397_, v___x_3407_);
lean_dec(v_snd_3397_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
lean_dec(v_fst_3396_);
lean_dec(v___x_3085_);
v___x_3409_ = lean_box(v___x_3388_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3409_);
v___x_3411_ = v___x_3394_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
else
{
uint8_t v___x_3413_; uint8_t v___x_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; uint64_t v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_del_object(v___x_3394_);
v___x_3413_ = 1;
v___x_3414_ = 0;
v___x_3415_ = 2;
v___x_3416_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3416_, 0, v___x_3406_);
lean_ctor_set_uint8(v___x_3416_, 1, v___x_3406_);
lean_ctor_set_uint8(v___x_3416_, 2, v___x_3406_);
lean_ctor_set_uint8(v___x_3416_, 3, v___x_3406_);
lean_ctor_set_uint8(v___x_3416_, 4, v___x_3406_);
lean_ctor_set_uint8(v___x_3416_, 5, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 6, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 7, v___x_3406_);
lean_ctor_set_uint8(v___x_3416_, 8, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 9, v___x_3413_);
lean_ctor_set_uint8(v___x_3416_, 10, v___x_3414_);
lean_ctor_set_uint8(v___x_3416_, 11, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 12, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 13, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 14, v___x_3415_);
lean_ctor_set_uint8(v___x_3416_, 15, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 16, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 17, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 18, v___x_3408_);
lean_ctor_set_uint8(v___x_3416_, 19, v___x_3406_);
v___x_3417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3416_);
v___x_3418_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set_uint64(v___x_3418_, sizeof(void*)*1, v___x_3417_);
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3421_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3423_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3424_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3424_, 0, v___x_3418_);
lean_ctor_set(v___x_3424_, 1, v___x_3085_);
lean_ctor_set(v___x_3424_, 2, v___x_3421_);
lean_ctor_set(v___x_3424_, 3, v___x_3422_);
lean_ctor_set(v___x_3424_, 4, v___x_3423_);
lean_ctor_set(v___x_3424_, 5, v___x_3419_);
lean_ctor_set(v___x_3424_, 6, v___x_3423_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7, v___x_3406_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7 + 1, v___x_3406_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7 + 2, v___x_3406_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7 + 3, v_hasTrace_3093_);
v___x_3425_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3426_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3425_);
lean_ctor_set(v___x_3428_, 1, v___x_3426_);
lean_ctor_set(v___x_3428_, 2, v___x_3085_);
lean_ctor_set(v___x_3428_, 3, v___x_3420_);
lean_ctor_set(v___x_3428_, 4, v___x_3427_);
v___x_3429_ = lean_st_mk_ref(v___x_3428_);
v___x_3430_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3396_, v_hasTrace_3093_, v___x_3424_, v___x_3429_, v___y_3088_, v___y_3089_);
lean_dec_ref_known(v___x_3424_, 7);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3444_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3444_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3444_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_st_ref_get(v___x_3429_);
lean_dec(v___x_3429_);
lean_dec(v___x_3435_);
if (lean_obj_tag(v_a_3431_) == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_box(v___x_3406_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3436_);
v___x_3438_ = v___x_3433_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_dec_ref_known(v_a_3431_, 1);
v___x_3440_ = lean_box(v___x_3408_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3440_);
v___x_3442_ = v___x_3433_;
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
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v___x_3429_);
v_a_3445_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3430_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3430_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
else
{
uint8_t v___x_3453_; uint8_t v___x_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; uint64_t v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec(v_snd_3397_);
lean_del_object(v___x_3394_);
v___x_3453_ = 1;
v___x_3454_ = 0;
v___x_3455_ = 2;
v___x_3456_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3456_, 0, v___x_3388_);
lean_ctor_set_uint8(v___x_3456_, 1, v___x_3388_);
lean_ctor_set_uint8(v___x_3456_, 2, v___x_3388_);
lean_ctor_set_uint8(v___x_3456_, 3, v___x_3388_);
lean_ctor_set_uint8(v___x_3456_, 4, v___x_3388_);
lean_ctor_set_uint8(v___x_3456_, 5, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 6, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 7, v___x_3388_);
lean_ctor_set_uint8(v___x_3456_, 8, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 9, v___x_3453_);
lean_ctor_set_uint8(v___x_3456_, 10, v___x_3454_);
lean_ctor_set_uint8(v___x_3456_, 11, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 12, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 13, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 14, v___x_3455_);
lean_ctor_set_uint8(v___x_3456_, 15, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 16, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 17, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 18, v___x_3406_);
lean_ctor_set_uint8(v___x_3456_, 19, v___x_3388_);
v___x_3457_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3456_);
v___x_3458_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set_uint64(v___x_3458_, sizeof(void*)*1, v___x_3457_);
v___x_3459_ = lean_unsigned_to_nat(0u);
v___x_3460_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3461_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3462_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3463_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3464_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3464_, 0, v___x_3458_);
lean_ctor_set(v___x_3464_, 1, v___x_3085_);
lean_ctor_set(v___x_3464_, 2, v___x_3461_);
lean_ctor_set(v___x_3464_, 3, v___x_3462_);
lean_ctor_set(v___x_3464_, 4, v___x_3463_);
lean_ctor_set(v___x_3464_, 5, v___x_3459_);
lean_ctor_set(v___x_3464_, 6, v___x_3463_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7, v___x_3388_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7 + 1, v___x_3388_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7 + 2, v___x_3388_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7 + 3, v_hasTrace_3093_);
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3466_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3467_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3465_);
lean_ctor_set(v___x_3468_, 1, v___x_3466_);
lean_ctor_set(v___x_3468_, 2, v___x_3085_);
lean_ctor_set(v___x_3468_, 3, v___x_3460_);
lean_ctor_set(v___x_3468_, 4, v___x_3467_);
v___x_3469_ = lean_st_mk_ref(v___x_3468_);
v___x_3470_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3396_, v___x_3464_, v___x_3469_, v___y_3088_, v___y_3089_);
lean_dec_ref_known(v___x_3464_, 7);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3484_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3484_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3484_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_st_ref_get(v___x_3469_);
lean_dec(v___x_3469_);
lean_dec(v___x_3475_);
if (lean_obj_tag(v_a_3471_) == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_box(v___x_3388_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3476_);
v___x_3478_ = v___x_3473_;
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
lean_object* v___x_3480_; lean_object* v___x_3482_; 
lean_dec_ref_known(v_a_3471_, 1);
v___x_3480_ = lean_box(v___x_3406_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3480_);
v___x_3482_ = v___x_3473_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec(v___x_3469_);
v_a_3485_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3470_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3470_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_dec(v___x_3391_);
lean_dec(v_name_3087_);
lean_dec(v___x_3085_);
v___x_3494_ = lean_box(v___x_3388_);
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
return v___x_3495_;
}
}
else
{
goto v___jp_3263_;
}
}
else
{
goto v___jp_3263_;
}
v___jp_3207_:
{
lean_object* v___x_3211_; double v___x_3212_; double v___x_3213_; double v___x_3214_; double v___x_3215_; double v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3211_ = lean_io_mono_nanos_now();
v___x_3212_ = lean_float_of_nat(v___y_3209_);
v___x_3213_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3214_ = lean_float_div(v___x_3212_, v___x_3213_);
v___x_3215_ = lean_float_of_nat(v___x_3211_);
v___x_3216_ = lean_float_div(v___x_3215_, v___x_3213_);
v___x_3217_ = lean_box_float(v___x_3214_);
v___x_3218_ = lean_box_float(v___x_3216_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3217_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_a_3210_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3203_, v_hasTrace_3093_, v___x_3204_, v_options_3092_, v___x_3206_, v___y_3208_, v___f_3202_, v___x_3220_, v___y_3088_, v___y_3089_);
return v___x_3221_;
}
v___jp_3222_:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v_a_3225_);
v___y_3208_ = v___y_3223_;
v___y_3209_ = v___y_3224_;
v_a_3210_ = v___x_3226_;
goto v___jp_3207_;
}
v___jp_3227_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_box(v_a_3230_);
v___x_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
v___y_3208_ = v___y_3228_;
v___y_3209_ = v___y_3229_;
v_a_3210_ = v___x_3232_;
goto v___jp_3207_;
}
v___jp_3233_:
{
lean_object* v___x_3237_; double v___x_3238_; double v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3237_ = lean_io_get_num_heartbeats();
v___x_3238_ = lean_float_of_nat(v___y_3235_);
v___x_3239_ = lean_float_of_nat(v___x_3237_);
v___x_3240_ = lean_box_float(v___x_3238_);
v___x_3241_ = lean_box_float(v___x_3239_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_a_3236_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3203_, v_hasTrace_3093_, v___x_3204_, v_options_3092_, v___x_3206_, v___y_3234_, v___f_3202_, v___x_3243_, v___y_3088_, v___y_3089_);
return v___x_3244_;
}
v___jp_3245_:
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v_a_3248_);
v___y_3234_ = v___y_3246_;
v___y_3235_ = v___y_3247_;
v_a_3236_ = v___x_3249_;
goto v___jp_3233_;
}
v___jp_3250_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_box(v_a_3253_);
v___x_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
v___y_3234_ = v___y_3251_;
v___y_3235_ = v___y_3252_;
v_a_3236_ = v___x_3255_;
goto v___jp_3233_;
}
v___jp_3256_:
{
if (lean_obj_tag(v___y_3259_) == 0)
{
lean_object* v_a_3260_; uint8_t v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___y_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___y_3259_, 1);
v___x_3261_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
v___y_3251_ = v___y_3257_;
v___y_3252_ = v___y_3258_;
v_a_3253_ = v___x_3261_;
goto v___jp_3250_;
}
else
{
lean_object* v_a_3262_; 
v_a_3262_ = lean_ctor_get(v___y_3259_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___y_3259_, 1);
v___y_3246_ = v___y_3257_;
v___y_3247_ = v___y_3258_;
v_a_3248_ = v_a_3262_;
goto v___jp_3245_;
}
}
v___jp_3263_:
{
lean_object* v___x_3264_; lean_object* v_a_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3264_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3089_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v___x_3266_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3267_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3092_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v_env_3270_; lean_object* v___x_3271_; 
lean_dec_ref(v___f_3086_);
v___x_3268_ = lean_io_mono_nanos_now();
v___x_3269_ = lean_st_ref_get(v___y_3089_);
v_env_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref(v_env_3270_);
lean_dec(v___x_3269_);
lean_inc(v_name_3087_);
v___x_3271_ = l_Lean_Meta_declFromEqLikeName(v_env_3270_, v_name_3087_);
if (lean_obj_tag(v___x_3271_) == 1)
{
lean_object* v_val_3272_; lean_object* v_fst_3273_; lean_object* v_snd_3274_; lean_object* v___x_3275_; lean_object* v_env_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v_val_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_val_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v_fst_3273_ = lean_ctor_get(v_val_3272_, 0);
lean_inc_n(v_fst_3273_, 2);
v_snd_3274_ = lean_ctor_get(v_val_3272_, 1);
lean_inc_n(v_snd_3274_, 2);
lean_dec(v_val_3272_);
v___x_3275_ = lean_st_ref_get(v___y_3089_);
v_env_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc_ref(v_env_3276_);
lean_dec(v___x_3275_);
v___x_3277_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3276_, v_fst_3273_, v_snd_3274_);
v___x_3278_ = lean_name_eq(v_name_3087_, v___x_3277_);
lean_dec(v___x_3277_);
lean_dec(v_name_3087_);
if (v___x_3278_ == 0)
{
lean_dec(v_snd_3274_);
lean_dec(v_fst_3273_);
lean_dec(v___x_3085_);
v___y_3228_ = v_a_3265_;
v___y_3229_ = v___x_3268_;
v_a_3230_ = v___x_3267_;
goto v___jp_3227_;
}
else
{
uint8_t v___x_3279_; 
lean_inc(v_snd_3274_);
v___x_3279_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3274_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; uint8_t v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3281_ = lean_string_dec_eq(v_snd_3274_, v___x_3280_);
lean_dec(v_snd_3274_);
if (v___x_3281_ == 0)
{
lean_dec(v_fst_3273_);
lean_dec(v___x_3085_);
v___y_3228_ = v_a_3265_;
v___y_3229_ = v___x_3268_;
v_a_3230_ = v___x_3267_;
goto v___jp_3227_;
}
else
{
uint8_t v___x_3282_; uint8_t v___x_3283_; uint8_t v___x_3284_; lean_object* v___x_3285_; uint64_t v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3282_ = 1;
v___x_3283_ = 0;
v___x_3284_ = 2;
v___x_3285_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3285_, 0, v___x_3279_);
lean_ctor_set_uint8(v___x_3285_, 1, v___x_3279_);
lean_ctor_set_uint8(v___x_3285_, 2, v___x_3279_);
lean_ctor_set_uint8(v___x_3285_, 3, v___x_3279_);
lean_ctor_set_uint8(v___x_3285_, 4, v___x_3279_);
lean_ctor_set_uint8(v___x_3285_, 5, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 6, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 7, v___x_3279_);
lean_ctor_set_uint8(v___x_3285_, 8, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 9, v___x_3282_);
lean_ctor_set_uint8(v___x_3285_, 10, v___x_3283_);
lean_ctor_set_uint8(v___x_3285_, 11, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 12, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 13, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 14, v___x_3284_);
lean_ctor_set_uint8(v___x_3285_, 15, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 16, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 17, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 18, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, 19, v___x_3279_);
v___x_3286_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set_uint64(v___x_3287_, sizeof(void*)*1, v___x_3286_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3290_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3291_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3292_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3293_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3293_, 0, v___x_3287_);
lean_ctor_set(v___x_3293_, 1, v___x_3085_);
lean_ctor_set(v___x_3293_, 2, v___x_3290_);
lean_ctor_set(v___x_3293_, 3, v___x_3291_);
lean_ctor_set(v___x_3293_, 4, v___x_3292_);
lean_ctor_set(v___x_3293_, 5, v___x_3288_);
lean_ctor_set(v___x_3293_, 6, v___x_3292_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7, v___x_3279_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 1, v___x_3279_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 2, v___x_3279_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 3, v_hasTrace_3093_);
v___x_3294_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3294_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
lean_ctor_set(v___x_3297_, 2, v___x_3085_);
lean_ctor_set(v___x_3297_, 3, v___x_3289_);
lean_ctor_set(v___x_3297_, 4, v___x_3296_);
v___x_3298_ = lean_st_mk_ref(v___x_3297_);
v___x_3299_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3273_, v_hasTrace_3093_, v___x_3293_, v___x_3298_, v___y_3088_, v___y_3089_);
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
if (lean_obj_tag(v_a_3300_) == 0)
{
v___y_3228_ = v_a_3265_;
v___y_3229_ = v___x_3268_;
v_a_3230_ = v___x_3279_;
goto v___jp_3227_;
}
else
{
lean_dec_ref_known(v_a_3300_, 1);
v___y_3228_ = v_a_3265_;
v___y_3229_ = v___x_3268_;
v_a_3230_ = v___x_3281_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3302_; 
lean_dec(v___x_3298_);
v_a_3302_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3299_, 1);
v___y_3223_ = v_a_3265_;
v___y_3224_ = v___x_3268_;
v_a_3225_ = v_a_3302_;
goto v___jp_3222_;
}
}
}
else
{
uint8_t v___x_3303_; uint8_t v___x_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; uint64_t v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec(v_snd_3274_);
v___x_3303_ = 1;
v___x_3304_ = 0;
v___x_3305_ = 2;
v___x_3306_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3306_, 0, v___x_3267_);
lean_ctor_set_uint8(v___x_3306_, 1, v___x_3267_);
lean_ctor_set_uint8(v___x_3306_, 2, v___x_3267_);
lean_ctor_set_uint8(v___x_3306_, 3, v___x_3267_);
lean_ctor_set_uint8(v___x_3306_, 4, v___x_3267_);
lean_ctor_set_uint8(v___x_3306_, 5, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 6, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 7, v___x_3267_);
lean_ctor_set_uint8(v___x_3306_, 8, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 9, v___x_3303_);
lean_ctor_set_uint8(v___x_3306_, 10, v___x_3304_);
lean_ctor_set_uint8(v___x_3306_, 11, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 12, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 13, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 14, v___x_3305_);
lean_ctor_set_uint8(v___x_3306_, 15, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 16, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 17, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 18, v___x_3279_);
lean_ctor_set_uint8(v___x_3306_, 19, v___x_3267_);
v___x_3307_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set_uint64(v___x_3308_, sizeof(void*)*1, v___x_3307_);
v___x_3309_ = lean_unsigned_to_nat(0u);
v___x_3310_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3311_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3313_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3314_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3314_, 0, v___x_3308_);
lean_ctor_set(v___x_3314_, 1, v___x_3085_);
lean_ctor_set(v___x_3314_, 2, v___x_3311_);
lean_ctor_set(v___x_3314_, 3, v___x_3312_);
lean_ctor_set(v___x_3314_, 4, v___x_3313_);
lean_ctor_set(v___x_3314_, 5, v___x_3309_);
lean_ctor_set(v___x_3314_, 6, v___x_3313_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*7, v___x_3267_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*7 + 1, v___x_3267_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*7 + 2, v___x_3267_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*7 + 3, v_hasTrace_3093_);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3316_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3317_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3315_);
lean_ctor_set(v___x_3318_, 1, v___x_3316_);
lean_ctor_set(v___x_3318_, 2, v___x_3085_);
lean_ctor_set(v___x_3318_, 3, v___x_3310_);
lean_ctor_set(v___x_3318_, 4, v___x_3317_);
v___x_3319_ = lean_st_mk_ref(v___x_3318_);
v___x_3320_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3273_, v___x_3314_, v___x_3319_, v___y_3088_, v___y_3089_);
lean_dec_ref_known(v___x_3314_, 7);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3322_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3320_, 1);
v___x_3322_ = lean_st_ref_get(v___x_3319_);
lean_dec(v___x_3319_);
lean_dec(v___x_3322_);
if (lean_obj_tag(v_a_3321_) == 0)
{
v___y_3228_ = v_a_3265_;
v___y_3229_ = v___x_3268_;
v_a_3230_ = v___x_3267_;
goto v___jp_3227_;
}
else
{
lean_dec_ref_known(v_a_3321_, 1);
v___y_3228_ = v_a_3265_;
v___y_3229_ = v___x_3268_;
v_a_3230_ = v___x_3279_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3323_; 
lean_dec(v___x_3319_);
v_a_3323_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3320_, 1);
v___y_3223_ = v_a_3265_;
v___y_3224_ = v___x_3268_;
v_a_3225_ = v_a_3323_;
goto v___jp_3222_;
}
}
}
}
else
{
lean_dec(v___x_3271_);
lean_dec(v_name_3087_);
lean_dec(v___x_3085_);
v___y_3228_ = v_a_3265_;
v___y_3229_ = v___x_3268_;
v_a_3230_ = v___x_3267_;
goto v___jp_3227_;
}
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v_env_3326_; lean_object* v___x_3327_; 
v___x_3324_ = lean_io_get_num_heartbeats();
v___x_3325_ = lean_st_ref_get(v___y_3089_);
v_env_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc_ref(v_env_3326_);
lean_dec(v___x_3325_);
lean_inc(v_name_3087_);
v___x_3327_ = l_Lean_Meta_declFromEqLikeName(v_env_3326_, v_name_3087_);
if (lean_obj_tag(v___x_3327_) == 1)
{
lean_object* v_val_3328_; lean_object* v_fst_3329_; lean_object* v_snd_3330_; lean_object* v___x_3331_; lean_object* v_env_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v_val_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v_fst_3329_ = lean_ctor_get(v_val_3328_, 0);
lean_inc_n(v_fst_3329_, 2);
v_snd_3330_ = lean_ctor_get(v_val_3328_, 1);
lean_inc_n(v_snd_3330_, 2);
lean_dec(v_val_3328_);
v___x_3331_ = lean_st_ref_get(v___y_3089_);
v_env_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc_ref(v_env_3332_);
lean_dec(v___x_3331_);
v___x_3333_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3332_, v_fst_3329_, v_snd_3330_);
v___x_3334_ = lean_name_eq(v_name_3087_, v___x_3333_);
lean_dec(v___x_3333_);
lean_dec(v_name_3087_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
lean_dec(v_snd_3330_);
lean_dec(v_fst_3329_);
lean_dec(v___x_3085_);
v___x_3335_ = lean_box(0);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3088_);
v___x_3336_ = lean_apply_4(v___f_3086_, v___x_3335_, v___y_3088_, v___y_3089_, lean_box(0));
v___y_3257_ = v_a_3265_;
v___y_3258_ = v___x_3324_;
v___y_3259_ = v___x_3336_;
goto v___jp_3256_;
}
else
{
uint8_t v___x_3337_; 
lean_inc(v_snd_3330_);
v___x_3337_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3330_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3339_ = lean_string_dec_eq(v_snd_3330_, v___x_3338_);
lean_dec(v_snd_3330_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec(v_fst_3329_);
lean_dec(v___x_3085_);
v___x_3340_ = lean_box(0);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3088_);
v___x_3341_ = lean_apply_4(v___f_3086_, v___x_3340_, v___y_3088_, v___y_3089_, lean_box(0));
v___y_3257_ = v_a_3265_;
v___y_3258_ = v___x_3324_;
v___y_3259_ = v___x_3341_;
goto v___jp_3256_;
}
else
{
uint8_t v___x_3342_; uint8_t v___x_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; uint64_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_dec_ref(v___f_3086_);
v___x_3342_ = 1;
v___x_3343_ = 0;
v___x_3344_ = 2;
v___x_3345_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3345_, 0, v___x_3337_);
lean_ctor_set_uint8(v___x_3345_, 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3345_, 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3345_, 3, v___x_3337_);
lean_ctor_set_uint8(v___x_3345_, 4, v___x_3337_);
lean_ctor_set_uint8(v___x_3345_, 5, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 6, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 7, v___x_3337_);
lean_ctor_set_uint8(v___x_3345_, 8, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 9, v___x_3342_);
lean_ctor_set_uint8(v___x_3345_, 10, v___x_3343_);
lean_ctor_set_uint8(v___x_3345_, 11, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 12, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 13, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 14, v___x_3344_);
lean_ctor_set_uint8(v___x_3345_, 15, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 16, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 17, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 18, v___x_3339_);
lean_ctor_set_uint8(v___x_3345_, 19, v___x_3337_);
v___x_3346_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3345_);
v___x_3347_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3347_, 0, v___x_3345_);
lean_ctor_set_uint64(v___x_3347_, sizeof(void*)*1, v___x_3346_);
v___x_3348_ = lean_unsigned_to_nat(0u);
v___x_3349_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3350_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3352_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3353_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3353_, 0, v___x_3347_);
lean_ctor_set(v___x_3353_, 1, v___x_3085_);
lean_ctor_set(v___x_3353_, 2, v___x_3350_);
lean_ctor_set(v___x_3353_, 3, v___x_3351_);
lean_ctor_set(v___x_3353_, 4, v___x_3352_);
lean_ctor_set(v___x_3353_, 5, v___x_3348_);
lean_ctor_set(v___x_3353_, 6, v___x_3352_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*7, v___x_3337_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*7 + 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*7 + 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*7 + 3, v___x_3267_);
v___x_3354_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3355_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3356_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3354_);
lean_ctor_set(v___x_3357_, 1, v___x_3355_);
lean_ctor_set(v___x_3357_, 2, v___x_3085_);
lean_ctor_set(v___x_3357_, 3, v___x_3349_);
lean_ctor_set(v___x_3357_, 4, v___x_3356_);
v___x_3358_ = lean_st_mk_ref(v___x_3357_);
v___x_3359_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3329_, v___x_3267_, v___x_3353_, v___x_3358_, v___y_3088_, v___y_3089_);
lean_dec_ref_known(v___x_3353_, 7);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = lean_st_ref_get(v___x_3358_);
lean_dec(v___x_3358_);
lean_dec(v___x_3361_);
if (lean_obj_tag(v_a_3360_) == 0)
{
v___y_3251_ = v_a_3265_;
v___y_3252_ = v___x_3324_;
v_a_3253_ = v___x_3337_;
goto v___jp_3250_;
}
else
{
lean_dec_ref_known(v_a_3360_, 1);
v___y_3251_ = v_a_3265_;
v___y_3252_ = v___x_3324_;
v_a_3253_ = v___x_3339_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_a_3362_; 
lean_dec(v___x_3358_);
v_a_3362_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3359_, 1);
v___y_3246_ = v_a_3265_;
v___y_3247_ = v___x_3324_;
v_a_3248_ = v_a_3362_;
goto v___jp_3245_;
}
}
}
else
{
uint8_t v___x_3363_; uint8_t v___x_3364_; uint8_t v___x_3365_; uint8_t v___x_3366_; lean_object* v___x_3367_; uint64_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v_snd_3330_);
lean_dec_ref(v___f_3086_);
v___x_3363_ = 0;
v___x_3364_ = 1;
v___x_3365_ = 0;
v___x_3366_ = 2;
v___x_3367_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3367_, 0, v___x_3363_);
lean_ctor_set_uint8(v___x_3367_, 1, v___x_3363_);
lean_ctor_set_uint8(v___x_3367_, 2, v___x_3363_);
lean_ctor_set_uint8(v___x_3367_, 3, v___x_3363_);
lean_ctor_set_uint8(v___x_3367_, 4, v___x_3363_);
lean_ctor_set_uint8(v___x_3367_, 5, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 6, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 7, v___x_3363_);
lean_ctor_set_uint8(v___x_3367_, 8, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 9, v___x_3364_);
lean_ctor_set_uint8(v___x_3367_, 10, v___x_3365_);
lean_ctor_set_uint8(v___x_3367_, 11, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 12, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 13, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 14, v___x_3366_);
lean_ctor_set_uint8(v___x_3367_, 15, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 16, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 17, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 18, v___x_3337_);
lean_ctor_set_uint8(v___x_3367_, 19, v___x_3363_);
v___x_3368_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3367_);
v___x_3369_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set_uint64(v___x_3369_, sizeof(void*)*1, v___x_3368_);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3372_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3374_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3375_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3375_, 0, v___x_3369_);
lean_ctor_set(v___x_3375_, 1, v___x_3085_);
lean_ctor_set(v___x_3375_, 2, v___x_3372_);
lean_ctor_set(v___x_3375_, 3, v___x_3373_);
lean_ctor_set(v___x_3375_, 4, v___x_3374_);
lean_ctor_set(v___x_3375_, 5, v___x_3370_);
lean_ctor_set(v___x_3375_, 6, v___x_3374_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7, v___x_3363_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7 + 1, v___x_3363_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7 + 2, v___x_3363_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*7 + 3, v___x_3267_);
v___x_3376_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3377_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3378_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3376_);
lean_ctor_set(v___x_3379_, 1, v___x_3377_);
lean_ctor_set(v___x_3379_, 2, v___x_3085_);
lean_ctor_set(v___x_3379_, 3, v___x_3371_);
lean_ctor_set(v___x_3379_, 4, v___x_3378_);
v___x_3380_ = lean_st_mk_ref(v___x_3379_);
v___x_3381_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3329_, v___x_3375_, v___x_3380_, v___y_3088_, v___y_3089_);
lean_dec_ref_known(v___x_3375_, 7);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
v___x_3383_ = lean_st_ref_get(v___x_3380_);
lean_dec(v___x_3380_);
lean_dec(v___x_3383_);
if (lean_obj_tag(v_a_3382_) == 0)
{
v___y_3251_ = v_a_3265_;
v___y_3252_ = v___x_3324_;
v_a_3253_ = v___x_3363_;
goto v___jp_3250_;
}
else
{
lean_dec_ref_known(v_a_3382_, 1);
v___y_3251_ = v_a_3265_;
v___y_3252_ = v___x_3324_;
v_a_3253_ = v___x_3337_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_a_3384_; 
lean_dec(v___x_3380_);
v_a_3384_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3381_, 1);
v___y_3246_ = v_a_3265_;
v___y_3247_ = v___x_3324_;
v_a_3248_ = v_a_3384_;
goto v___jp_3245_;
}
}
}
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec(v___x_3327_);
lean_dec(v_name_3087_);
lean_dec(v___x_3085_);
v___x_3385_ = lean_box(0);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3088_);
v___x_3386_ = lean_apply_4(v___f_3086_, v___x_3385_, v___y_3088_, v___y_3089_, lean_box(0));
v___y_3257_ = v_a_3265_;
v___y_3258_ = v___x_3324_;
v___y_3259_ = v___x_3386_;
goto v___jp_3256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3496_, lean_object* v___f_3497_, lean_object* v_name_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3496_, v___f_3497_, v_name_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
return v_res_3502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = lean_unsigned_to_nat(3137104340u);
v___x_3548_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3549_ = l_Lean_Name_num___override(v___x_3548_, v___x_3547_);
return v___x_3549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3552_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3553_ = l_Lean_Name_str___override(v___x_3552_, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3556_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3557_ = l_Lean_Name_str___override(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = lean_unsigned_to_nat(2u);
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3560_ = l_Lean_Name_num___override(v___x_3559_, v___x_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3562_; lean_object* v___x_3563_; 
v___f_3562_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3563_ = l_Lean_registerReservedNameAction(v___f_3562_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v___x_3564_; uint8_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_dec_ref_known(v___x_3563_, 1);
v___x_3564_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3565_ = 0;
v___x_3566_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3567_ = l_Lean_registerTraceClass(v___x_3564_, v___x_3565_, v___x_3566_);
return v___x_3567_;
}
else
{
return v___x_3563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3571_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3576_, lean_object* v_x_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3576_, v_x_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
return v_res_3581_;
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
