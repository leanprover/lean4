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
uint16_t v___y_686_; lean_object* v___y_687_; lean_object* v_fileName_688_; lean_object* v_fileMap_689_; lean_object* v_currNamespace_690_; lean_object* v_openDecls_691_; lean_object* v_initHeartbeats_692_; lean_object* v_maxHeartbeats_693_; lean_object* v_quotContext_694_; lean_object* v_currMacroScope_695_; lean_object* v_cancelTk_x3f_696_; lean_object* v_inheritedTraceOptions_697_; lean_object* v_currRecDepth_698_; lean_object* v_ref_699_; uint8_t v_suppressElabErrors_700_; uint8_t v_checkDeprecated_701_; uint8_t v_isRecordingDeps_702_; lean_object* v___y_703_; uint16_t v___y_710_; uint8_t v___y_711_; lean_object* v___y_712_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_toCold_752_; lean_object* v_currRecDepth_753_; lean_object* v_ref_754_; uint8_t v_suppressElabErrors_755_; uint8_t v_checkDeprecated_756_; uint8_t v_isRecordingDeps_757_; lean_object* v_fileName_758_; lean_object* v_fileMap_759_; lean_object* v_options_760_; lean_object* v_currNamespace_761_; lean_object* v_openDecls_762_; lean_object* v_initHeartbeats_763_; lean_object* v_maxHeartbeats_764_; lean_object* v_quotContext_765_; lean_object* v_currMacroScope_766_; lean_object* v_cancelTk_x3f_767_; lean_object* v_inheritedTraceOptions_768_; lean_object* v___y_770_; 
v___x_750_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_751_ = lean_st_ref_get(v_a_683_);
v_toCold_752_ = lean_ctor_get(v_a_682_, 0);
v_currRecDepth_753_ = lean_ctor_get(v_a_682_, 1);
v_ref_754_ = lean_ctor_get(v_a_682_, 2);
v_suppressElabErrors_755_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 2);
v_checkDeprecated_756_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 3);
v_isRecordingDeps_757_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 4);
v_fileName_758_ = lean_ctor_get(v_toCold_752_, 0);
v_fileMap_759_ = lean_ctor_get(v_toCold_752_, 1);
v_options_760_ = lean_ctor_get(v_toCold_752_, 2);
v_currNamespace_761_ = lean_ctor_get(v_toCold_752_, 4);
v_openDecls_762_ = lean_ctor_get(v_toCold_752_, 5);
v_initHeartbeats_763_ = lean_ctor_get(v_toCold_752_, 6);
v_maxHeartbeats_764_ = lean_ctor_get(v_toCold_752_, 7);
v_quotContext_765_ = lean_ctor_get(v_toCold_752_, 8);
v_currMacroScope_766_ = lean_ctor_get(v_toCold_752_, 9);
v_cancelTk_x3f_767_ = lean_ctor_get(v_toCold_752_, 10);
v_inheritedTraceOptions_768_ = lean_ctor_get(v_toCold_752_, 11);
if (v_isRecordingDeps_757_ == 0)
{
lean_object* v_env_781_; lean_object* v___x_782_; lean_object* v_toEnvExtension_783_; lean_object* v_asyncMode_784_; uint8_t v___x_785_; lean_object* v___x_786_; 
v_env_781_ = lean_ctor_get(v___x_751_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_751_);
v___x_782_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_783_ = lean_ctor_get(v___x_782_, 0);
v_asyncMode_784_ = lean_ctor_get(v_toEnvExtension_783_, 2);
v___x_785_ = 0;
v___x_786_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_750_, v___x_782_, v_env_781_, v_declName_678_, v_asyncMode_784_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 1)
{
lean_object* v_val_787_; lean_object* v___y_789_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_val_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_793_ = l_Lean_Meta_eqnAffectingOptions;
v___x_794_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_794_ == 0)
{
lean_inc_ref(v_options_760_);
v___y_789_ = v_options_760_;
goto v___jp_788_;
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
lean_inc_ref(v_options_760_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_793_, v___x_795_, v___x_796_, v_options_760_);
v___y_789_ = v___x_797_;
goto v___jp_788_;
}
v___jp_788_:
{
size_t v_sz_790_; size_t v___x_791_; lean_object* v___x_792_; 
v_sz_790_ = lean_array_size(v_val_787_);
v___x_791_ = ((size_t)0ULL);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_787_, v_sz_790_, v___x_791_, v___y_789_);
lean_dec(v_val_787_);
v___y_770_ = v___x_792_;
goto v___jp_769_;
}
}
else
{
lean_object* v___x_798_; uint8_t v___x_799_; 
lean_dec(v___x_786_);
v___x_798_ = l_Lean_Meta_eqnAffectingOptions;
v___x_799_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_799_ == 0)
{
lean_inc_ref(v_options_760_);
v___y_770_ = v_options_760_;
goto v___jp_769_;
}
else
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = ((size_t)0ULL);
v___x_801_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
lean_inc_ref(v_options_760_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_798_, v___x_800_, v___x_801_, v_options_760_);
v___y_770_ = v___x_802_;
goto v___jp_769_;
}
}
}
else
{
lean_object* v___x_803_; 
lean_dec(v___x_751_);
lean_dec(v_declName_678_);
lean_inc_ref(v_options_760_);
v___x_803_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_760_);
v___y_770_ = v___x_803_;
goto v___jp_769_;
}
v___jp_685_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = l_Lean_maxRecDepth;
v___x_705_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_687_, v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_706_, 0, v_fileName_688_);
lean_ctor_set(v___x_706_, 1, v_fileMap_689_);
lean_ctor_set(v___x_706_, 2, v___y_687_);
lean_ctor_set(v___x_706_, 3, v___x_705_);
lean_ctor_set(v___x_706_, 4, v_currNamespace_690_);
lean_ctor_set(v___x_706_, 5, v_openDecls_691_);
lean_ctor_set(v___x_706_, 6, v_initHeartbeats_692_);
lean_ctor_set(v___x_706_, 7, v_maxHeartbeats_693_);
lean_ctor_set(v___x_706_, 8, v_quotContext_694_);
lean_ctor_set(v___x_706_, 9, v_currMacroScope_695_);
lean_ctor_set(v___x_706_, 10, v_cancelTk_x3f_696_);
lean_ctor_set(v___x_706_, 11, v_inheritedTraceOptions_697_);
lean_inc(v_ref_699_);
lean_inc(v_currRecDepth_698_);
v___x_707_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_currRecDepth_698_);
lean_ctor_set(v___x_707_, 2, v_ref_699_);
lean_ctor_set_uint16(v___x_707_, sizeof(void*)*3, v___y_686_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*3 + 2, v_suppressElabErrors_700_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*3 + 3, v_checkDeprecated_701_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*3 + 4, v_isRecordingDeps_702_);
lean_inc(v___y_703_);
lean_inc(v_a_681_);
lean_inc_ref(v_a_680_);
v___x_708_ = lean_apply_5(v_act_679_, v_a_680_, v_a_681_, v___x_707_, v___y_703_, lean_box(0));
return v___x_708_;
}
v___jp_709_:
{
lean_object* v___x_713_; lean_object* v_env_714_; lean_object* v_nextMacroScope_715_; lean_object* v_ngen_716_; lean_object* v_auxDeclNGen_717_; lean_object* v_traceState_718_; lean_object* v_recordedDeps_719_; lean_object* v_messages_720_; lean_object* v_infoState_721_; lean_object* v_snapshotTasks_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_748_; 
v___x_713_ = lean_st_ref_take(v_a_683_);
v_env_714_ = lean_ctor_get(v___x_713_, 0);
v_nextMacroScope_715_ = lean_ctor_get(v___x_713_, 1);
v_ngen_716_ = lean_ctor_get(v___x_713_, 2);
v_auxDeclNGen_717_ = lean_ctor_get(v___x_713_, 3);
v_traceState_718_ = lean_ctor_get(v___x_713_, 4);
v_recordedDeps_719_ = lean_ctor_get(v___x_713_, 6);
v_messages_720_ = lean_ctor_get(v___x_713_, 7);
v_infoState_721_ = lean_ctor_get(v___x_713_, 8);
v_snapshotTasks_722_ = lean_ctor_get(v___x_713_, 9);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v___x_713_, 5);
lean_dec(v_unused_749_);
v___x_724_ = v___x_713_;
v_isShared_725_ = v_isSharedCheck_748_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snapshotTasks_722_);
lean_inc(v_infoState_721_);
lean_inc(v_messages_720_);
lean_inc(v_recordedDeps_719_);
lean_inc(v_traceState_718_);
lean_inc(v_auxDeclNGen_717_);
lean_inc(v_ngen_716_);
lean_inc(v_nextMacroScope_715_);
lean_inc(v_env_714_);
lean_dec(v___x_713_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_748_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = l_Lean_Kernel_enableDiag(v_env_714_, v___y_711_);
v___x_727_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 5, v___x_727_);
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_nextMacroScope_715_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_ngen_716_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_auxDeclNGen_717_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_traceState_718_);
lean_ctor_set(v_reuseFailAlloc_747_, 5, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_747_, 6, v_recordedDeps_719_);
lean_ctor_set(v_reuseFailAlloc_747_, 7, v_messages_720_);
lean_ctor_set(v_reuseFailAlloc_747_, 8, v_infoState_721_);
lean_ctor_set(v_reuseFailAlloc_747_, 9, v_snapshotTasks_722_);
v___x_729_ = v_reuseFailAlloc_747_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v_toCold_731_; lean_object* v_currRecDepth_732_; lean_object* v_ref_733_; uint8_t v_suppressElabErrors_734_; uint8_t v_checkDeprecated_735_; uint8_t v_isRecordingDeps_736_; lean_object* v_fileName_737_; lean_object* v_fileMap_738_; lean_object* v_currNamespace_739_; lean_object* v_openDecls_740_; lean_object* v_initHeartbeats_741_; lean_object* v_maxHeartbeats_742_; lean_object* v_quotContext_743_; lean_object* v_currMacroScope_744_; lean_object* v_cancelTk_x3f_745_; lean_object* v_inheritedTraceOptions_746_; 
v___x_730_ = lean_st_ref_put(v_a_683_, v___x_729_);
v_toCold_731_ = lean_ctor_get(v_a_682_, 0);
v_currRecDepth_732_ = lean_ctor_get(v_a_682_, 1);
v_ref_733_ = lean_ctor_get(v_a_682_, 2);
v_suppressElabErrors_734_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 2);
v_checkDeprecated_735_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 3);
v_isRecordingDeps_736_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 4);
v_fileName_737_ = lean_ctor_get(v_toCold_731_, 0);
v_fileMap_738_ = lean_ctor_get(v_toCold_731_, 1);
v_currNamespace_739_ = lean_ctor_get(v_toCold_731_, 4);
v_openDecls_740_ = lean_ctor_get(v_toCold_731_, 5);
v_initHeartbeats_741_ = lean_ctor_get(v_toCold_731_, 6);
v_maxHeartbeats_742_ = lean_ctor_get(v_toCold_731_, 7);
v_quotContext_743_ = lean_ctor_get(v_toCold_731_, 8);
v_currMacroScope_744_ = lean_ctor_get(v_toCold_731_, 9);
v_cancelTk_x3f_745_ = lean_ctor_get(v_toCold_731_, 10);
v_inheritedTraceOptions_746_ = lean_ctor_get(v_toCold_731_, 11);
lean_inc_ref(v_inheritedTraceOptions_746_);
lean_inc(v_cancelTk_x3f_745_);
lean_inc(v_currMacroScope_744_);
lean_inc(v_quotContext_743_);
lean_inc(v_maxHeartbeats_742_);
lean_inc(v_initHeartbeats_741_);
lean_inc(v_openDecls_740_);
lean_inc(v_currNamespace_739_);
lean_inc_ref(v_fileMap_738_);
lean_inc_ref(v_fileName_737_);
v___y_686_ = v___y_710_;
v___y_687_ = v___y_712_;
v_fileName_688_ = v_fileName_737_;
v_fileMap_689_ = v_fileMap_738_;
v_currNamespace_690_ = v_currNamespace_739_;
v_openDecls_691_ = v_openDecls_740_;
v_initHeartbeats_692_ = v_initHeartbeats_741_;
v_maxHeartbeats_693_ = v_maxHeartbeats_742_;
v_quotContext_694_ = v_quotContext_743_;
v_currMacroScope_695_ = v_currMacroScope_744_;
v_cancelTk_x3f_696_ = v_cancelTk_x3f_745_;
v_inheritedTraceOptions_697_ = v_inheritedTraceOptions_746_;
v_currRecDepth_698_ = v_currRecDepth_732_;
v_ref_699_ = v_ref_733_;
v_suppressElabErrors_700_ = v_suppressElabErrors_734_;
v_checkDeprecated_701_ = v_checkDeprecated_735_;
v_isRecordingDeps_702_ = v_isRecordingDeps_736_;
v___y_703_ = v_a_683_;
goto v___jp_685_;
}
}
}
v___jp_769_:
{
uint16_t v___x_771_; lean_object* v___x_772_; lean_object* v_env_773_; uint8_t v___x_774_; uint16_t v___x_775_; uint16_t v___x_776_; uint16_t v___x_777_; uint8_t v___x_778_; 
v___x_771_ = l_Lean_OptionFlags_ofOptions(v___y_770_);
v___x_772_ = lean_st_ref_get(v_a_683_);
v_env_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_env_773_);
lean_dec(v___x_772_);
v___x_774_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_773_);
lean_dec_ref(v_env_773_);
v___x_775_ = 512;
v___x_776_ = lean_uint16_land(v___x_771_, v___x_775_);
v___x_777_ = 0;
v___x_778_ = lean_uint16_dec_eq(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
if (v___x_774_ == 0)
{
uint8_t v___x_779_; 
v___x_779_ = 1;
v___y_710_ = v___x_771_;
v___y_711_ = v___x_779_;
v___y_712_ = v___y_770_;
goto v___jp_709_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_768_);
lean_inc(v_cancelTk_x3f_767_);
lean_inc(v_currMacroScope_766_);
lean_inc(v_quotContext_765_);
lean_inc(v_maxHeartbeats_764_);
lean_inc(v_initHeartbeats_763_);
lean_inc(v_openDecls_762_);
lean_inc(v_currNamespace_761_);
lean_inc_ref(v_fileMap_759_);
lean_inc_ref(v_fileName_758_);
v___y_686_ = v___x_771_;
v___y_687_ = v___y_770_;
v_fileName_688_ = v_fileName_758_;
v_fileMap_689_ = v_fileMap_759_;
v_currNamespace_690_ = v_currNamespace_761_;
v_openDecls_691_ = v_openDecls_762_;
v_initHeartbeats_692_ = v_initHeartbeats_763_;
v_maxHeartbeats_693_ = v_maxHeartbeats_764_;
v_quotContext_694_ = v_quotContext_765_;
v_currMacroScope_695_ = v_currMacroScope_766_;
v_cancelTk_x3f_696_ = v_cancelTk_x3f_767_;
v_inheritedTraceOptions_697_ = v_inheritedTraceOptions_768_;
v_currRecDepth_698_ = v_currRecDepth_753_;
v_ref_699_ = v_ref_754_;
v_suppressElabErrors_700_ = v_suppressElabErrors_755_;
v_checkDeprecated_701_ = v_checkDeprecated_756_;
v_isRecordingDeps_702_ = v_isRecordingDeps_757_;
v___y_703_ = v_a_683_;
goto v___jp_685_;
}
}
else
{
if (v___x_774_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_768_);
lean_inc(v_cancelTk_x3f_767_);
lean_inc(v_currMacroScope_766_);
lean_inc(v_quotContext_765_);
lean_inc(v_maxHeartbeats_764_);
lean_inc(v_initHeartbeats_763_);
lean_inc(v_openDecls_762_);
lean_inc(v_currNamespace_761_);
lean_inc_ref(v_fileMap_759_);
lean_inc_ref(v_fileName_758_);
v___y_686_ = v___x_771_;
v___y_687_ = v___y_770_;
v_fileName_688_ = v_fileName_758_;
v_fileMap_689_ = v_fileMap_759_;
v_currNamespace_690_ = v_currNamespace_761_;
v_openDecls_691_ = v_openDecls_762_;
v_initHeartbeats_692_ = v_initHeartbeats_763_;
v_maxHeartbeats_693_ = v_maxHeartbeats_764_;
v_quotContext_694_ = v_quotContext_765_;
v_currMacroScope_695_ = v_currMacroScope_766_;
v_cancelTk_x3f_696_ = v_cancelTk_x3f_767_;
v_inheritedTraceOptions_697_ = v_inheritedTraceOptions_768_;
v_currRecDepth_698_ = v_currRecDepth_753_;
v_ref_699_ = v_ref_754_;
v_suppressElabErrors_700_ = v_suppressElabErrors_755_;
v_checkDeprecated_701_ = v_checkDeprecated_756_;
v_isRecordingDeps_702_ = v_isRecordingDeps_757_;
v___y_703_ = v_a_683_;
goto v___jp_685_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = 0;
v___y_710_ = v___x_771_;
v___y_711_ = v___x_780_;
v___y_712_ = v___y_770_;
goto v___jp_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_804_, lean_object* v_act_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_804_, v_act_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_812_, lean_object* v_declName_813_, lean_object* v_act_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_813_, v_act_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_821_, lean_object* v_declName_822_, lean_object* v_act_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_821_, v_declName_822_, v_act_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_env_834_; lean_object* v_toConstantVal_835_; lean_object* v_value_836_; lean_object* v_all_837_; lean_object* v_type_844_; uint8_t v___x_845_; 
v___x_833_ = lean_st_ref_get(v___y_831_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref_n(v_env_834_, 2);
lean_dec(v___x_833_);
v_toConstantVal_835_ = lean_ctor_get(v_thm_830_, 0);
v_value_836_ = lean_ctor_get(v_thm_830_, 1);
v_all_837_ = lean_ctor_get(v_thm_830_, 2);
v_type_844_ = lean_ctor_get(v_toConstantVal_835_, 2);
v___x_845_ = l_Lean_Environment_hasUnsafe(v_env_834_, v_type_844_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; 
v___x_846_ = l_Lean_Environment_hasUnsafe(v_env_834_, v_value_836_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_847_, 0, v_thm_830_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
else
{
lean_inc(v_all_837_);
lean_inc_ref(v_value_836_);
lean_inc_ref(v_toConstantVal_835_);
lean_dec_ref(v_thm_830_);
goto v___jp_838_;
}
}
else
{
lean_inc(v_all_837_);
lean_inc_ref(v_value_836_);
lean_inc_ref(v_toConstantVal_835_);
lean_dec_ref(v_env_834_);
lean_dec_ref(v_thm_830_);
goto v___jp_838_;
}
v___jp_838_:
{
lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_839_ = lean_box(0);
v___x_840_ = 0;
v___x_841_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_841_, 0, v_toConstantVal_835_);
lean_ctor_set(v___x_841_, 1, v_value_836_);
lean_ctor_set(v___x_841_, 2, v___x_839_);
lean_ctor_set(v___x_841_, 3, v_all_837_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*4, v___x_840_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_849_, v___y_850_);
lean_dec(v___y_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_853_, v___y_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_867_, lean_object* v_b_868_, lean_object* v_c_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
lean_inc(v___y_873_);
lean_inc_ref(v___y_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
v___x_875_ = lean_apply_7(v_k_867_, v_b_868_, v_c_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, lean_box(0));
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_876_, lean_object* v_b_877_, lean_object* v_c_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_876_, v_b_877_, v_c_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_885_, lean_object* v_k_886_, uint8_t v_cleanupAnnotations_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___f_893_; uint8_t v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_893_, 0, v_k_886_);
v___x_894_ = 1;
v___x_895_ = 0;
v___x_896_ = lean_box(0);
v___x_897_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_885_, v___x_894_, v___x_895_, v___x_894_, v___x_895_, v___x_896_, v___f_893_, v_cleanupAnnotations_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_a_906_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_897_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_897_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_914_, lean_object* v_k_915_, lean_object* v_cleanupAnnotations_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_922_; lean_object* v_res_923_; 
v_cleanupAnnotations_boxed_922_ = lean_unbox(v_cleanupAnnotations_916_);
v_res_923_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_914_, v_k_915_, v_cleanupAnnotations_boxed_922_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_924_, lean_object* v_e_925_, lean_object* v_k_926_, uint8_t v_cleanupAnnotations_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_925_, v_k_926_, v_cleanupAnnotations_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_934_, lean_object* v_e_935_, lean_object* v_k_936_, lean_object* v_cleanupAnnotations_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_943_; lean_object* v_res_944_; 
v_cleanupAnnotations_boxed_943_ = lean_unbox(v_cleanupAnnotations_937_);
v_res_944_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_934_, v_e_935_, v_k_936_, v_cleanupAnnotations_boxed_943_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
if (lean_obj_tag(v_a_945_) == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_List_reverse___redArg(v_a_946_);
return v___x_947_;
}
else
{
lean_object* v_head_948_; lean_object* v_tail_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_958_; 
v_head_948_ = lean_ctor_get(v_a_945_, 0);
v_tail_949_ = lean_ctor_get(v_a_945_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_958_ == 0)
{
v___x_951_ = v_a_945_;
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_tail_949_);
lean_inc(v_head_948_);
lean_dec(v_a_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = l_Lean_mkLevelParam(v_head_948_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_a_946_);
lean_ctor_set(v___x_951_, 0, v___x_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_a_946_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v_a_945_ = v_tail_949_;
v_a_946_ = v___x_955_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_959_, lean_object* v_name_960_, lean_object* v_xs_961_, lean_object* v_body_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_name_968_; lean_object* v_levelParams_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1039_; 
v_name_968_ = lean_ctor_get(v_toConstantVal_959_, 0);
v_levelParams_969_ = lean_ctor_get(v_toConstantVal_959_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_toConstantVal_959_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v_toConstantVal_959_, 2);
lean_dec(v_unused_1040_);
v___x_971_ = v_toConstantVal_959_;
v_isShared_972_ = v_isSharedCheck_1039_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_levelParams_969_);
lean_inc(v_name_968_);
lean_dec(v_toConstantVal_959_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1039_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_lhs_976_; lean_object* v___x_977_; 
v___x_973_ = lean_box(0);
lean_inc(v_levelParams_969_);
v___x_974_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_969_, v___x_973_);
v___x_975_ = l_Lean_mkConst(v_name_968_, v___x_974_);
v_lhs_976_ = l_Lean_mkAppN(v___x_975_, v_xs_961_);
lean_inc_ref(v_lhs_976_);
v___x_977_ = l_Lean_Meta_mkEq(v_lhs_976_, v_body_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; uint8_t v___x_979_; uint8_t v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = 0;
v___x_980_ = 1;
v___x_981_ = 1;
v___x_982_ = l_Lean_Meta_mkForallFVars(v_xs_961_, v_a_978_, v___x_979_, v___x_980_, v___x_980_, v___x_981_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_Lean_Meta_letToHave(v_a_983_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = l_Lean_Meta_mkEqRefl(v_lhs_976_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = l_Lean_Meta_mkLambdaFVars(v_xs_961_, v_a_987_, v___x_979_, v___x_980_, v___x_979_, v___x_980_, v___x_981_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
lean_inc(v_name_960_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 2, v_a_985_);
lean_ctor_set(v___x_971_, 0, v_name_960_);
v___x_991_ = v___x_971_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_name_960_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_levelParams_969_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_a_985_);
v___x_991_ = v_reuseFailAlloc_998_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_a_995_; lean_object* v___x_996_; 
lean_inc(v_name_960_);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v_name_960_);
lean_ctor_set(v___x_992_, 1, v___x_973_);
v___x_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v_a_989_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
v___x_994_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_993_, v___y_966_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v___x_994_);
v___x_996_ = l_Lean_addDecl(v_a_995_, v___x_979_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; 
lean_dec_ref_known(v___x_996_, 1);
v___x_997_ = l_Lean_inferDefEqAttr(v_name_960_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_997_;
}
else
{
lean_dec(v_name_960_);
return v___x_996_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_a_985_);
lean_del_object(v___x_971_);
lean_dec(v_levelParams_969_);
lean_dec(v_name_960_);
v_a_999_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_988_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_988_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_985_);
lean_del_object(v___x_971_);
lean_dec(v_levelParams_969_);
lean_dec(v_name_960_);
v_a_1007_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_986_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_986_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_lhs_976_);
lean_del_object(v___x_971_);
lean_dec(v_levelParams_969_);
lean_dec(v_name_960_);
v_a_1015_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_984_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_984_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_lhs_976_);
lean_del_object(v___x_971_);
lean_dec(v_levelParams_969_);
lean_dec(v_name_960_);
v_a_1023_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_982_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_982_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_lhs_976_);
lean_del_object(v___x_971_);
lean_dec(v_levelParams_969_);
lean_dec(v_name_960_);
v_a_1031_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_977_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_977_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1041_, lean_object* v_name_1042_, lean_object* v_xs_1043_, lean_object* v_body_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1041_, v_name_1042_, v_xs_1043_, v_body_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec_ref(v_xs_1043_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1051_, lean_object* v_info_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_toConstantVal_1058_; lean_object* v_value_1059_; lean_object* v___f_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
v_toConstantVal_1058_ = lean_ctor_get(v_info_1052_, 0);
lean_inc_ref(v_toConstantVal_1058_);
v_value_1059_ = lean_ctor_get(v_info_1052_, 1);
lean_inc_ref(v_value_1059_);
lean_dec_ref(v_info_1052_);
v___f_1060_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1060_, 0, v_toConstantVal_1058_);
lean_closure_set(v___f_1060_, 1, v_name_1051_);
v___x_1061_ = 1;
v___x_1062_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1059_, v___f_1060_, v___x_1061_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1063_, lean_object* v_info_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1063_, v_info_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1071_, lean_object* v_name_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1081_; lean_object* v_env_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1081_ = lean_st_ref_get(v_a_1076_);
v_env_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_env_1082_);
lean_dec(v___x_1081_);
v___x_1083_ = 0;
lean_inc(v_declName_1071_);
v___x_1084_ = l_Lean_Environment_find_x3f(v_env_1082_, v_declName_1071_, v___x_1083_);
if (lean_obj_tag(v___x_1084_) == 1)
{
lean_object* v_val_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1112_; 
v_val_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1112_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_val_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1112_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_val_1085_) == 1)
{
lean_object* v_val_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_val_1089_ = lean_ctor_get(v_val_1085_, 0);
lean_inc_ref(v_val_1089_);
lean_dec_ref_known(v_val_1085_, 1);
lean_inc_n(v_name_1072_, 2);
v___x_1090_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1090_, 0, v_name_1072_);
lean_closure_set(v___x_1090_, 1, v_val_1089_);
lean_inc(v_declName_1071_);
v___x_1091_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1091_, 0, lean_box(0));
lean_closure_set(v___x_1091_, 1, v_declName_1071_);
lean_closure_set(v___x_1091_, 2, v___x_1090_);
v___x_1092_ = l_Lean_Meta_realizeConst(v_declName_1071_, v_name_1072_, v___x_1091_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1102_; 
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v___x_1092_, 0);
lean_dec(v_unused_1103_);
v___x_1094_ = v___x_1092_;
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v___x_1092_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_name_1072_);
v___x_1097_ = v___x_1087_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_name_1072_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
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
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_del_object(v___x_1087_);
lean_dec(v_name_1072_);
v_a_1104_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1092_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1092_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_del_object(v___x_1087_);
lean_dec(v_val_1085_);
lean_dec(v_name_1072_);
lean_dec(v_declName_1071_);
goto v___jp_1078_;
}
}
}
else
{
lean_dec(v___x_1084_);
lean_dec(v_name_1072_);
lean_dec(v_declName_1071_);
goto v___jp_1078_;
}
v___jp_1078_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1113_, lean_object* v_name_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1113_, v_name_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1121_, lean_object* v_vals_1122_, lean_object* v_i_1123_, lean_object* v_k_1124_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_array_get_size(v_keys_1121_);
v___x_1126_ = lean_nat_dec_lt(v_i_1123_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec(v_i_1123_);
v___x_1127_ = lean_box(0);
return v___x_1127_;
}
else
{
lean_object* v_k_x27_1128_; uint8_t v___x_1129_; 
v_k_x27_1128_ = lean_array_fget_borrowed(v_keys_1121_, v_i_1123_);
v___x_1129_ = lean_name_eq(v_k_1124_, v_k_x27_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_nat_add(v_i_1123_, v___x_1130_);
lean_dec(v_i_1123_);
v_i_1123_ = v___x_1131_;
goto _start;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_array_fget_borrowed(v_vals_1122_, v_i_1123_);
lean_dec(v_i_1123_);
lean_inc(v___x_1133_);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1135_, lean_object* v_vals_1136_, lean_object* v_i_1137_, lean_object* v_k_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1135_, v_vals_1136_, v_i_1137_, v_k_1138_);
lean_dec(v_k_1138_);
lean_dec_ref(v_vals_1136_);
lean_dec_ref(v_keys_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1140_, size_t v_x_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
lean_object* v_es_1143_; lean_object* v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v_j_1147_; lean_object* v___x_1148_; 
v_es_1143_ = lean_ctor_get(v_x_1140_, 0);
v___x_1144_ = lean_box(2);
v___x_1145_ = ((size_t)31ULL);
v___x_1146_ = lean_usize_land(v_x_1141_, v___x_1145_);
v_j_1147_ = lean_usize_to_nat(v___x_1146_);
v___x_1148_ = lean_array_get_borrowed(v___x_1144_, v_es_1143_, v_j_1147_);
lean_dec(v_j_1147_);
switch(lean_obj_tag(v___x_1148_))
{
case 0:
{
lean_object* v_key_1149_; lean_object* v_val_1150_; uint8_t v___x_1151_; 
v_key_1149_ = lean_ctor_get(v___x_1148_, 0);
v_val_1150_ = lean_ctor_get(v___x_1148_, 1);
v___x_1151_ = lean_name_eq(v_x_1142_, v_key_1149_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_box(0);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; 
lean_inc(v_val_1150_);
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_val_1150_);
return v___x_1153_;
}
}
case 1:
{
lean_object* v_node_1154_; size_t v___x_1155_; size_t v___x_1156_; 
v_node_1154_ = lean_ctor_get(v___x_1148_, 0);
v___x_1155_ = ((size_t)5ULL);
v___x_1156_ = lean_usize_shift_right(v_x_1141_, v___x_1155_);
v_x_1140_ = v_node_1154_;
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
size_t v_x_344__boxed_1166_; lean_object* v_res_1167_; 
v_x_344__boxed_1166_ = lean_unbox_usize(v_x_1164_);
lean_dec(v_x_1164_);
v_res_1167_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1163_, v_x_344__boxed_1166_, v_x_1165_);
lean_dec(v_x_1165_);
lean_dec_ref(v_x_1163_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
uint64_t v___y_1171_; 
if (lean_obj_tag(v_x_1169_) == 0)
{
uint64_t v___x_1174_; 
v___x_1174_ = 1723ULL;
v___y_1171_ = v___x_1174_;
goto v___jp_1170_;
}
else
{
uint64_t v_hash_1175_; 
v_hash_1175_ = lean_ctor_get_uint64(v_x_1169_, sizeof(void*)*2);
v___y_1171_ = v_hash_1175_;
goto v___jp_1170_;
}
v___jp_1170_:
{
size_t v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_uint64_to_usize(v___y_1171_);
v___x_1173_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1168_, v___x_1172_, v_x_1169_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1176_, lean_object* v_x_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1176_, v_x_1177_);
lean_dec(v_x_1177_);
lean_dec_ref(v_x_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_env_1184_; lean_object* v___x_1185_; lean_object* v_asyncMode_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1182_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1183_ = lean_st_ref_get(v_a_1180_);
v_env_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_env_1184_);
lean_dec(v___x_1183_);
v___x_1185_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1186_ = lean_ctor_get(v___x_1185_, 2);
v___x_1187_ = lean_box(0);
v___x_1188_ = 0;
v___x_1189_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1182_, v___x_1185_, v_env_1184_, v_asyncMode_1186_, v___x_1187_, v___x_1188_);
v___x_1190_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1189_, v_thmName_1179_);
lean_dec(v___x_1189_);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec(v_thmName_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1196_, v_a_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_thmName_1201_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1207_, v_x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1210_, v_x_1211_, v_x_1212_);
lean_dec(v_x_1212_);
lean_dec_ref(v_x_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1214_, lean_object* v_x_1215_, size_t v_x_1216_, lean_object* v_x_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1215_, v_x_1216_, v_x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1219_, lean_object* v_x_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
size_t v_x_439__boxed_1223_; lean_object* v_res_1224_; 
v_x_439__boxed_1223_ = lean_unbox_usize(v_x_1221_);
lean_dec(v_x_1221_);
v_res_1224_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1219_, v_x_1220_, v_x_439__boxed_1223_, v_x_1222_);
lean_dec(v_x_1222_);
lean_dec_ref(v_x_1220_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1225_, lean_object* v_keys_1226_, lean_object* v_vals_1227_, lean_object* v_heq_1228_, lean_object* v_i_1229_, lean_object* v_k_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1226_, v_vals_1227_, v_i_1229_, v_k_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1232_, lean_object* v_keys_1233_, lean_object* v_vals_1234_, lean_object* v_heq_1235_, lean_object* v_i_1236_, lean_object* v_k_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1232_, v_keys_1233_, v_vals_1234_, v_heq_1235_, v_i_1236_, v_k_1237_);
lean_dec(v_k_1237_);
lean_dec_ref(v_vals_1234_);
lean_dec_ref(v_keys_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1239_, lean_object* v_i_1240_, lean_object* v_k_1241_){
_start:
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_array_get_size(v_keys_1239_);
v___x_1243_ = lean_nat_dec_lt(v_i_1240_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec(v_i_1240_);
return v___x_1243_;
}
else
{
lean_object* v_k_x27_1244_; uint8_t v___x_1245_; 
v_k_x27_1244_ = lean_array_fget_borrowed(v_keys_1239_, v_i_1240_);
v___x_1245_ = lean_name_eq(v_k_1241_, v_k_x27_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_i_1240_, v___x_1246_);
lean_dec(v_i_1240_);
v_i_1240_ = v___x_1247_;
goto _start;
}
else
{
lean_dec(v_i_1240_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1249_, lean_object* v_i_1250_, lean_object* v_k_1251_){
_start:
{
uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_res_1252_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1249_, v_i_1250_, v_k_1251_);
lean_dec(v_k_1251_);
lean_dec_ref(v_keys_1249_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1254_, size_t v_x_1255_, lean_object* v_x_1256_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v_es_1257_; lean_object* v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v_j_1261_; lean_object* v___x_1262_; 
v_es_1257_ = lean_ctor_get(v_x_1254_, 0);
v___x_1258_ = lean_box(2);
v___x_1259_ = ((size_t)31ULL);
v___x_1260_ = lean_usize_land(v_x_1255_, v___x_1259_);
v_j_1261_ = lean_usize_to_nat(v___x_1260_);
v___x_1262_ = lean_array_get_borrowed(v___x_1258_, v_es_1257_, v_j_1261_);
lean_dec(v_j_1261_);
switch(lean_obj_tag(v___x_1262_))
{
case 0:
{
lean_object* v_key_1263_; uint8_t v___x_1264_; 
v_key_1263_ = lean_ctor_get(v___x_1262_, 0);
v___x_1264_ = lean_name_eq(v_x_1256_, v_key_1263_);
return v___x_1264_;
}
case 1:
{
lean_object* v_node_1265_; size_t v___x_1266_; size_t v___x_1267_; 
v_node_1265_ = lean_ctor_get(v___x_1262_, 0);
v___x_1266_ = ((size_t)5ULL);
v___x_1267_ = lean_usize_shift_right(v_x_1255_, v___x_1266_);
v_x_1254_ = v_node_1265_;
v_x_1255_ = v___x_1267_;
goto _start;
}
default: 
{
uint8_t v___x_1269_; 
v___x_1269_ = 0;
return v___x_1269_;
}
}
}
else
{
lean_object* v_ks_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_ks_1270_ = lean_ctor_get(v_x_1254_, 0);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1270_, v___x_1271_, v_x_1256_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
size_t v_x_328__boxed_1276_; uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_x_328__boxed_1276_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_res_1277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1273_, v_x_328__boxed_1276_, v_x_1275_);
lean_dec(v_x_1275_);
lean_dec_ref(v_x_1273_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
uint64_t v___y_1282_; 
if (lean_obj_tag(v_x_1280_) == 0)
{
uint64_t v___x_1285_; 
v___x_1285_ = 1723ULL;
v___y_1282_ = v___x_1285_;
goto v___jp_1281_;
}
else
{
uint64_t v_hash_1286_; 
v_hash_1286_ = lean_ctor_get_uint64(v_x_1280_, sizeof(void*)*2);
v___y_1282_ = v_hash_1286_;
goto v___jp_1281_;
}
v___jp_1281_:
{
size_t v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = lean_uint64_to_usize(v___y_1282_);
v___x_1284_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1279_, v___x_1283_, v_x_1280_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1287_, v_x_1288_);
lean_dec(v_x_1288_);
lean_dec_ref(v_x_1287_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_env_1296_; lean_object* v___x_1297_; lean_object* v_asyncMode_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1294_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1295_ = lean_st_ref_get(v_a_1292_);
v_env_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc_ref(v_env_1296_);
lean_dec(v___x_1295_);
v___x_1297_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1298_ = lean_ctor_get(v___x_1297_, 2);
v___x_1299_ = lean_box(0);
v___x_1300_ = 0;
v___x_1301_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1294_, v___x_1297_, v_env_1296_, v_asyncMode_1298_, v___x_1299_, v___x_1300_);
v___x_1302_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1301_, v_thmName_1291_);
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
size_t v_x_419__boxed_1337_; uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_x_419__boxed_1337_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_res_1338_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1333_, v_x_1334_, v_x_419__boxed_1337_, v_x_1336_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1355_, lean_object* v_msg_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_panic_fn_borrowed(v_x1_1355_, v_msg_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1358_, lean_object* v_msg_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1358_, v_msg_1359_);
lean_dec_ref(v_x1_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v_ks_1365_; lean_object* v_vs_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1390_; 
v_ks_1365_ = lean_ctor_get(v_x_1361_, 0);
v_vs_1366_ = lean_ctor_get(v_x_1361_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_x_1361_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1368_ = v_x_1361_;
v_isShared_1369_ = v_isSharedCheck_1390_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_vs_1366_);
lean_inc(v_ks_1365_);
lean_dec(v_x_1361_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1390_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_array_get_size(v_ks_1365_);
v___x_1371_ = lean_nat_dec_lt(v_x_1362_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec(v_x_1362_);
v___x_1372_ = lean_array_push(v_ks_1365_, v_x_1363_);
v___x_1373_ = lean_array_push(v_vs_1366_, v_x_1364_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1373_);
lean_ctor_set(v___x_1368_, 0, v___x_1372_);
v___x_1375_ = v___x_1368_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v_k_x27_1377_; uint8_t v___x_1378_; 
v_k_x27_1377_ = lean_array_fget_borrowed(v_ks_1365_, v_x_1362_);
v___x_1378_ = lean_name_eq(v_x_1363_, v_k_x27_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1380_; 
if (v_isShared_1369_ == 0)
{
v___x_1380_ = v___x_1368_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_ks_1365_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_vs_1366_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_add(v_x_1362_, v___x_1381_);
lean_dec(v_x_1362_);
v_x_1361_ = v___x_1380_;
v_x_1362_ = v___x_1382_;
goto _start;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = lean_array_fset(v_ks_1365_, v_x_1362_, v_x_1363_);
v___x_1386_ = lean_array_fset(v_vs_1366_, v_x_1362_, v_x_1364_);
lean_dec(v_x_1362_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1386_);
lean_ctor_set(v___x_1368_, 0, v___x_1385_);
v___x_1388_ = v___x_1368_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1391_, lean_object* v_k_1392_, lean_object* v_v_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1391_, v___x_1394_, v_k_1392_, v_v_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1397_, size_t v_x_1398_, size_t v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1397_) == 0)
{
lean_object* v_es_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v_j_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_es_1402_ = lean_ctor_get(v_x_1397_, 0);
v___x_1403_ = ((size_t)31ULL);
v___x_1404_ = lean_usize_land(v_x_1398_, v___x_1403_);
v_j_1405_ = lean_usize_to_nat(v___x_1404_);
v___x_1406_ = lean_array_get_size(v_es_1402_);
v___x_1407_ = lean_nat_dec_lt(v_j_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_dec(v_j_1405_);
lean_dec(v_x_1401_);
lean_dec(v_x_1400_);
return v_x_1397_;
}
else
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1446_; 
lean_inc_ref(v_es_1402_);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_x_1397_, 0);
lean_dec(v_unused_1447_);
v___x_1409_ = v_x_1397_;
v_isShared_1410_ = v_isSharedCheck_1446_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_x_1397_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1446_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_v_1411_; lean_object* v___x_1412_; lean_object* v_xs_x27_1413_; lean_object* v___y_1415_; 
v_v_1411_ = lean_array_fget(v_es_1402_, v_j_1405_);
v___x_1412_ = lean_box(0);
v_xs_x27_1413_ = lean_array_fset(v_es_1402_, v_j_1405_, v___x_1412_);
switch(lean_obj_tag(v_v_1411_))
{
case 0:
{
lean_object* v_key_1420_; lean_object* v_val_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1431_; 
v_key_1420_ = lean_ctor_get(v_v_1411_, 0);
v_val_1421_ = lean_ctor_get(v_v_1411_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_v_1411_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1423_ = v_v_1411_;
v_isShared_1424_ = v_isSharedCheck_1431_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_val_1421_);
lean_inc(v_key_1420_);
lean_dec(v_v_1411_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1431_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_name_eq(v_x_1400_, v_key_1420_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_del_object(v___x_1423_);
v___x_1426_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1420_, v_val_1421_, v_x_1400_, v_x_1401_);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
v___y_1415_ = v___x_1427_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1429_; 
lean_dec(v_val_1421_);
lean_dec(v_key_1420_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_x_1401_);
lean_ctor_set(v___x_1423_, 0, v_x_1400_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_x_1400_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_x_1401_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v___y_1415_ = v___x_1429_;
goto v___jp_1414_;
}
}
}
}
case 1:
{
lean_object* v_node_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1444_; 
v_node_1432_ = lean_ctor_get(v_v_1411_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_v_1411_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1434_ = v_v_1411_;
v_isShared_1435_ = v_isSharedCheck_1444_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_node_1432_);
lean_dec(v_v_1411_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1444_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
size_t v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1436_ = ((size_t)5ULL);
v___x_1437_ = lean_usize_shift_right(v_x_1398_, v___x_1436_);
v___x_1438_ = ((size_t)1ULL);
v___x_1439_ = lean_usize_add(v_x_1399_, v___x_1438_);
v___x_1440_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1432_, v___x_1437_, v___x_1439_, v_x_1400_, v_x_1401_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1440_);
v___x_1442_ = v___x_1434_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
v___y_1415_ = v___x_1442_;
goto v___jp_1414_;
}
}
}
default: 
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_x_1400_);
lean_ctor_set(v___x_1445_, 1, v_x_1401_);
v___y_1415_ = v___x_1445_;
goto v___jp_1414_;
}
}
v___jp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_array_fset(v_xs_x27_1413_, v_j_1405_, v___y_1415_);
lean_dec(v_j_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1416_);
v___x_1418_ = v___x_1409_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v_ks_1448_; lean_object* v_vs_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1467_; 
v_ks_1448_ = lean_ctor_get(v_x_1397_, 0);
v_vs_1449_ = lean_ctor_get(v_x_1397_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1451_ = v_x_1397_;
v_isShared_1452_ = v_isSharedCheck_1467_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_vs_1449_);
lean_inc(v_ks_1448_);
lean_dec(v_x_1397_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1467_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_ks_1448_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_vs_1449_);
v___x_1454_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v_newNode_1455_; size_t v___x_1456_; uint8_t v___x_1457_; 
v_newNode_1455_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1454_, v_x_1400_, v_x_1401_);
v___x_1456_ = ((size_t)7ULL);
v___x_1457_ = lean_usize_dec_le(v___x_1456_, v_x_1399_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1455_);
v___x_1459_ = lean_unsigned_to_nat(4u);
v___x_1460_ = lean_nat_dec_lt(v___x_1458_, v___x_1459_);
lean_dec(v___x_1458_);
if (v___x_1460_ == 0)
{
lean_object* v_ks_1461_; lean_object* v_vs_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_ks_1461_ = lean_ctor_get(v_newNode_1455_, 0);
lean_inc_ref(v_ks_1461_);
v_vs_1462_ = lean_ctor_get(v_newNode_1455_, 1);
lean_inc_ref(v_vs_1462_);
lean_dec_ref(v_newNode_1455_);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1465_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1399_, v_ks_1461_, v_vs_1462_, v___x_1463_, v___x_1464_);
lean_dec_ref(v_vs_1462_);
lean_dec_ref(v_ks_1461_);
return v___x_1465_;
}
else
{
return v_newNode_1455_;
}
}
else
{
return v_newNode_1455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1468_, lean_object* v_keys_1469_, lean_object* v_vals_1470_, lean_object* v_i_1471_, lean_object* v_entries_1472_){
_start:
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_array_get_size(v_keys_1469_);
v___x_1474_ = lean_nat_dec_lt(v_i_1471_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_dec(v_i_1471_);
return v_entries_1472_;
}
else
{
lean_object* v_k_1475_; lean_object* v_v_1476_; uint64_t v___y_1478_; 
v_k_1475_ = lean_array_fget_borrowed(v_keys_1469_, v_i_1471_);
v_v_1476_ = lean_array_fget_borrowed(v_vals_1470_, v_i_1471_);
if (lean_obj_tag(v_k_1475_) == 0)
{
uint64_t v___x_1489_; 
v___x_1489_ = 1723ULL;
v___y_1478_ = v___x_1489_;
goto v___jp_1477_;
}
else
{
uint64_t v_hash_1490_; 
v_hash_1490_ = lean_ctor_get_uint64(v_k_1475_, sizeof(void*)*2);
v___y_1478_ = v_hash_1490_;
goto v___jp_1477_;
}
v___jp_1477_:
{
size_t v_h_1479_; size_t v___x_1480_; lean_object* v___x_1481_; size_t v___x_1482_; size_t v___x_1483_; size_t v___x_1484_; size_t v_h_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_h_1479_ = lean_uint64_to_usize(v___y_1478_);
v___x_1480_ = ((size_t)5ULL);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_sub(v_depth_1468_, v___x_1482_);
v___x_1484_ = lean_usize_mul(v___x_1480_, v___x_1483_);
v_h_1485_ = lean_usize_shift_right(v_h_1479_, v___x_1484_);
v___x_1486_ = lean_nat_add(v_i_1471_, v___x_1481_);
lean_dec(v_i_1471_);
lean_inc(v_v_1476_);
lean_inc(v_k_1475_);
v___x_1487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1472_, v_h_1485_, v_depth_1468_, v_k_1475_, v_v_1476_);
v_i_1471_ = v___x_1486_;
v_entries_1472_ = v___x_1487_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1491_, lean_object* v_keys_1492_, lean_object* v_vals_1493_, lean_object* v_i_1494_, lean_object* v_entries_1495_){
_start:
{
size_t v_depth_boxed_1496_; lean_object* v_res_1497_; 
v_depth_boxed_1496_ = lean_unbox_usize(v_depth_1491_);
lean_dec(v_depth_1491_);
v_res_1497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1496_, v_keys_1492_, v_vals_1493_, v_i_1494_, v_entries_1495_);
lean_dec_ref(v_vals_1493_);
lean_dec_ref(v_keys_1492_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
size_t v_x_905__boxed_1503_; size_t v_x_906__boxed_1504_; lean_object* v_res_1505_; 
v_x_905__boxed_1503_ = lean_unbox_usize(v_x_1499_);
lean_dec(v_x_1499_);
v_x_906__boxed_1504_ = lean_unbox_usize(v_x_1500_);
lean_dec(v_x_1500_);
v_res_1505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1498_, v_x_905__boxed_1503_, v_x_906__boxed_1504_, v_x_1501_, v_x_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
uint64_t v___y_1510_; 
if (lean_obj_tag(v_x_1507_) == 0)
{
uint64_t v___x_1514_; 
v___x_1514_ = 1723ULL;
v___y_1510_ = v___x_1514_;
goto v___jp_1509_;
}
else
{
uint64_t v_hash_1515_; 
v_hash_1515_ = lean_ctor_get_uint64(v_x_1507_, sizeof(void*)*2);
v___y_1510_ = v_hash_1515_;
goto v___jp_1509_;
}
v___jp_1509_:
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_uint64_to_usize(v___y_1510_);
v___x_1512_ = ((size_t)1ULL);
v___x_1513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1506_, v___x_1511_, v___x_1512_, v_x_1507_, v_x_1508_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1521_, lean_object* v_as_1522_, size_t v_i_1523_, size_t v_stop_1524_, lean_object* v_b_1525_){
_start:
{
lean_object* v___y_1527_; uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_eq(v_i_1523_, v_stop_1524_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_array_uget_borrowed(v_as_1522_, v_i_1523_);
v___x_1533_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1525_, v___x_1532_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; 
lean_inc(v_declName_1521_);
lean_inc(v___x_1532_);
v___x_1534_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1525_, v___x_1532_, v_declName_1521_);
v___y_1527_ = v___x_1534_;
goto v___jp_1526_;
}
else
{
lean_object* v_val_1535_; uint8_t v___x_1536_; 
v_val_1535_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1536_ = lean_name_eq(v_val_1535_, v_declName_1521_);
if (v___x_1536_ == 0)
{
uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1537_ = 1;
v___x_1538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1540_ = lean_unsigned_to_nat(227u);
v___x_1541_ = lean_unsigned_to_nat(10u);
v___x_1542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1532_);
v___x_1543_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1532_, v___x_1537_);
v___x_1544_ = lean_string_append(v___x_1542_, v___x_1543_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1546_ = lean_string_append(v___x_1544_, v___x_1545_);
v___x_1547_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1535_, v___x_1537_);
v___x_1548_ = lean_string_append(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1550_ = lean_string_append(v___x_1548_, v___x_1549_);
v___x_1551_ = l_mkPanicMessageWithDecl(v___x_1538_, v___x_1539_, v___x_1540_, v___x_1541_, v___x_1550_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = lean_panic_fn_borrowed(v_b_1525_, v___x_1551_);
lean_dec_ref(v_b_1525_);
v___y_1527_ = v___x_1552_;
goto v___jp_1526_;
}
else
{
lean_dec(v_val_1535_);
v___y_1527_ = v_b_1525_;
goto v___jp_1526_;
}
}
}
else
{
lean_dec(v_declName_1521_);
return v_b_1525_;
}
v___jp_1526_:
{
size_t v___x_1528_; size_t v___x_1529_; 
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_add(v_i_1523_, v___x_1528_);
v_i_1523_ = v___x_1529_;
v_b_1525_ = v___y_1527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1553_, lean_object* v_as_1554_, lean_object* v_i_1555_, lean_object* v_stop_1556_, lean_object* v_b_1557_){
_start:
{
size_t v_i_boxed_1558_; size_t v_stop_boxed_1559_; lean_object* v_res_1560_; 
v_i_boxed_1558_ = lean_unbox_usize(v_i_1555_);
lean_dec(v_i_1555_);
v_stop_boxed_1559_ = lean_unbox_usize(v_stop_1556_);
lean_dec(v_stop_1556_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1553_, v_as_1554_, v_i_boxed_1558_, v_stop_boxed_1559_, v_b_1557_);
lean_dec_ref(v_as_1554_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1561_, lean_object* v_declName_1562_, lean_object* v_s_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_array_get_size(v_eqThms_1561_);
v___x_1566_ = lean_nat_dec_lt(v___x_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_dec(v_declName_1562_);
return v_s_1563_;
}
else
{
size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = lean_usize_of_nat(v___x_1565_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1562_, v_eqThms_1561_, v___x_1567_, v___x_1568_, v_s_1563_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1570_, lean_object* v_declName_1571_, lean_object* v_s_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1570_, v_declName_1571_, v_s_1572_);
lean_dec_ref(v_eqThms_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1574_, lean_object* v_eqThms_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v_env_1580_; lean_object* v_nextMacroScope_1581_; lean_object* v_ngen_1582_; lean_object* v_auxDeclNGen_1583_; lean_object* v_traceState_1584_; lean_object* v_recordedDeps_1585_; lean_object* v_messages_1586_; lean_object* v_infoState_1587_; lean_object* v_snapshotTasks_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1604_; 
v___f_1578_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1578_, 0, v_eqThms_1575_);
lean_closure_set(v___f_1578_, 1, v_declName_1574_);
v___x_1579_ = lean_st_ref_take(v_a_1576_);
v_env_1580_ = lean_ctor_get(v___x_1579_, 0);
v_nextMacroScope_1581_ = lean_ctor_get(v___x_1579_, 1);
v_ngen_1582_ = lean_ctor_get(v___x_1579_, 2);
v_auxDeclNGen_1583_ = lean_ctor_get(v___x_1579_, 3);
v_traceState_1584_ = lean_ctor_get(v___x_1579_, 4);
v_recordedDeps_1585_ = lean_ctor_get(v___x_1579_, 6);
v_messages_1586_ = lean_ctor_get(v___x_1579_, 7);
v_infoState_1587_ = lean_ctor_get(v___x_1579_, 8);
v_snapshotTasks_1588_ = lean_ctor_get(v___x_1579_, 9);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1579_, 5);
lean_dec(v_unused_1605_);
v___x_1590_ = v___x_1579_;
v_isShared_1591_ = v_isSharedCheck_1604_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_snapshotTasks_1588_);
lean_inc(v_infoState_1587_);
lean_inc(v_messages_1586_);
lean_inc(v_recordedDeps_1585_);
lean_inc(v_traceState_1584_);
lean_inc(v_auxDeclNGen_1583_);
lean_inc(v_ngen_1582_);
lean_inc(v_nextMacroScope_1581_);
lean_inc(v_env_1580_);
lean_dec(v___x_1579_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1604_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v_asyncMode_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1592_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1593_ = lean_ctor_get(v___x_1592_, 2);
v___x_1594_ = lean_box(0);
v___x_1595_ = lean_box(0);
v___x_1596_ = 1;
v___x_1597_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1592_, v_env_1580_, v___f_1578_, v_asyncMode_1593_, v___x_1595_, v___x_1596_);
v___x_1598_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 5, v___x_1598_);
lean_ctor_set(v___x_1590_, 0, v___x_1597_);
v___x_1600_ = v___x_1590_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_nextMacroScope_1581_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_ngen_1582_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_auxDeclNGen_1583_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_traceState_1584_);
lean_ctor_set(v_reuseFailAlloc_1603_, 5, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1603_, 6, v_recordedDeps_1585_);
lean_ctor_set(v_reuseFailAlloc_1603_, 7, v_messages_1586_);
lean_ctor_set(v_reuseFailAlloc_1603_, 8, v_infoState_1587_);
lean_ctor_set(v_reuseFailAlloc_1603_, 9, v_snapshotTasks_1588_);
v___x_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_st_ref_put(v_a_1576_, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1594_);
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1606_, lean_object* v_eqThms_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1606_, v_eqThms_1607_, v_a_1608_);
lean_dec(v_a_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1611_, lean_object* v_eqThms_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1611_, v_eqThms_1612_, v_a_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1617_, lean_object* v_eqThms_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1617_, v_eqThms_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1624_, v_x_1625_, v_x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1628_, lean_object* v_x_1629_, size_t v_x_1630_, size_t v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1629_, v_x_1630_, v_x_1631_, v_x_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
size_t v_x_1219__boxed_1641_; size_t v_x_1220__boxed_1642_; lean_object* v_res_1643_; 
v_x_1219__boxed_1641_ = lean_unbox_usize(v_x_1637_);
lean_dec(v_x_1637_);
v_x_1220__boxed_1642_ = lean_unbox_usize(v_x_1638_);
lean_dec(v_x_1638_);
v_res_1643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1635_, v_x_1636_, v_x_1219__boxed_1641_, v_x_1220__boxed_1642_, v_x_1639_, v_x_1640_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1644_, lean_object* v_n_1645_, lean_object* v_k_1646_, lean_object* v_v_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1645_, v_k_1646_, v_v_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1649_, size_t v_depth_1650_, lean_object* v_keys_1651_, lean_object* v_vals_1652_, lean_object* v_heq_1653_, lean_object* v_i_1654_, lean_object* v_entries_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1650_, v_keys_1651_, v_vals_1652_, v_i_1654_, v_entries_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1657_, lean_object* v_depth_1658_, lean_object* v_keys_1659_, lean_object* v_vals_1660_, lean_object* v_heq_1661_, lean_object* v_i_1662_, lean_object* v_entries_1663_){
_start:
{
size_t v_depth_boxed_1664_; lean_object* v_res_1665_; 
v_depth_boxed_1664_ = lean_unbox_usize(v_depth_1658_);
lean_dec(v_depth_1658_);
v_res_1665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1657_, v_depth_boxed_1664_, v_keys_1659_, v_vals_1660_, v_heq_1661_, v_i_1662_, v_entries_1663_);
lean_dec_ref(v_vals_1660_);
lean_dec_ref(v_keys_1659_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1667_, v_x_1668_, v_x_1669_, v_x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1672_, lean_object* v_env_1673_, lean_object* v_idx_1674_, lean_object* v_eqs_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_nextEq_1682_; uint8_t v___x_1683_; 
v___x_1677_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1678_ = lean_unsigned_to_nat(1u);
v___x_1679_ = lean_nat_add(v_idx_1674_, v___x_1678_);
lean_dec(v_idx_1674_);
lean_inc(v___x_1679_);
v___x_1680_ = l_Nat_reprFast(v___x_1679_);
v___x_1681_ = lean_string_append(v___x_1677_, v___x_1680_);
lean_dec_ref(v___x_1680_);
lean_inc(v_declName_1672_);
lean_inc_ref(v_env_1673_);
v_nextEq_1682_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1673_, v_declName_1672_, v___x_1681_);
v___x_1683_ = l_Lean_Environment_containsOnBranch(v_env_1673_, v_nextEq_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec(v_nextEq_1682_);
lean_dec(v___x_1679_);
lean_dec_ref(v_env_1673_);
lean_dec(v_declName_1672_);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_eqs_1675_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_array_push(v_eqs_1675_, v_nextEq_1682_);
v_idx_1674_ = v___x_1679_;
v_eqs_1675_ = v___x_1685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1687_, lean_object* v_env_1688_, lean_object* v_idx_1689_, lean_object* v_eqs_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1687_, v_env_1688_, v_idx_1689_, v_eqs_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1693_, lean_object* v_env_1694_, lean_object* v_idx_1695_, lean_object* v_eqs_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1693_, v_env_1694_, v_idx_1695_, v_eqs_1696_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1703_, lean_object* v_env_1704_, lean_object* v_idx_1705_, lean_object* v_eqs_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1703_, v_env_1704_, v_idx_1705_, v_eqs_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1716_; lean_object* v_env_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; 
v___x_1716_ = lean_st_ref_get(v_a_1714_);
v_env_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc_ref_n(v_env_1717_, 3);
lean_dec(v___x_1716_);
v___x_1718_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1713_);
v___x_1719_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1717_, v_declName_1713_, v___x_1718_);
v___x_1720_ = 1;
lean_inc(v___x_1719_);
v___x_1721_ = l_Lean_Environment_contains(v_env_1717_, v___x_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v___x_1719_);
lean_dec_ref(v_env_1717_);
lean_dec(v_declName_1713_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_mk_empty_array_with_capacity(v___x_1724_);
v___x_1726_ = lean_array_push(v___x_1725_, v___x_1719_);
lean_inc(v_declName_1713_);
v___x_1727_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1713_, v_env_1717_, v___x_1724_, v___x_1726_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc_n(v_a_1728_, 2);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1713_, v_a_1728_, v_a_1714_);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v___x_1729_, 0);
lean_dec(v_unused_1738_);
v___x_1731_ = v___x_1729_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v___x_1729_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1728_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_declName_1713_);
v_a_1739_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1727_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1727_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1747_, v_a_1748_);
lean_dec(v_a_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1751_, v_a_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1765_, lean_object* v_localInsts_1766_, lean_object* v_x_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1765_, v_localInsts_1766_, v_x_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1773_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1773_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1790_, lean_object* v_localInsts_1791_, lean_object* v_x_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1790_, v_localInsts_1791_, v_x_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1799_, lean_object* v_lctx_1800_, lean_object* v_localInsts_1801_, lean_object* v_x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1800_, v_localInsts_1801_, v_x_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_lctx_1810_, lean_object* v_localInsts_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1809_, v_lctx_1810_, v_localInsts_1811_, v_x_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
if (lean_obj_tag(v_as_x27_1823_) == 0)
{
lean_object* v___x_1830_; 
lean_dec(v_declName_1822_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_b_1824_);
return v___x_1830_;
}
else
{
lean_object* v_head_1831_; lean_object* v_tail_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref(v_b_1824_);
v_head_1831_ = lean_ctor_get(v_as_x27_1823_, 0);
v_tail_1832_ = lean_ctor_get(v_as_x27_1823_, 1);
v___x_1833_ = lean_box(0);
v___x_1834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1831_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v_declName_1822_);
v___x_1835_ = lean_apply_6(v_head_1831_, v_declName_1822_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, lean_box(0));
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
if (lean_obj_tag(v_a_1836_) == 1)
{
lean_object* v_val_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1847_; 
v_val_1837_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_val_1837_);
v___x_1838_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1822_, v_val_1837_, v___y_1828_);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1838_, 0);
lean_dec(v_unused_1848_);
v___x_1840_ = v___x_1838_;
v_isShared_1841_ = v_isSharedCheck_1847_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v___x_1838_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1847_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_a_1836_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1833_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1843_);
v___x_1845_ = v___x_1840_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_dec(v_a_1836_);
v_as_x27_1823_ = v_tail_1832_;
v_b_1824_ = v___x_1834_;
goto _start;
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_declName_1822_);
v_a_1850_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1835_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1835_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1858_, lean_object* v_as_x27_1859_, lean_object* v_b_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1858_, v_as_x27_1859_, v_b_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v_as_x27_1859_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
lean_inc(v_declName_1867_);
v___x_1873_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1911_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1911_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1911_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_unbox(v_a_1874_);
lean_dec(v_a_1874_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_dec(v_declName_1867_);
v___x_1879_ = lean_box(0);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
else
{
lean_object* v___x_1883_; 
lean_del_object(v___x_1876_);
lean_inc(v_declName_1867_);
v___x_1883_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1867_, v___y_1871_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
if (lean_obj_tag(v_a_1884_) == 1)
{
lean_dec(v_declName_1867_);
return v___x_1883_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1886_ = lean_st_ref_get(v___x_1885_);
v___x_1887_ = lean_box(0);
v___x_1888_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1889_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1867_, v___x_1886_, v___x_1888_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___x_1886_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1902_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_fst_1894_; 
v_fst_1894_ = lean_ctor_get(v_a_1890_, 0);
lean_inc(v_fst_1894_);
lean_dec(v_a_1890_);
if (lean_obj_tag(v_fst_1894_) == 0)
{
lean_object* v___x_1896_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1887_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1887_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v_val_1898_; lean_object* v___x_1900_; 
v_val_1898_ = lean_ctor_get(v_fst_1894_, 0);
lean_inc(v_val_1898_);
lean_dec_ref_known(v_fst_1894_, 1);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_val_1898_);
v___x_1900_ = v___x_1892_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_val_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1903_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1889_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1889_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
else
{
lean_dec(v_declName_1867_);
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_declName_1867_);
v_a_1912_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1873_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1873_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1929_ = lean_box(1);
v___x_1930_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___x_1930_);
lean_ctor_set(v___x_1932_, 2, v___x_1929_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___f_1941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1941_, 0, v_declName_1935_);
v___x_1942_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1944_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1942_, v___x_1943_, v___f_1941_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1952_, lean_object* v_as_1953_, lean_object* v_as_x27_1954_, lean_object* v_b_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1952_, v_as_x27_1954_, v_b_1955_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1963_, lean_object* v_as_1964_, lean_object* v_as_x27_1965_, lean_object* v_b_1966_, lean_object* v_a_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1963_, v_as_1964_, v_as_x27_1965_, v_b_1966_, v_a_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v_as_x27_1965_);
lean_dec(v_as_1964_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1980_ = lean_unsigned_to_nat(32u);
v___x_1981_ = lean_mk_empty_array_with_capacity(v___x_1980_);
lean_dec_ref(v___x_1981_);
v___x_1982_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1974_);
v___x_1984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1984_, 0, v_declName_1974_);
v___x_1985_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1985_, 0, lean_box(0));
lean_closure_set(v___x_1985_, 1, v_declName_1974_);
lean_closure_set(v___x_1985_, 2, v___x_1984_);
v___x_1986_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1982_, v___x_1983_, v___x_1985_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
return v_res_1993_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_1994_, lean_object* v_opt_1995_){
_start:
{
lean_object* v_name_1996_; lean_object* v_defValue_1997_; lean_object* v_map_1998_; lean_object* v___x_1999_; 
v_name_1996_ = lean_ctor_get(v_opt_1995_, 0);
v_defValue_1997_ = lean_ctor_get(v_opt_1995_, 1);
v_map_1998_ = lean_ctor_get(v_opts_1994_, 0);
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1998_, v_name_1996_);
if (lean_obj_tag(v___x_1999_) == 0)
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_unbox(v_defValue_1997_);
return v___x_2000_;
}
else
{
lean_object* v_val_2001_; 
v_val_2001_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v___x_1999_, 1);
if (lean_obj_tag(v_val_2001_) == 1)
{
uint8_t v_v_2002_; 
v_v_2002_ = lean_ctor_get_uint8(v_val_2001_, 0);
lean_dec_ref_known(v_val_2001_, 0);
return v_v_2002_;
}
else
{
uint8_t v___x_2003_; 
lean_dec(v_val_2001_);
v___x_2003_ = lean_unbox(v_defValue_1997_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_2004_, lean_object* v_opt_2005_){
_start:
{
uint8_t v_res_2006_; lean_object* v_r_2007_; 
v_res_2006_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2004_, v_opt_2005_);
lean_dec_ref(v_opt_2005_);
lean_dec_ref(v_opts_2004_);
v_r_2007_ = lean_box(v_res_2006_);
return v_r_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2008_, lean_object* v_as_2009_, size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_b_2012_){
_start:
{
lean_object* v_a_2015_; uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_b_2012_);
return v___x_2020_;
}
else
{
lean_object* v_a_2021_; lean_object* v_name_2022_; lean_object* v_defValue_2023_; uint8_t v___x_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2035_; 
v_a_2021_ = lean_array_uget(v_as_2009_, v_i_2011_);
v_name_2022_ = lean_ctor_get(v_a_2021_, 0);
lean_inc(v_name_2022_);
v_defValue_2023_ = lean_ctor_get(v_a_2021_, 1);
lean_inc(v_defValue_2023_);
v___x_2024_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2008_, v_a_2021_);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; lean_object* v_unused_2037_; 
v_unused_2036_ = lean_ctor_get(v_a_2021_, 1);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_a_2021_, 0);
lean_dec(v_unused_2037_);
v___x_2026_ = v_a_2021_;
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
else
{
lean_dec(v_a_2021_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_unbox(v_defValue_2023_);
lean_dec(v_defValue_2023_);
if (v___x_2034_ == 0)
{
if (v___x_2024_ == 0)
{
lean_del_object(v___x_2026_);
lean_dec(v_name_2022_);
v_a_2015_ = v_b_2012_;
goto v___jp_2014_;
}
else
{
goto v___jp_2028_;
}
}
else
{
if (v___x_2024_ == 0)
{
goto v___jp_2028_;
}
else
{
lean_del_object(v___x_2026_);
lean_dec(v_name_2022_);
v_a_2015_ = v_b_2012_;
goto v___jp_2014_;
}
}
v___jp_2028_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2029_, 0, v___x_2024_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 1, v___x_2029_);
v___x_2031_ = v___x_2026_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_name_2022_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_array_push(v_b_2012_, v___x_2031_);
v_a_2015_ = v___x_2032_;
goto v___jp_2014_;
}
}
}
}
v___jp_2014_:
{
size_t v___x_2016_; size_t v___x_2017_; 
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_add(v_i_2011_, v___x_2016_);
v_i_2011_ = v___x_2017_;
v_b_2012_ = v_a_2015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2038_, lean_object* v_as_2039_, lean_object* v_sz_2040_, lean_object* v_i_2041_, lean_object* v_b_2042_, lean_object* v___y_2043_){
_start:
{
size_t v_sz_boxed_2044_; size_t v_i_boxed_2045_; lean_object* v_res_2046_; 
v_sz_boxed_2044_ = lean_unbox_usize(v_sz_2040_);
lean_dec(v_sz_2040_);
v_i_boxed_2045_ = lean_unbox_usize(v_i_2041_);
lean_dec(v_i_2041_);
v_res_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2038_, v_as_2039_, v_sz_boxed_2044_, v_i_boxed_2045_, v_b_2042_);
lean_dec_ref(v_as_2039_);
lean_dec_ref(v___x_2038_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v_env_2054_; uint8_t v___x_2055_; lean_object* v_env_2056_; lean_object* v___x_2057_; lean_object* v_toCold_2058_; lean_object* v_mctx_2059_; lean_object* v_lctx_2060_; lean_object* v_options_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2053_ = lean_st_ref_get(v___y_2051_);
v_env_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_ref(v_env_2054_);
lean_dec(v___x_2053_);
v___x_2055_ = 0;
v_env_2056_ = l_Lean_Environment_setRecordingDeps(v_env_2054_, v___x_2055_);
v___x_2057_ = lean_st_ref_get(v___y_2049_);
v_toCold_2058_ = lean_ctor_get(v___y_2050_, 0);
v_mctx_2059_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_ref(v_mctx_2059_);
lean_dec(v___x_2057_);
v_lctx_2060_ = lean_ctor_get(v___y_2048_, 2);
v_options_2061_ = lean_ctor_get(v_toCold_2058_, 2);
lean_inc_ref(v_options_2061_);
lean_inc_ref(v_lctx_2060_);
v___x_2062_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2062_, 0, v_env_2056_);
lean_ctor_set(v___x_2062_, 1, v_mctx_2059_);
lean_ctor_set(v___x_2062_, 2, v_lctx_2060_);
lean_ctor_set(v___x_2062_, 3, v_options_2061_);
v___x_2063_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_msgData_2047_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2071_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2072_; double v___x_2073_; 
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_float_of_nat(v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2077_, lean_object* v_msg_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_ref_2084_; lean_object* v___x_2085_; lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2131_; 
v_ref_2084_ = lean_ctor_get(v___y_2081_, 2);
v___x_2085_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2131_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2131_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v_traceState_2091_; lean_object* v_env_2092_; lean_object* v_nextMacroScope_2093_; lean_object* v_ngen_2094_; lean_object* v_auxDeclNGen_2095_; lean_object* v_cache_2096_; lean_object* v_recordedDeps_2097_; lean_object* v_messages_2098_; lean_object* v_infoState_2099_; lean_object* v_snapshotTasks_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2130_; 
v___x_2090_ = lean_st_ref_take(v___y_2082_);
v_traceState_2091_ = lean_ctor_get(v___x_2090_, 4);
v_env_2092_ = lean_ctor_get(v___x_2090_, 0);
v_nextMacroScope_2093_ = lean_ctor_get(v___x_2090_, 1);
v_ngen_2094_ = lean_ctor_get(v___x_2090_, 2);
v_auxDeclNGen_2095_ = lean_ctor_get(v___x_2090_, 3);
v_cache_2096_ = lean_ctor_get(v___x_2090_, 5);
v_recordedDeps_2097_ = lean_ctor_get(v___x_2090_, 6);
v_messages_2098_ = lean_ctor_get(v___x_2090_, 7);
v_infoState_2099_ = lean_ctor_get(v___x_2090_, 8);
v_snapshotTasks_2100_ = lean_ctor_get(v___x_2090_, 9);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2102_ = v___x_2090_;
v_isShared_2103_ = v_isSharedCheck_2130_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_snapshotTasks_2100_);
lean_inc(v_infoState_2099_);
lean_inc(v_messages_2098_);
lean_inc(v_recordedDeps_2097_);
lean_inc(v_cache_2096_);
lean_inc(v_traceState_2091_);
lean_inc(v_auxDeclNGen_2095_);
lean_inc(v_ngen_2094_);
lean_inc(v_nextMacroScope_2093_);
lean_inc(v_env_2092_);
lean_dec(v___x_2090_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2130_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint64_t v_tid_2104_; lean_object* v_traces_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2129_; 
v_tid_2104_ = lean_ctor_get_uint64(v_traceState_2091_, sizeof(void*)*1);
v_traces_2105_ = lean_ctor_get(v_traceState_2091_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_traceState_2091_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2107_ = v_traceState_2091_;
v_isShared_2108_ = v_isSharedCheck_2129_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_traces_2105_);
lean_dec(v_traceState_2091_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2129_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; double v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2112_ = 0;
v___x_2113_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2114_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2114_, 0, v_cls_2077_);
lean_ctor_set(v___x_2114_, 1, v___x_2110_);
lean_ctor_set(v___x_2114_, 2, v___x_2113_);
lean_ctor_set_float(v___x_2114_, sizeof(void*)*3, v___x_2111_);
lean_ctor_set_float(v___x_2114_, sizeof(void*)*3 + 8, v___x_2111_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*3 + 16, v___x_2112_);
v___x_2115_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2116_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v_a_2086_);
lean_ctor_set(v___x_2116_, 2, v___x_2115_);
lean_inc(v_ref_2084_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v_ref_2084_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = l_Lean_PersistentArray_push___redArg(v_traces_2105_, v___x_2117_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2118_);
v___x_2120_ = v___x_2107_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2118_);
lean_ctor_set_uint64(v_reuseFailAlloc_2128_, sizeof(void*)*1, v_tid_2104_);
v___x_2120_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v___x_2120_);
v___x_2122_ = v___x_2102_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_env_2092_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_nextMacroScope_2093_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_ngen_2094_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_auxDeclNGen_2095_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2127_, 5, v_cache_2096_);
lean_ctor_set(v_reuseFailAlloc_2127_, 6, v_recordedDeps_2097_);
lean_ctor_set(v_reuseFailAlloc_2127_, 7, v_messages_2098_);
lean_ctor_set(v_reuseFailAlloc_2127_, 8, v_infoState_2099_);
lean_ctor_set(v_reuseFailAlloc_2127_, 9, v_snapshotTasks_2100_);
v___x_2122_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_st_ref_put(v___y_2082_, v___x_2122_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2109_);
v___x_2125_ = v___x_2088_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2109_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2132_, lean_object* v_msg_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2132_, v_msg_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2139_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2142_; size_t v_sz_2143_; 
v___x_2142_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2143_ = lean_array_size(v___x_2142_);
return v_sz_2143_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2145_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
lean_ctor_set(v___x_2145_, 2, v___x_2144_);
lean_ctor_set(v___x_2145_, 3, v___x_2144_);
lean_ctor_set(v___x_2145_, 4, v___x_2144_);
lean_ctor_set(v___x_2145_, 5, v___x_2144_);
lean_ctor_set(v___x_2145_, 6, v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2154_ = l_Lean_Name_append(v___x_2153_, v___x_2152_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2157_ = l_Lean_stringToMessageData(v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; size_t v_sz_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2164_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2161_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2167_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2168_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2164_, v___x_2167_, v_sz_2168_, v___x_2169_, v___x_2166_);
lean_dec_ref(v___x_2164_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2234_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2234_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2234_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; uint8_t v___x_2176_; lean_object* v___y_2178_; lean_object* v___y_2179_; 
v___x_2175_ = lean_array_get_size(v_a_2171_);
v___x_2176_ = lean_nat_dec_eq(v___x_2175_, v___x_2165_);
if (v___x_2176_ == 0)
{
lean_object* v_toCold_2221_; lean_object* v_options_2222_; uint8_t v_hasTrace_2223_; 
v_toCold_2221_ = lean_ctor_get(v_a_2161_, 0);
v_options_2222_ = lean_ctor_get(v_toCold_2221_, 2);
v_hasTrace_2223_ = lean_ctor_get_uint8(v_options_2222_, sizeof(void*)*1);
if (v_hasTrace_2223_ == 0)
{
v___y_2178_ = v_a_2160_;
v___y_2179_ = v_a_2162_;
goto v___jp_2177_;
}
else
{
lean_object* v_inheritedTraceOptions_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v_inheritedTraceOptions_2224_ = lean_ctor_get(v_toCold_2221_, 11);
v___x_2225_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2226_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2227_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2224_, v_options_2222_, v___x_2226_);
if (v___x_2227_ == 0)
{
v___y_2178_ = v_a_2160_;
v___y_2179_ = v_a_2162_;
goto v___jp_2177_;
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2228_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2158_);
v___x_2229_ = l_Lean_MessageData_ofName(v_declName_2158_);
v___x_2230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2225_, v___x_2230_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_dec_ref_known(v___x_2231_, 1);
v___y_2178_ = v_a_2160_;
v___y_2179_ = v_a_2162_;
goto v___jp_2177_;
}
else
{
lean_del_object(v___x_2173_);
lean_dec(v_a_2171_);
lean_dec(v_declName_2158_);
return v___x_2231_;
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_del_object(v___x_2173_);
lean_dec(v_a_2171_);
lean_dec(v_declName_2158_);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
v___jp_2177_:
{
lean_object* v___x_2180_; lean_object* v_env_2181_; lean_object* v_nextMacroScope_2182_; lean_object* v_ngen_2183_; lean_object* v_auxDeclNGen_2184_; lean_object* v_traceState_2185_; lean_object* v_recordedDeps_2186_; lean_object* v_messages_2187_; lean_object* v_infoState_2188_; lean_object* v_snapshotTasks_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2219_; 
v___x_2180_ = lean_st_ref_take(v___y_2179_);
v_env_2181_ = lean_ctor_get(v___x_2180_, 0);
v_nextMacroScope_2182_ = lean_ctor_get(v___x_2180_, 1);
v_ngen_2183_ = lean_ctor_get(v___x_2180_, 2);
v_auxDeclNGen_2184_ = lean_ctor_get(v___x_2180_, 3);
v_traceState_2185_ = lean_ctor_get(v___x_2180_, 4);
v_recordedDeps_2186_ = lean_ctor_get(v___x_2180_, 6);
v_messages_2187_ = lean_ctor_get(v___x_2180_, 7);
v_infoState_2188_ = lean_ctor_get(v___x_2180_, 8);
v_snapshotTasks_2189_ = lean_ctor_get(v___x_2180_, 9);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; 
v_unused_2220_ = lean_ctor_get(v___x_2180_, 5);
lean_dec(v_unused_2220_);
v___x_2191_ = v___x_2180_;
v_isShared_2192_ = v_isSharedCheck_2219_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_snapshotTasks_2189_);
lean_inc(v_infoState_2188_);
lean_inc(v_messages_2187_);
lean_inc(v_recordedDeps_2186_);
lean_inc(v_traceState_2185_);
lean_inc(v_auxDeclNGen_2184_);
lean_inc(v_ngen_2183_);
lean_inc(v_nextMacroScope_2182_);
lean_inc(v_env_2181_);
lean_dec(v___x_2180_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2219_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2193_ = l_Lean_Meta_eqnOptionsExt;
v___x_2194_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2193_, v_env_2181_, v_declName_2158_, v_a_2171_, v___x_2176_);
v___x_2195_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 5, v___x_2195_);
lean_ctor_set(v___x_2191_, 0, v___x_2194_);
v___x_2197_ = v___x_2191_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_nextMacroScope_2182_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_ngen_2183_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v_auxDeclNGen_2184_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v_traceState_2185_);
lean_ctor_set(v_reuseFailAlloc_2218_, 5, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2218_, 6, v_recordedDeps_2186_);
lean_ctor_set(v_reuseFailAlloc_2218_, 7, v_messages_2187_);
lean_ctor_set(v_reuseFailAlloc_2218_, 8, v_infoState_2188_);
lean_ctor_set(v_reuseFailAlloc_2218_, 9, v_snapshotTasks_2189_);
v___x_2197_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_mctx_2200_; lean_object* v_zetaDeltaFVarIds_2201_; lean_object* v_postponed_2202_; lean_object* v_diag_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2216_; 
v___x_2198_ = lean_st_ref_put(v___y_2179_, v___x_2197_);
v___x_2199_ = lean_st_ref_take(v___y_2178_);
v_mctx_2200_ = lean_ctor_get(v___x_2199_, 0);
v_zetaDeltaFVarIds_2201_ = lean_ctor_get(v___x_2199_, 2);
v_postponed_2202_ = lean_ctor_get(v___x_2199_, 3);
v_diag_2203_ = lean_ctor_get(v___x_2199_, 4);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2199_, 1);
lean_dec(v_unused_2217_);
v___x_2205_ = v___x_2199_;
v_isShared_2206_ = v_isSharedCheck_2216_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_diag_2203_);
lean_inc(v_postponed_2202_);
lean_inc(v_zetaDeltaFVarIds_2201_);
lean_inc(v_mctx_2200_);
lean_dec(v___x_2199_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2216_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___x_2208_);
v___x_2210_ = v___x_2205_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_mctx_2200_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_zetaDeltaFVarIds_2201_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_postponed_2202_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_diag_2203_);
v___x_2210_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_st_ref_put(v___y_2178_, v___x_2210_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2207_);
v___x_2213_ = v___x_2173_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2207_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
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
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_declName_2158_);
v_a_2235_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2170_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2170_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2250_, lean_object* v_as_2251_, size_t v_sz_2252_, size_t v_i_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2250_, v_as_2251_, v_sz_2252_, v_i_2253_, v_b_2254_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2261_, lean_object* v_as_2262_, lean_object* v_sz_2263_, lean_object* v_i_2264_, lean_object* v_b_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2263_);
lean_dec(v_sz_2263_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2261_, v_as_2262_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v_as_2262_);
lean_dec_ref(v___x_2261_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_st_mk_ref(v___x_2275_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2280_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = l_Lean_initializing();
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec_ref(v_f_2280_);
v___x_2283_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2285_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2286_ = lean_st_ref_take(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_f_2280_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_st_ref_put(v___x_2285_, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2290_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2296_, lean_object* v_as_x27_2297_, lean_object* v_b_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
if (lean_obj_tag(v_as_x27_2297_) == 0)
{
lean_object* v___x_2304_; 
lean_dec(v_declName_2296_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_b_2298_);
return v___x_2304_;
}
else
{
lean_object* v_head_2305_; lean_object* v_tail_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
lean_dec_ref(v_b_2298_);
v_head_2305_ = lean_ctor_get(v_as_x27_2297_, 0);
v_tail_2306_ = lean_ctor_get(v_as_x27_2297_, 1);
v___x_2307_ = lean_box(0);
v___x_2308_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2305_);
lean_inc(v___y_2302_);
lean_inc_ref(v___y_2301_);
lean_inc(v___y_2300_);
lean_inc_ref(v___y_2299_);
lean_inc(v_declName_2296_);
v___x_2309_ = lean_apply_6(v_head_2305_, v_declName_2296_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, lean_box(0));
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2320_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2320_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2320_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
if (lean_obj_tag(v_a_2310_) == 1)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
lean_dec(v_declName_2296_);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_a_2310_);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v___x_2307_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2315_);
v___x_2317_ = v___x_2312_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
else
{
lean_del_object(v___x_2312_);
lean_dec(v_a_2310_);
v_as_x27_2297_ = v_tail_2306_;
v_b_2298_ = v___x_2308_;
goto _start;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_declName_2296_);
v_a_2321_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2309_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2309_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2329_, lean_object* v_as_x27_2330_, lean_object* v_b_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2329_, v_as_x27_2330_, v_b_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v_as_x27_2330_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2338_, lean_object* v_declName_2339_, uint8_t v_nonRec_2340_, lean_object* v___x_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2350_; lean_object* v_env_2351_; uint8_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2350_ = lean_st_ref_get(v___y_2345_);
v_env_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc_ref(v_env_2351_);
lean_dec(v___x_2350_);
v___x_2352_ = 1;
lean_inc(v___x_2338_);
v___x_2353_ = l_Lean_Environment_contains(v_env_2351_, v___x_2338_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec(v___x_2338_);
lean_inc(v_declName_2339_);
v___x_2354_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2339_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
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
lean_dec_ref(v___x_2341_);
lean_dec(v_declName_2339_);
goto v___jp_2347_;
}
else
{
lean_object* v___x_2357_; 
lean_inc(v_declName_2339_);
v___x_2357_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2339_, v___y_2345_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; uint8_t v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2359_ = lean_unbox(v_a_2358_);
lean_dec(v_a_2358_);
if (v___x_2359_ == 0)
{
if (v_nonRec_2340_ == 0)
{
lean_dec_ref(v___x_2341_);
lean_dec(v_declName_2339_);
goto v___jp_2347_;
}
else
{
lean_object* v___x_2360_; lean_object* v_env_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2360_ = lean_st_ref_get(v___y_2345_);
v_env_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc_ref(v_env_2361_);
lean_dec(v___x_2360_);
lean_inc(v_declName_2339_);
v___x_2362_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2361_, v_declName_2339_, v___x_2341_);
v___x_2363_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2339_, v___x_2362_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2363_;
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec_ref(v___x_2341_);
v___x_2364_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2365_ = lean_st_ref_get(v___x_2364_);
v___x_2366_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2367_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2339_, v___x_2365_, v___x_2366_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___x_2365_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2377_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2377_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2377_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_fst_2372_; 
v_fst_2372_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_fst_2372_);
lean_dec(v_a_2368_);
if (lean_obj_tag(v_fst_2372_) == 0)
{
lean_del_object(v___x_2370_);
goto v___jp_2347_;
}
else
{
lean_object* v_val_2373_; lean_object* v___x_2375_; 
v_val_2373_ = lean_ctor_get(v_fst_2372_, 0);
lean_inc(v_val_2373_);
lean_dec_ref_known(v_fst_2372_, 1);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v_val_2373_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_val_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
v_a_2378_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2367_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2367_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v___x_2341_);
lean_dec(v_declName_2339_);
v_a_2386_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2357_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2357_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec_ref(v___x_2341_);
lean_dec(v_declName_2339_);
v_a_2394_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2354_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2354_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v___x_2341_);
lean_dec(v_declName_2339_);
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2338_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
return v___x_2403_;
}
v___jp_2347_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2404_, lean_object* v_declName_2405_, lean_object* v_nonRec_2406_, lean_object* v___x_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_nonRec_boxed_2413_; lean_object* v_res_2414_; 
v_nonRec_boxed_2413_ = lean_unbox(v_nonRec_2406_);
v_res_2414_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2404_, v_declName_2405_, v_nonRec_boxed_2413_, v___x_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_ref_2421_; lean_object* v___x_2422_; lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2431_; 
v_ref_2421_ = lean_ctor_get(v___y_2418_, 2);
v___x_2422_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
lean_inc(v_ref_2421_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_ref_2421_);
lean_ctor_set(v___x_2427_, 1, v_a_2423_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set_tag(v___x_2425_, 1);
lean_ctor_set(v___x_2425_, 0, v___x_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2439_, uint8_t v_isExporting_2440_, lean_object* v___x_2441_, lean_object* v___y_2442_, lean_object* v___x_2443_, lean_object* v_a_x3f_2444_){
_start:
{
lean_object* v___x_2446_; lean_object* v_env_2447_; lean_object* v_nextMacroScope_2448_; lean_object* v_ngen_2449_; lean_object* v_auxDeclNGen_2450_; lean_object* v_traceState_2451_; lean_object* v_recordedDeps_2452_; lean_object* v_messages_2453_; lean_object* v_infoState_2454_; lean_object* v_snapshotTasks_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2480_; 
v___x_2446_ = lean_st_ref_take(v___y_2439_);
v_env_2447_ = lean_ctor_get(v___x_2446_, 0);
v_nextMacroScope_2448_ = lean_ctor_get(v___x_2446_, 1);
v_ngen_2449_ = lean_ctor_get(v___x_2446_, 2);
v_auxDeclNGen_2450_ = lean_ctor_get(v___x_2446_, 3);
v_traceState_2451_ = lean_ctor_get(v___x_2446_, 4);
v_recordedDeps_2452_ = lean_ctor_get(v___x_2446_, 6);
v_messages_2453_ = lean_ctor_get(v___x_2446_, 7);
v_infoState_2454_ = lean_ctor_get(v___x_2446_, 8);
v_snapshotTasks_2455_ = lean_ctor_get(v___x_2446_, 9);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2446_, 5);
lean_dec(v_unused_2481_);
v___x_2457_ = v___x_2446_;
v_isShared_2458_ = v_isSharedCheck_2480_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_snapshotTasks_2455_);
lean_inc(v_infoState_2454_);
lean_inc(v_messages_2453_);
lean_inc(v_recordedDeps_2452_);
lean_inc(v_traceState_2451_);
lean_inc(v_auxDeclNGen_2450_);
lean_inc(v_ngen_2449_);
lean_inc(v_nextMacroScope_2448_);
lean_inc(v_env_2447_);
lean_dec(v___x_2446_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2480_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2459_ = l_Lean_Environment_setExporting(v_env_2447_, v_isExporting_2440_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 5, v___x_2441_);
lean_ctor_set(v___x_2457_, 0, v___x_2459_);
v___x_2461_ = v___x_2457_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_nextMacroScope_2448_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_ngen_2449_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_auxDeclNGen_2450_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_traceState_2451_);
lean_ctor_set(v_reuseFailAlloc_2479_, 5, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2479_, 6, v_recordedDeps_2452_);
lean_ctor_set(v_reuseFailAlloc_2479_, 7, v_messages_2453_);
lean_ctor_set(v_reuseFailAlloc_2479_, 8, v_infoState_2454_);
lean_ctor_set(v_reuseFailAlloc_2479_, 9, v_snapshotTasks_2455_);
v___x_2461_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v_mctx_2464_; lean_object* v_zetaDeltaFVarIds_2465_; lean_object* v_postponed_2466_; lean_object* v_diag_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2477_; 
v___x_2462_ = lean_st_ref_put(v___y_2439_, v___x_2461_);
v___x_2463_ = lean_st_ref_take(v___y_2442_);
v_mctx_2464_ = lean_ctor_get(v___x_2463_, 0);
v_zetaDeltaFVarIds_2465_ = lean_ctor_get(v___x_2463_, 2);
v_postponed_2466_ = lean_ctor_get(v___x_2463_, 3);
v_diag_2467_ = lean_ctor_get(v___x_2463_, 4);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2463_, 1);
lean_dec(v_unused_2478_);
v___x_2469_ = v___x_2463_;
v_isShared_2470_ = v_isSharedCheck_2477_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_diag_2467_);
lean_inc(v_postponed_2466_);
lean_inc(v_zetaDeltaFVarIds_2465_);
lean_inc(v_mctx_2464_);
lean_dec(v___x_2463_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2477_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_box(0);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 1, v___x_2443_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_mctx_2464_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_zetaDeltaFVarIds_2465_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_postponed_2466_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_diag_2467_);
v___x_2473_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_st_ref_put(v___y_2442_, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2471_);
return v___x_2475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2482_, lean_object* v_isExporting_2483_, lean_object* v___x_2484_, lean_object* v___y_2485_, lean_object* v___x_2486_, lean_object* v_a_x3f_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v_isExporting_boxed_2489_; lean_object* v_res_2490_; 
v_isExporting_boxed_2489_ = lean_unbox(v_isExporting_2483_);
v_res_2490_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2482_, v_isExporting_boxed_2489_, v___x_2484_, v___y_2485_, v___x_2486_, v_a_x3f_2487_);
lean_dec(v_a_x3f_2487_);
lean_dec(v___y_2485_);
lean_dec(v___y_2482_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2491_, uint8_t v_isExporting_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; lean_object* v_env_2499_; lean_object* v___x_2500_; uint8_t v_isModule_2501_; 
v___x_2498_ = lean_st_ref_get(v___y_2496_);
v_env_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc_ref(v_env_2499_);
lean_dec(v___x_2498_);
v___x_2500_ = l_Lean_Environment_header(v_env_2499_);
v_isModule_2501_ = lean_ctor_get_uint8(v___x_2500_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2500_);
if (v_isModule_2501_ == 0)
{
lean_object* v___x_2502_; 
lean_dec_ref(v_env_2499_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
v___x_2502_ = lean_apply_5(v_x_2491_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, lean_box(0));
return v___x_2502_;
}
else
{
uint8_t v_isExporting_2503_; 
v_isExporting_2503_ = lean_ctor_get_uint8(v_env_2499_, sizeof(void*)*13);
lean_dec_ref(v_env_2499_);
if (v_isExporting_2492_ == 0)
{
if (v_isExporting_2503_ == 0)
{
lean_object* v___x_2570_; 
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
v___x_2570_ = lean_apply_5(v_x_2491_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, lean_box(0));
return v___x_2570_;
}
else
{
goto v___jp_2504_;
}
}
else
{
if (v_isExporting_2503_ == 0)
{
goto v___jp_2504_;
}
else
{
lean_object* v___x_2571_; 
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
v___x_2571_ = lean_apply_5(v_x_2491_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, lean_box(0));
return v___x_2571_;
}
}
v___jp_2504_:
{
lean_object* v___x_2505_; lean_object* v_env_2506_; lean_object* v_nextMacroScope_2507_; lean_object* v_ngen_2508_; lean_object* v_auxDeclNGen_2509_; lean_object* v_traceState_2510_; lean_object* v_recordedDeps_2511_; lean_object* v_messages_2512_; lean_object* v_infoState_2513_; lean_object* v_snapshotTasks_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2568_; 
v___x_2505_ = lean_st_ref_take(v___y_2496_);
v_env_2506_ = lean_ctor_get(v___x_2505_, 0);
v_nextMacroScope_2507_ = lean_ctor_get(v___x_2505_, 1);
v_ngen_2508_ = lean_ctor_get(v___x_2505_, 2);
v_auxDeclNGen_2509_ = lean_ctor_get(v___x_2505_, 3);
v_traceState_2510_ = lean_ctor_get(v___x_2505_, 4);
v_recordedDeps_2511_ = lean_ctor_get(v___x_2505_, 6);
v_messages_2512_ = lean_ctor_get(v___x_2505_, 7);
v_infoState_2513_ = lean_ctor_get(v___x_2505_, 8);
v_snapshotTasks_2514_ = lean_ctor_get(v___x_2505_, 9);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v___x_2505_, 5);
lean_dec(v_unused_2569_);
v___x_2516_ = v___x_2505_;
v_isShared_2517_ = v_isSharedCheck_2568_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_snapshotTasks_2514_);
lean_inc(v_infoState_2513_);
lean_inc(v_messages_2512_);
lean_inc(v_recordedDeps_2511_);
lean_inc(v_traceState_2510_);
lean_inc(v_auxDeclNGen_2509_);
lean_inc(v_ngen_2508_);
lean_inc(v_nextMacroScope_2507_);
lean_inc(v_env_2506_);
lean_dec(v___x_2505_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2568_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2518_ = l_Lean_Environment_setExporting(v_env_2506_, v_isExporting_2492_);
v___x_2519_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 5, v___x_2519_);
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2521_ = v___x_2516_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_nextMacroScope_2507_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_ngen_2508_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_auxDeclNGen_2509_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_traceState_2510_);
lean_ctor_set(v_reuseFailAlloc_2567_, 5, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2567_, 6, v_recordedDeps_2511_);
lean_ctor_set(v_reuseFailAlloc_2567_, 7, v_messages_2512_);
lean_ctor_set(v_reuseFailAlloc_2567_, 8, v_infoState_2513_);
lean_ctor_set(v_reuseFailAlloc_2567_, 9, v_snapshotTasks_2514_);
v___x_2521_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_mctx_2524_; lean_object* v_zetaDeltaFVarIds_2525_; lean_object* v_postponed_2526_; lean_object* v_diag_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2565_; 
v___x_2522_ = lean_st_ref_put(v___y_2496_, v___x_2521_);
v___x_2523_ = lean_st_ref_take(v___y_2494_);
v_mctx_2524_ = lean_ctor_get(v___x_2523_, 0);
v_zetaDeltaFVarIds_2525_ = lean_ctor_get(v___x_2523_, 2);
v_postponed_2526_ = lean_ctor_get(v___x_2523_, 3);
v_diag_2527_ = lean_ctor_get(v___x_2523_, 4);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2523_, 1);
lean_dec(v_unused_2566_);
v___x_2529_ = v___x_2523_;
v_isShared_2530_ = v_isSharedCheck_2565_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_diag_2527_);
lean_inc(v_postponed_2526_);
lean_inc(v_zetaDeltaFVarIds_2525_);
lean_inc(v_mctx_2524_);
lean_dec(v___x_2523_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2565_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2531_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2531_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_mctx_2524_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_zetaDeltaFVarIds_2525_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_postponed_2526_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_diag_2527_);
v___x_2533_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; lean_object* v_r_2535_; 
v___x_2534_ = lean_st_ref_put(v___y_2494_, v___x_2533_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
v_r_2535_ = lean_apply_5(v_x_2491_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, lean_box(0));
if (lean_obj_tag(v_r_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2552_; 
v_a_2536_ = lean_ctor_get(v_r_2535_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_r_2535_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2538_ = v_r_2535_;
v_isShared_2539_ = v_isSharedCheck_2552_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v_r_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2552_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
lean_inc(v_a_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set_tag(v___x_2538_, 1);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v___x_2542_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2496_, v_isExporting_2503_, v___x_2519_, v___y_2494_, v___x_2531_, v___x_2541_);
lean_dec_ref(v___x_2541_);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v___x_2542_, 0);
lean_dec(v_unused_2550_);
v___x_2544_ = v___x_2542_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_dec(v___x_2542_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v_a_2536_);
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2536_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2553_ = lean_ctor_get(v_r_2535_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v_r_2535_, 1);
v___x_2554_ = lean_box(0);
v___x_2555_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2496_, v_isExporting_2503_, v___x_2519_, v___y_2494_, v___x_2531_, v___x_2554_);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2563_);
v___x_2557_ = v___x_2555_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_dec(v___x_2555_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set_tag(v___x_2557_, 1);
lean_ctor_set(v___x_2557_, 0, v_a_2553_);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2553_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2572_, lean_object* v_isExporting_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v_isExporting_boxed_2579_; lean_object* v_res_2580_; 
v_isExporting_boxed_2579_ = lean_unbox(v_isExporting_2573_);
v_res_2580_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2572_, v_isExporting_boxed_2579_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2581_, uint8_t v_when_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
if (v_when_2582_ == 0)
{
lean_object* v___x_2588_; 
lean_inc(v___y_2586_);
lean_inc_ref(v___y_2585_);
lean_inc(v___y_2584_);
lean_inc_ref(v___y_2583_);
v___x_2588_ = lean_apply_5(v_x_2581_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, lean_box(0));
return v___x_2588_;
}
else
{
uint8_t v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = 0;
v___x_2590_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2581_, v___x_2589_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2591_, lean_object* v_when_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
uint8_t v_when_boxed_2598_; lean_object* v_res_2599_; 
v_when_boxed_2598_ = lean_unbox(v_when_2592_);
v_res_2599_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2591_, v_when_boxed_2598_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
return v_res_2599_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2607_ = l_Lean_stringToMessageData(v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2608_, uint8_t v_nonRec_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; lean_object* v_env_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___f_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2615_ = lean_st_ref_get(v___y_2613_);
v_env_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc_ref(v_env_2616_);
lean_dec(v___x_2615_);
v___x_2617_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2608_);
v___x_2618_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2616_, v_declName_2608_, v___x_2617_);
v___x_2619_ = lean_box(v_nonRec_2609_);
lean_inc(v___x_2618_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2620_, 0, v___x_2618_);
lean_closure_set(v___f_2620_, 1, v_declName_2608_);
lean_closure_set(v___f_2620_, 2, v___x_2619_);
lean_closure_set(v___f_2620_, 3, v___x_2617_);
v___x_2621_ = 1;
v___x_2622_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2620_, v___x_2621_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
if (lean_obj_tag(v_a_2623_) == 1)
{
lean_object* v_val_2624_; uint8_t v___x_2625_; 
v_val_2624_ = lean_ctor_get(v_a_2623_, 0);
v___x_2625_ = lean_name_eq(v_val_2624_, v___x_2618_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_inc(v_val_2624_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2626_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2627_ = l_Lean_MessageData_ofName(v_val_2624_);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = l_Lean_MessageData_ofName(v___x_2618_);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2634_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_dec(v___x_2618_);
return v___x_2622_;
}
}
else
{
lean_dec(v___x_2618_);
return v___x_2622_;
}
}
else
{
lean_dec(v___x_2618_);
return v___x_2622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2644_, lean_object* v_nonRec_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
uint8_t v_nonRec_boxed_2651_; lean_object* v_res_2652_; 
v_nonRec_boxed_2651_ = lean_unbox(v_nonRec_2645_);
v_res_2652_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2644_, v_nonRec_boxed_2651_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2653_, uint8_t v_nonRec_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v___f_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2660_ = lean_box(v_nonRec_2654_);
v___f_2661_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2661_, 0, v_declName_2653_);
lean_closure_set(v___f_2661_, 1, v___x_2660_);
v___x_2662_ = lean_unsigned_to_nat(32u);
v___x_2663_ = lean_mk_empty_array_with_capacity(v___x_2662_);
lean_dec_ref(v___x_2663_);
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2665_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2666_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2664_, v___x_2665_, v___f_2661_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2667_, lean_object* v_nonRec_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
uint8_t v_nonRec_boxed_2674_; lean_object* v_res_2675_; 
v_nonRec_boxed_2674_ = lean_unbox(v_nonRec_2668_);
v_res_2675_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2667_, v_nonRec_boxed_2674_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2676_, lean_object* v_as_2677_, lean_object* v_as_x27_2678_, lean_object* v_b_2679_, lean_object* v_a_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2676_, v_as_x27_2678_, v_b_2679_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2687_, lean_object* v_as_2688_, lean_object* v_as_x27_2689_, lean_object* v_b_2690_, lean_object* v_a_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2687_, v_as_2688_, v_as_x27_2689_, v_b_2690_, v_a_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v_as_x27_2689_);
lean_dec(v_as_2688_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2698_, lean_object* v_x_2699_, uint8_t v_isExporting_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2699_, v_isExporting_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2707_, lean_object* v_x_2708_, lean_object* v_isExporting_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
uint8_t v_isExporting_boxed_2715_; lean_object* v_res_2716_; 
v_isExporting_boxed_2715_ = lean_unbox(v_isExporting_2709_);
v_res_2716_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2707_, v_x_2708_, v_isExporting_boxed_2715_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2717_, lean_object* v_x_2718_, uint8_t v_when_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2718_, v_when_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_x_2727_, lean_object* v_when_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v_when_boxed_2734_; lean_object* v_res_2735_; 
v_when_boxed_2734_ = lean_unbox(v_when_2728_);
v_res_2735_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2726_, v_x_2727_, v_when_boxed_2734_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2736_, lean_object* v_msg_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2744_, lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2744_, v_msg_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2751_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = lean_unsigned_to_nat(32u);
v___x_2753_ = lean_mk_empty_array_with_capacity(v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2755_ = ((size_t)5ULL);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = lean_unsigned_to_nat(32u);
v___x_2758_ = lean_mk_empty_array_with_capacity(v___x_2757_);
v___x_2759_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2760_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___x_2758_);
lean_ctor_set(v___x_2760_, 2, v___x_2756_);
lean_ctor_set(v___x_2760_, 3, v___x_2756_);
lean_ctor_set_usize(v___x_2760_, 4, v___x_2755_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; lean_object* v_traceState_2764_; lean_object* v_traces_2765_; lean_object* v___x_2766_; lean_object* v_traceState_2767_; lean_object* v_env_2768_; lean_object* v_nextMacroScope_2769_; lean_object* v_ngen_2770_; lean_object* v_auxDeclNGen_2771_; lean_object* v_cache_2772_; lean_object* v_recordedDeps_2773_; lean_object* v_messages_2774_; lean_object* v_infoState_2775_; lean_object* v_snapshotTasks_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2795_; 
v___x_2763_ = lean_st_ref_get(v___y_2761_);
v_traceState_2764_ = lean_ctor_get(v___x_2763_, 4);
lean_inc_ref(v_traceState_2764_);
lean_dec(v___x_2763_);
v_traces_2765_ = lean_ctor_get(v_traceState_2764_, 0);
lean_inc_ref(v_traces_2765_);
lean_dec_ref(v_traceState_2764_);
v___x_2766_ = lean_st_ref_take(v___y_2761_);
v_traceState_2767_ = lean_ctor_get(v___x_2766_, 4);
v_env_2768_ = lean_ctor_get(v___x_2766_, 0);
v_nextMacroScope_2769_ = lean_ctor_get(v___x_2766_, 1);
v_ngen_2770_ = lean_ctor_get(v___x_2766_, 2);
v_auxDeclNGen_2771_ = lean_ctor_get(v___x_2766_, 3);
v_cache_2772_ = lean_ctor_get(v___x_2766_, 5);
v_recordedDeps_2773_ = lean_ctor_get(v___x_2766_, 6);
v_messages_2774_ = lean_ctor_get(v___x_2766_, 7);
v_infoState_2775_ = lean_ctor_get(v___x_2766_, 8);
v_snapshotTasks_2776_ = lean_ctor_get(v___x_2766_, 9);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2778_ = v___x_2766_;
v_isShared_2779_ = v_isSharedCheck_2795_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_snapshotTasks_2776_);
lean_inc(v_infoState_2775_);
lean_inc(v_messages_2774_);
lean_inc(v_recordedDeps_2773_);
lean_inc(v_cache_2772_);
lean_inc(v_traceState_2767_);
lean_inc(v_auxDeclNGen_2771_);
lean_inc(v_ngen_2770_);
lean_inc(v_nextMacroScope_2769_);
lean_inc(v_env_2768_);
lean_dec(v___x_2766_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2795_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
uint64_t v_tid_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2793_; 
v_tid_2780_ = lean_ctor_get_uint64(v_traceState_2767_, sizeof(void*)*1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_traceState_2767_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v_traceState_2767_, 0);
lean_dec(v_unused_2794_);
v___x_2782_ = v_traceState_2767_;
v_isShared_2783_ = v_isSharedCheck_2793_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v_traceState_2767_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2793_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2784_);
lean_ctor_set_uint64(v_reuseFailAlloc_2792_, sizeof(void*)*1, v_tid_2780_);
v___x_2786_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2788_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 4, v___x_2786_);
v___x_2788_ = v___x_2778_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_env_2768_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_nextMacroScope_2769_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_ngen_2770_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_auxDeclNGen_2771_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2791_, 5, v_cache_2772_);
lean_ctor_set(v_reuseFailAlloc_2791_, 6, v_recordedDeps_2773_);
lean_ctor_set(v_reuseFailAlloc_2791_, 7, v_messages_2774_);
lean_ctor_set(v_reuseFailAlloc_2791_, 8, v_infoState_2775_);
lean_ctor_set(v_reuseFailAlloc_2791_, 9, v_snapshotTasks_2776_);
v___x_2788_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_st_ref_put(v___y_2761_, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_traces_2765_);
return v___x_2790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2796_);
lean_dec(v___y_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = 0;
v___x_2812_ = lean_box(v___x_2811_);
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
return v_res_2818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2821_ = l_Lean_stringToMessageData(v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2822_, lean_object* v_x_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2827_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2828_ = l_Lean_MessageData_ofName(v_name_2822_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2831_, lean_object* v_x_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2831_, v_x_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v_x_2832_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2837_){
_start:
{
if (lean_obj_tag(v_x_2837_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
v_a_2839_ = lean_ctor_get(v_x_2837_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_x_2837_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v_x_2837_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v_x_2837_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 1);
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
v_a_2847_ = lean_ctor_get(v_x_2837_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_x_2837_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v_x_2837_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v_x_2837_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set_tag(v___x_2849_, 0);
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2858_){
_start:
{
if (lean_obj_tag(v_e_2858_) == 0)
{
uint8_t v___x_2859_; 
v___x_2859_ = 2;
return v___x_2859_;
}
else
{
lean_object* v_a_2860_; uint8_t v___x_2861_; 
v_a_2860_ = lean_ctor_get(v_e_2858_, 0);
v___x_2861_ = lean_unbox(v_a_2860_);
if (v___x_2861_ == 0)
{
uint8_t v___x_2862_; 
v___x_2862_ = 1;
return v___x_2862_;
}
else
{
uint8_t v___x_2863_; 
v___x_2863_ = 0;
return v___x_2863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2864_){
_start:
{
uint8_t v_res_2865_; lean_object* v_r_2866_; 
v_res_2865_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2864_);
lean_dec_ref(v_e_2864_);
v_r_2866_ = lean_box(v_res_2865_);
return v_r_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2867_, size_t v_i_2868_, lean_object* v_bs_2869_){
_start:
{
uint8_t v___x_2870_; 
v___x_2870_ = lean_usize_dec_lt(v_i_2868_, v_sz_2867_);
if (v___x_2870_ == 0)
{
return v_bs_2869_;
}
else
{
lean_object* v_v_2871_; lean_object* v_msg_2872_; lean_object* v___x_2873_; lean_object* v_bs_x27_2874_; size_t v___x_2875_; size_t v___x_2876_; lean_object* v___x_2877_; 
v_v_2871_ = lean_array_uget_borrowed(v_bs_2869_, v_i_2868_);
v_msg_2872_ = lean_ctor_get(v_v_2871_, 1);
lean_inc_ref(v_msg_2872_);
v___x_2873_ = lean_unsigned_to_nat(0u);
v_bs_x27_2874_ = lean_array_uset(v_bs_2869_, v_i_2868_, v___x_2873_);
v___x_2875_ = ((size_t)1ULL);
v___x_2876_ = lean_usize_add(v_i_2868_, v___x_2875_);
v___x_2877_ = lean_array_uset(v_bs_x27_2874_, v_i_2868_, v_msg_2872_);
v_i_2868_ = v___x_2876_;
v_bs_2869_ = v___x_2877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2879_, lean_object* v_i_2880_, lean_object* v_bs_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2879_);
lean_dec(v_sz_2879_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2880_);
lean_dec(v_i_2880_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2882_, v_i_boxed_2883_, v_bs_2881_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2885_, lean_object* v_data_2886_, lean_object* v_ref_2887_, lean_object* v_msg_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_toCold_2892_; lean_object* v_currRecDepth_2893_; lean_object* v_ref_2894_; uint16_t v_optionFlags_2895_; uint8_t v_suppressElabErrors_2896_; uint8_t v_checkDeprecated_2897_; uint8_t v_isRecordingDeps_2898_; lean_object* v_ref_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v_traceState_2902_; lean_object* v_traces_2903_; lean_object* v___x_2904_; size_t v_sz_2905_; size_t v___x_2906_; lean_object* v___x_2907_; lean_object* v_msg_2908_; lean_object* v___x_2909_; lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2948_; 
v_toCold_2892_ = lean_ctor_get(v___y_2889_, 0);
v_currRecDepth_2893_ = lean_ctor_get(v___y_2889_, 1);
v_ref_2894_ = lean_ctor_get(v___y_2889_, 2);
v_optionFlags_2895_ = lean_ctor_get_uint16(v___y_2889_, sizeof(void*)*3);
v_suppressElabErrors_2896_ = lean_ctor_get_uint8(v___y_2889_, sizeof(void*)*3 + 2);
v_checkDeprecated_2897_ = lean_ctor_get_uint8(v___y_2889_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2898_ = lean_ctor_get_uint8(v___y_2889_, sizeof(void*)*3 + 4);
v_ref_2899_ = l_Lean_replaceRef(v_ref_2887_, v_ref_2894_);
lean_inc(v_currRecDepth_2893_);
lean_inc_ref(v_toCold_2892_);
v___x_2900_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2900_, 0, v_toCold_2892_);
lean_ctor_set(v___x_2900_, 1, v_currRecDepth_2893_);
lean_ctor_set(v___x_2900_, 2, v_ref_2899_);
lean_ctor_set_uint16(v___x_2900_, sizeof(void*)*3, v_optionFlags_2895_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3 + 2, v_suppressElabErrors_2896_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3 + 3, v_checkDeprecated_2897_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3 + 4, v_isRecordingDeps_2898_);
v___x_2901_ = lean_st_ref_get(v___y_2890_);
v_traceState_2902_ = lean_ctor_get(v___x_2901_, 4);
lean_inc_ref(v_traceState_2902_);
lean_dec(v___x_2901_);
v_traces_2903_ = lean_ctor_get(v_traceState_2902_, 0);
lean_inc_ref(v_traces_2903_);
lean_dec_ref(v_traceState_2902_);
v___x_2904_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2903_);
lean_dec_ref(v_traces_2903_);
v_sz_2905_ = lean_array_size(v___x_2904_);
v___x_2906_ = ((size_t)0ULL);
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2905_, v___x_2906_, v___x_2904_);
v_msg_2908_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2908_, 0, v_data_2886_);
lean_ctor_set(v_msg_2908_, 1, v_msg_2888_);
lean_ctor_set(v_msg_2908_, 2, v___x_2907_);
v___x_2909_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2908_, v___x_2900_, v___y_2890_);
lean_dec_ref_known(v___x_2900_, 3);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2948_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2948_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v_traceState_2915_; lean_object* v_env_2916_; lean_object* v_nextMacroScope_2917_; lean_object* v_ngen_2918_; lean_object* v_auxDeclNGen_2919_; lean_object* v_cache_2920_; lean_object* v_recordedDeps_2921_; lean_object* v_messages_2922_; lean_object* v_infoState_2923_; lean_object* v_snapshotTasks_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2947_; 
v___x_2914_ = lean_st_ref_take(v___y_2890_);
v_traceState_2915_ = lean_ctor_get(v___x_2914_, 4);
v_env_2916_ = lean_ctor_get(v___x_2914_, 0);
v_nextMacroScope_2917_ = lean_ctor_get(v___x_2914_, 1);
v_ngen_2918_ = lean_ctor_get(v___x_2914_, 2);
v_auxDeclNGen_2919_ = lean_ctor_get(v___x_2914_, 3);
v_cache_2920_ = lean_ctor_get(v___x_2914_, 5);
v_recordedDeps_2921_ = lean_ctor_get(v___x_2914_, 6);
v_messages_2922_ = lean_ctor_get(v___x_2914_, 7);
v_infoState_2923_ = lean_ctor_get(v___x_2914_, 8);
v_snapshotTasks_2924_ = lean_ctor_get(v___x_2914_, 9);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2926_ = v___x_2914_;
v_isShared_2927_ = v_isSharedCheck_2947_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_snapshotTasks_2924_);
lean_inc(v_infoState_2923_);
lean_inc(v_messages_2922_);
lean_inc(v_recordedDeps_2921_);
lean_inc(v_cache_2920_);
lean_inc(v_traceState_2915_);
lean_inc(v_auxDeclNGen_2919_);
lean_inc(v_ngen_2918_);
lean_inc(v_nextMacroScope_2917_);
lean_inc(v_env_2916_);
lean_dec(v___x_2914_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2947_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
uint64_t v_tid_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2945_; 
v_tid_2928_ = lean_ctor_get_uint64(v_traceState_2915_, sizeof(void*)*1);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_traceState_2915_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v_traceState_2915_, 0);
lean_dec(v_unused_2946_);
v___x_2930_ = v_traceState_2915_;
v_isShared_2931_ = v_isSharedCheck_2945_;
goto v_resetjp_2929_;
}
else
{
lean_dec(v_traceState_2915_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2945_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2933_, 0, v_ref_2887_);
lean_ctor_set(v___x_2933_, 1, v_a_2910_);
v___x_2934_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2885_, v___x_2933_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2934_);
v___x_2936_ = v___x_2930_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2934_);
lean_ctor_set_uint64(v_reuseFailAlloc_2944_, sizeof(void*)*1, v_tid_2928_);
v___x_2936_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2938_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 4, v___x_2936_);
v___x_2938_ = v___x_2926_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_env_2916_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_nextMacroScope_2917_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_ngen_2918_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_auxDeclNGen_2919_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v___x_2936_);
lean_ctor_set(v_reuseFailAlloc_2943_, 5, v_cache_2920_);
lean_ctor_set(v_reuseFailAlloc_2943_, 6, v_recordedDeps_2921_);
lean_ctor_set(v_reuseFailAlloc_2943_, 7, v_messages_2922_);
lean_ctor_set(v_reuseFailAlloc_2943_, 8, v_infoState_2923_);
lean_ctor_set(v_reuseFailAlloc_2943_, 9, v_snapshotTasks_2924_);
v___x_2938_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_st_ref_put(v___y_2890_, v___x_2938_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2932_);
v___x_2941_ = v___x_2912_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2932_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2949_, lean_object* v_data_2950_, lean_object* v_ref_2951_, lean_object* v_msg_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2949_, v_data_2950_, v_ref_2951_, v_msg_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
return v_res_2956_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2959_ = l_Lean_stringToMessageData(v___x_2958_);
return v___x_2959_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2960_; double v___x_2961_; 
v___x_2960_ = lean_unsigned_to_nat(1000u);
v___x_2961_ = lean_float_of_nat(v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2962_, uint8_t v_collapsed_2963_, lean_object* v_tag_2964_, lean_object* v_opts_2965_, uint8_t v_clsEnabled_2966_, lean_object* v_oldTraces_2967_, lean_object* v_msg_2968_, lean_object* v_resStartStop_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_fst_2973_; lean_object* v_snd_2974_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v_data_2978_; lean_object* v_fst_2989_; lean_object* v_snd_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___y_2994_; lean_object* v_a_2995_; uint8_t v___y_3010_; double v___y_3042_; 
v_fst_2973_ = lean_ctor_get(v_resStartStop_2969_, 0);
lean_inc(v_fst_2973_);
v_snd_2974_ = lean_ctor_get(v_resStartStop_2969_, 1);
lean_inc(v_snd_2974_);
lean_dec_ref(v_resStartStop_2969_);
v_fst_2989_ = lean_ctor_get(v_snd_2974_, 0);
lean_inc(v_fst_2989_);
v_snd_2990_ = lean_ctor_get(v_snd_2974_, 1);
lean_inc(v_snd_2990_);
lean_dec(v_snd_2974_);
v___x_2991_ = l_Lean_trace_profiler;
v___x_2992_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2965_, v___x_2991_);
if (v___x_2992_ == 0)
{
v___y_3010_ = v___x_2992_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3048_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2965_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; double v___x_3051_; double v___x_3052_; double v___x_3053_; 
v___x_3049_ = l_Lean_trace_profiler_threshold;
v___x_3050_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2965_, v___x_3049_);
v___x_3051_ = lean_float_of_nat(v___x_3050_);
v___x_3052_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3053_ = lean_float_div(v___x_3051_, v___x_3052_);
v___y_3042_ = v___x_3053_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; double v___x_3056_; 
v___x_3054_ = l_Lean_trace_profiler_threshold;
v___x_3055_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2965_, v___x_3054_);
v___x_3056_ = lean_float_of_nat(v___x_3055_);
v___y_3042_ = v___x_3056_;
goto v___jp_3041_;
}
}
v___jp_2975_:
{
lean_object* v___x_2979_; 
lean_inc(v___y_2976_);
v___x_2979_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2967_, v_data_2978_, v___y_2976_, v___y_2977_, v___y_2970_, v___y_2971_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2980_; 
lean_dec_ref_known(v___x_2979_, 1);
v___x_2980_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2973_);
return v___x_2980_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_fst_2973_);
v_a_2981_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
v___jp_2993_:
{
uint8_t v_result_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; double v___x_2999_; lean_object* v_data_3000_; 
v_result_2996_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2973_);
v___x_2997_ = lean_box(v_result_2996_);
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
v___x_2999_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_2964_);
lean_inc_ref(v___x_2998_);
lean_inc(v_cls_2962_);
v_data_3000_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3000_, 0, v_cls_2962_);
lean_ctor_set(v_data_3000_, 1, v___x_2998_);
lean_ctor_set(v_data_3000_, 2, v_tag_2964_);
lean_ctor_set_float(v_data_3000_, sizeof(void*)*3, v___x_2999_);
lean_ctor_set_float(v_data_3000_, sizeof(void*)*3 + 8, v___x_2999_);
lean_ctor_set_uint8(v_data_3000_, sizeof(void*)*3 + 16, v_collapsed_2963_);
if (v___x_2992_ == 0)
{
lean_dec_ref_known(v___x_2998_, 1);
lean_dec(v_snd_2990_);
lean_dec(v_fst_2989_);
lean_dec_ref(v_tag_2964_);
lean_dec(v_cls_2962_);
v___y_2976_ = v___y_2994_;
v___y_2977_ = v_a_2995_;
v_data_2978_ = v_data_3000_;
goto v___jp_2975_;
}
else
{
lean_object* v_data_3001_; double v___x_3002_; double v___x_3003_; 
lean_dec_ref_known(v_data_3000_, 3);
v_data_3001_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3001_, 0, v_cls_2962_);
lean_ctor_set(v_data_3001_, 1, v___x_2998_);
lean_ctor_set(v_data_3001_, 2, v_tag_2964_);
v___x_3002_ = lean_unbox_float(v_fst_2989_);
lean_dec(v_fst_2989_);
lean_ctor_set_float(v_data_3001_, sizeof(void*)*3, v___x_3002_);
v___x_3003_ = lean_unbox_float(v_snd_2990_);
lean_dec(v_snd_2990_);
lean_ctor_set_float(v_data_3001_, sizeof(void*)*3 + 8, v___x_3003_);
lean_ctor_set_uint8(v_data_3001_, sizeof(void*)*3 + 16, v_collapsed_2963_);
v___y_2976_ = v___y_2994_;
v___y_2977_ = v_a_2995_;
v_data_2978_ = v_data_3001_;
goto v___jp_2975_;
}
}
v___jp_3004_:
{
lean_object* v_ref_3005_; lean_object* v___x_3006_; 
v_ref_3005_ = lean_ctor_get(v___y_2970_, 2);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc(v_fst_2973_);
v___x_3006_ = lean_apply_4(v_msg_2968_, v_fst_2973_, v___y_2970_, v___y_2971_, lean_box(0));
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___y_2994_ = v_ref_3005_;
v_a_2995_ = v_a_3007_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3008_; 
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2994_ = v_ref_3005_;
v_a_2995_ = v___x_3008_;
goto v___jp_2993_;
}
}
v___jp_3009_:
{
if (v_clsEnabled_2966_ == 0)
{
if (v___y_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v_traceState_3012_; lean_object* v_env_3013_; lean_object* v_nextMacroScope_3014_; lean_object* v_ngen_3015_; lean_object* v_auxDeclNGen_3016_; lean_object* v_cache_3017_; lean_object* v_recordedDeps_3018_; lean_object* v_messages_3019_; lean_object* v_infoState_3020_; lean_object* v_snapshotTasks_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_snd_2990_);
lean_dec(v_fst_2989_);
lean_dec_ref(v_msg_2968_);
lean_dec_ref(v_tag_2964_);
lean_dec(v_cls_2962_);
v___x_3011_ = lean_st_ref_take(v___y_2971_);
v_traceState_3012_ = lean_ctor_get(v___x_3011_, 4);
v_env_3013_ = lean_ctor_get(v___x_3011_, 0);
v_nextMacroScope_3014_ = lean_ctor_get(v___x_3011_, 1);
v_ngen_3015_ = lean_ctor_get(v___x_3011_, 2);
v_auxDeclNGen_3016_ = lean_ctor_get(v___x_3011_, 3);
v_cache_3017_ = lean_ctor_get(v___x_3011_, 5);
v_recordedDeps_3018_ = lean_ctor_get(v___x_3011_, 6);
v_messages_3019_ = lean_ctor_get(v___x_3011_, 7);
v_infoState_3020_ = lean_ctor_get(v___x_3011_, 8);
v_snapshotTasks_3021_ = lean_ctor_get(v___x_3011_, 9);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3023_ = v___x_3011_;
v_isShared_3024_ = v_isSharedCheck_3040_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_snapshotTasks_3021_);
lean_inc(v_infoState_3020_);
lean_inc(v_messages_3019_);
lean_inc(v_recordedDeps_3018_);
lean_inc(v_cache_3017_);
lean_inc(v_traceState_3012_);
lean_inc(v_auxDeclNGen_3016_);
lean_inc(v_ngen_3015_);
lean_inc(v_nextMacroScope_3014_);
lean_inc(v_env_3013_);
lean_dec(v___x_3011_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3040_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
uint64_t v_tid_3025_; lean_object* v_traces_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3039_; 
v_tid_3025_ = lean_ctor_get_uint64(v_traceState_3012_, sizeof(void*)*1);
v_traces_3026_ = lean_ctor_get(v_traceState_3012_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_traceState_3012_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3028_ = v_traceState_3012_;
v_isShared_3029_ = v_isSharedCheck_3039_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_traces_3026_);
lean_dec(v_traceState_3012_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3039_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3030_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2967_, v_traces_3026_);
lean_dec_ref(v_traces_3026_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3030_);
v___x_3032_ = v___x_3028_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3030_);
lean_ctor_set_uint64(v_reuseFailAlloc_3038_, sizeof(void*)*1, v_tid_3025_);
v___x_3032_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 4, v___x_3032_);
v___x_3034_ = v___x_3023_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_env_3013_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_nextMacroScope_3014_);
lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_ngen_3015_);
lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_auxDeclNGen_3016_);
lean_ctor_set(v_reuseFailAlloc_3037_, 4, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3037_, 5, v_cache_3017_);
lean_ctor_set(v_reuseFailAlloc_3037_, 6, v_recordedDeps_3018_);
lean_ctor_set(v_reuseFailAlloc_3037_, 7, v_messages_3019_);
lean_ctor_set(v_reuseFailAlloc_3037_, 8, v_infoState_3020_);
lean_ctor_set(v_reuseFailAlloc_3037_, 9, v_snapshotTasks_3021_);
v___x_3034_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = lean_st_ref_put(v___y_2971_, v___x_3034_);
v___x_3036_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2973_);
return v___x_3036_;
}
}
}
}
}
else
{
goto v___jp_3004_;
}
}
else
{
goto v___jp_3004_;
}
}
v___jp_3041_:
{
double v___x_3043_; double v___x_3044_; double v___x_3045_; uint8_t v___x_3046_; 
v___x_3043_ = lean_unbox_float(v_snd_2990_);
v___x_3044_ = lean_unbox_float(v_fst_2989_);
v___x_3045_ = lean_float_sub(v___x_3043_, v___x_3044_);
v___x_3046_ = lean_float_decLt(v___y_3042_, v___x_3045_);
v___y_3010_ = v___x_3046_;
goto v___jp_3009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3057_, lean_object* v_collapsed_3058_, lean_object* v_tag_3059_, lean_object* v_opts_3060_, lean_object* v_clsEnabled_3061_, lean_object* v_oldTraces_3062_, lean_object* v_msg_3063_, lean_object* v_resStartStop_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
uint8_t v_collapsed_boxed_3068_; uint8_t v_clsEnabled_boxed_3069_; lean_object* v_res_3070_; 
v_collapsed_boxed_3068_ = lean_unbox(v_collapsed_3058_);
v_clsEnabled_boxed_3069_ = lean_unbox(v_clsEnabled_3061_);
v_res_3070_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3057_, v_collapsed_boxed_3068_, v_tag_3059_, v_opts_3060_, v_clsEnabled_boxed_3069_, v_oldTraces_3062_, v_msg_3063_, v_resStartStop_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_opts_3060_);
return v_res_3070_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3073_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3074_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
lean_ctor_set(v___x_3076_, 2, v___x_3075_);
lean_ctor_set(v___x_3076_, 3, v___x_3075_);
lean_ctor_set(v___x_3076_, 4, v___x_3074_);
lean_ctor_set(v___x_3076_, 5, v___x_3074_);
lean_ctor_set(v___x_3076_, 6, v___x_3074_);
lean_ctor_set(v___x_3076_, 7, v___x_3074_);
lean_ctor_set(v___x_3076_, 8, v___x_3074_);
lean_ctor_set(v___x_3076_, 9, v___x_3074_);
lean_ctor_set(v___x_3076_, 10, v___x_3074_);
lean_ctor_set(v___x_3076_, 11, v___x_3073_);
return v___x_3076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3078_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
lean_ctor_set(v___x_3078_, 2, v___x_3077_);
lean_ctor_set(v___x_3078_, 3, v___x_3077_);
lean_ctor_set(v___x_3078_, 4, v___x_3077_);
lean_ctor_set(v___x_3078_, 5, v___x_3077_);
lean_ctor_set(v___x_3078_, 6, v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
lean_ctor_set(v___x_3080_, 2, v___x_3079_);
lean_ctor_set(v___x_3080_, 3, v___x_3079_);
lean_ctor_set(v___x_3080_, 4, v___x_3079_);
return v___x_3080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3086_ = l_Lean_Name_append(v___x_3085_, v___x_3084_);
return v___x_3086_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3087_; double v___x_3088_; 
v___x_3087_ = lean_unsigned_to_nat(1000000000u);
v___x_3088_ = lean_float_of_nat(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3089_, lean_object* v___f_3090_, lean_object* v_name_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_toCold_3095_; lean_object* v_options_3096_; uint8_t v_hasTrace_3097_; 
v_toCold_3095_ = lean_ctor_get(v___y_3092_, 0);
v_options_3096_ = lean_ctor_get(v_toCold_3095_, 2);
v_hasTrace_3097_ = lean_ctor_get_uint8(v_options_3096_, sizeof(void*)*1);
if (v_hasTrace_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v_env_3099_; lean_object* v___x_3100_; 
lean_dec_ref(v___f_3090_);
v___x_3098_ = lean_st_ref_get(v___y_3093_);
v_env_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc_ref(v_env_3099_);
lean_dec(v___x_3098_);
lean_inc(v_name_3091_);
v___x_3100_ = l_Lean_Meta_declFromEqLikeName(v_env_3099_, v_name_3091_);
if (lean_obj_tag(v___x_3100_) == 1)
{
lean_object* v_val_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3202_; 
v_val_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3202_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_val_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3202_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v_fst_3105_; lean_object* v_snd_3106_; lean_object* v___x_3107_; lean_object* v_env_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v_fst_3105_ = lean_ctor_get(v_val_3101_, 0);
lean_inc_n(v_fst_3105_, 2);
v_snd_3106_ = lean_ctor_get(v_val_3101_, 1);
lean_inc_n(v_snd_3106_, 2);
lean_dec(v_val_3101_);
v___x_3107_ = lean_st_ref_get(v___y_3093_);
v_env_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc_ref(v_env_3108_);
lean_dec(v___x_3107_);
v___x_3109_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3108_, v_fst_3105_, v_snd_3106_);
v___x_3110_ = lean_name_eq(v_name_3091_, v___x_3109_);
lean_dec(v___x_3109_);
lean_dec(v_name_3091_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
lean_dec(v_snd_3106_);
lean_dec(v_fst_3105_);
lean_dec(v___x_3089_);
v___x_3111_ = lean_box(v_hasTrace_3097_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set_tag(v___x_3103_, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3111_);
v___x_3113_ = v___x_3103_;
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
uint8_t v___x_3115_; 
lean_inc(v_snd_3106_);
v___x_3115_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3106_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3117_ = lean_string_dec_eq(v_snd_3106_, v___x_3116_);
lean_dec(v_snd_3106_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
lean_dec(v_fst_3105_);
lean_dec(v___x_3089_);
v___x_3118_ = lean_box(v_hasTrace_3097_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set_tag(v___x_3103_, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3118_);
v___x_3120_ = v___x_3103_;
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
else
{
uint8_t v___x_3122_; uint8_t v___x_3123_; uint8_t v___x_3124_; lean_object* v___x_3125_; uint64_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_del_object(v___x_3103_);
v___x_3122_ = 1;
v___x_3123_ = 0;
v___x_3124_ = 2;
v___x_3125_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3125_, 0, v___x_3115_);
lean_ctor_set_uint8(v___x_3125_, 1, v___x_3115_);
lean_ctor_set_uint8(v___x_3125_, 2, v___x_3115_);
lean_ctor_set_uint8(v___x_3125_, 3, v___x_3115_);
lean_ctor_set_uint8(v___x_3125_, 4, v___x_3115_);
lean_ctor_set_uint8(v___x_3125_, 5, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 6, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 7, v___x_3115_);
lean_ctor_set_uint8(v___x_3125_, 8, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 9, v___x_3122_);
lean_ctor_set_uint8(v___x_3125_, 10, v___x_3123_);
lean_ctor_set_uint8(v___x_3125_, 11, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 12, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 13, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 14, v___x_3124_);
lean_ctor_set_uint8(v___x_3125_, 15, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 16, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 17, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 18, v___x_3117_);
lean_ctor_set_uint8(v___x_3125_, 19, v___x_3115_);
v___x_3126_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3127_, 0, v___x_3125_);
lean_ctor_set_uint64(v___x_3127_, sizeof(void*)*1, v___x_3126_);
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3130_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3132_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3133_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3133_, 0, v___x_3127_);
lean_ctor_set(v___x_3133_, 1, v___x_3089_);
lean_ctor_set(v___x_3133_, 2, v___x_3130_);
lean_ctor_set(v___x_3133_, 3, v___x_3131_);
lean_ctor_set(v___x_3133_, 4, v___x_3132_);
lean_ctor_set(v___x_3133_, 5, v___x_3128_);
lean_ctor_set(v___x_3133_, 6, v___x_3132_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7, v___x_3115_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7 + 1, v___x_3115_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7 + 2, v___x_3115_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7 + 3, v___x_3110_);
v___x_3134_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3135_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3136_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3134_);
lean_ctor_set(v___x_3137_, 1, v___x_3135_);
lean_ctor_set(v___x_3137_, 2, v___x_3089_);
lean_ctor_set(v___x_3137_, 3, v___x_3129_);
lean_ctor_set(v___x_3137_, 4, v___x_3136_);
v___x_3138_ = lean_st_mk_ref(v___x_3137_);
v___x_3139_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3105_, v___x_3110_, v___x_3133_, v___x_3138_, v___y_3092_, v___y_3093_);
lean_dec_ref_known(v___x_3133_, 7);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3153_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3153_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3153_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_st_ref_get(v___x_3138_);
lean_dec(v___x_3138_);
lean_dec(v___x_3144_);
if (lean_obj_tag(v_a_3140_) == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_box(v___x_3115_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3145_);
v___x_3147_ = v___x_3142_;
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
lean_object* v___x_3149_; lean_object* v___x_3151_; 
lean_dec_ref_known(v_a_3140_, 1);
v___x_3149_ = lean_box(v___x_3117_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3149_);
v___x_3151_ = v___x_3142_;
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
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v___x_3138_);
v_a_3154_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3139_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3139_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
else
{
uint8_t v___x_3162_; uint8_t v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; uint64_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v_snd_3106_);
lean_del_object(v___x_3103_);
v___x_3162_ = 1;
v___x_3163_ = 0;
v___x_3164_ = 2;
v___x_3165_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3165_, 0, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3165_, 1, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3165_, 2, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3165_, 3, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3165_, 4, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3165_, 5, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 6, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 7, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3165_, 8, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 9, v___x_3162_);
lean_ctor_set_uint8(v___x_3165_, 10, v___x_3163_);
lean_ctor_set_uint8(v___x_3165_, 11, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 12, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 13, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 14, v___x_3164_);
lean_ctor_set_uint8(v___x_3165_, 15, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 16, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 17, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 18, v___x_3115_);
lean_ctor_set_uint8(v___x_3165_, 19, v_hasTrace_3097_);
v___x_3166_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3165_);
v___x_3167_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set_uint64(v___x_3167_, sizeof(void*)*1, v___x_3166_);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3170_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3171_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3172_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3173_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3173_, 0, v___x_3167_);
lean_ctor_set(v___x_3173_, 1, v___x_3089_);
lean_ctor_set(v___x_3173_, 2, v___x_3170_);
lean_ctor_set(v___x_3173_, 3, v___x_3171_);
lean_ctor_set(v___x_3173_, 4, v___x_3172_);
lean_ctor_set(v___x_3173_, 5, v___x_3168_);
lean_ctor_set(v___x_3173_, 6, v___x_3172_);
lean_ctor_set_uint8(v___x_3173_, sizeof(void*)*7, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3173_, sizeof(void*)*7 + 1, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3173_, sizeof(void*)*7 + 2, v_hasTrace_3097_);
lean_ctor_set_uint8(v___x_3173_, sizeof(void*)*7 + 3, v___x_3110_);
v___x_3174_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3175_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3176_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3174_);
lean_ctor_set(v___x_3177_, 1, v___x_3175_);
lean_ctor_set(v___x_3177_, 2, v___x_3089_);
lean_ctor_set(v___x_3177_, 3, v___x_3169_);
lean_ctor_set(v___x_3177_, 4, v___x_3176_);
v___x_3178_ = lean_st_mk_ref(v___x_3177_);
v___x_3179_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3105_, v___x_3173_, v___x_3178_, v___y_3092_, v___y_3093_);
lean_dec_ref_known(v___x_3173_, 7);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3193_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3193_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3193_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_st_ref_get(v___x_3178_);
lean_dec(v___x_3178_);
lean_dec(v___x_3184_);
if (lean_obj_tag(v_a_3180_) == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = lean_box(v_hasTrace_3097_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3185_);
v___x_3187_ = v___x_3182_;
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
else
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
lean_dec_ref_known(v_a_3180_, 1);
v___x_3189_ = lean_box(v___x_3115_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3189_);
v___x_3191_ = v___x_3182_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v___x_3178_);
v_a_3194_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3179_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3179_);
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
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec(v___x_3100_);
lean_dec(v_name_3091_);
lean_dec(v___x_3089_);
v___x_3203_ = lean_box(v_hasTrace_3097_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v_a_3214_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v_a_3229_; lean_object* v___y_3232_; lean_object* v___y_3233_; uint8_t v_a_3234_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v_a_3240_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v_a_3252_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v_a_3257_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; 
v_inheritedTraceOptions_3205_ = lean_ctor_get(v_toCold_3095_, 11);
lean_inc(v_name_3091_);
v___f_3206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3206_, 0, v_name_3091_);
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3208_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3205_, v_options_3096_, v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3391_ = l_Lean_trace_profiler;
v___x_3392_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3096_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; lean_object* v_env_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v___f_3206_);
lean_dec_ref(v___f_3090_);
v___x_3393_ = lean_st_ref_get(v___y_3093_);
v_env_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc_ref(v_env_3394_);
lean_dec(v___x_3393_);
lean_inc(v_name_3091_);
v___x_3395_ = l_Lean_Meta_declFromEqLikeName(v_env_3394_, v_name_3091_);
if (lean_obj_tag(v___x_3395_) == 1)
{
lean_object* v_val_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3497_; 
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3497_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_val_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3497_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_fst_3400_; lean_object* v_snd_3401_; lean_object* v___x_3402_; lean_object* v_env_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v_fst_3400_ = lean_ctor_get(v_val_3396_, 0);
lean_inc_n(v_fst_3400_, 2);
v_snd_3401_ = lean_ctor_get(v_val_3396_, 1);
lean_inc_n(v_snd_3401_, 2);
lean_dec(v_val_3396_);
v___x_3402_ = lean_st_ref_get(v___y_3093_);
v_env_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc_ref(v_env_3403_);
lean_dec(v___x_3402_);
v___x_3404_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3403_, v_fst_3400_, v_snd_3401_);
v___x_3405_ = lean_name_eq(v_name_3091_, v___x_3404_);
lean_dec(v___x_3404_);
lean_dec(v_name_3091_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
lean_dec(v_snd_3401_);
lean_dec(v_fst_3400_);
lean_dec(v___x_3089_);
v___x_3406_ = lean_box(v___x_3392_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3406_);
v___x_3408_ = v___x_3398_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
else
{
uint8_t v___x_3410_; 
lean_inc(v_snd_3401_);
v___x_3410_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3401_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3411_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3412_ = lean_string_dec_eq(v_snd_3401_, v___x_3411_);
lean_dec(v_snd_3401_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
lean_dec(v_fst_3400_);
lean_dec(v___x_3089_);
v___x_3413_ = lean_box(v___x_3392_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3413_);
v___x_3415_ = v___x_3398_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
else
{
uint8_t v___x_3417_; uint8_t v___x_3418_; uint8_t v___x_3419_; lean_object* v___x_3420_; uint64_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_del_object(v___x_3398_);
v___x_3417_ = 1;
v___x_3418_ = 0;
v___x_3419_ = 2;
v___x_3420_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3420_, 0, v___x_3410_);
lean_ctor_set_uint8(v___x_3420_, 1, v___x_3410_);
lean_ctor_set_uint8(v___x_3420_, 2, v___x_3410_);
lean_ctor_set_uint8(v___x_3420_, 3, v___x_3410_);
lean_ctor_set_uint8(v___x_3420_, 4, v___x_3410_);
lean_ctor_set_uint8(v___x_3420_, 5, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 6, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 7, v___x_3410_);
lean_ctor_set_uint8(v___x_3420_, 8, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 9, v___x_3417_);
lean_ctor_set_uint8(v___x_3420_, 10, v___x_3418_);
lean_ctor_set_uint8(v___x_3420_, 11, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 12, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 13, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 14, v___x_3419_);
lean_ctor_set_uint8(v___x_3420_, 15, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 16, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 17, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 18, v___x_3412_);
lean_ctor_set_uint8(v___x_3420_, 19, v___x_3410_);
v___x_3421_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3420_);
v___x_3422_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set_uint64(v___x_3422_, sizeof(void*)*1, v___x_3421_);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3425_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3427_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3428_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3428_, 0, v___x_3422_);
lean_ctor_set(v___x_3428_, 1, v___x_3089_);
lean_ctor_set(v___x_3428_, 2, v___x_3425_);
lean_ctor_set(v___x_3428_, 3, v___x_3426_);
lean_ctor_set(v___x_3428_, 4, v___x_3427_);
lean_ctor_set(v___x_3428_, 5, v___x_3423_);
lean_ctor_set(v___x_3428_, 6, v___x_3427_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7, v___x_3410_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 1, v___x_3410_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 2, v___x_3410_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 3, v_hasTrace_3097_);
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3431_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___x_3430_);
lean_ctor_set(v___x_3432_, 2, v___x_3089_);
lean_ctor_set(v___x_3432_, 3, v___x_3424_);
lean_ctor_set(v___x_3432_, 4, v___x_3431_);
v___x_3433_ = lean_st_mk_ref(v___x_3432_);
v___x_3434_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3400_, v_hasTrace_3097_, v___x_3428_, v___x_3433_, v___y_3092_, v___y_3093_);
lean_dec_ref_known(v___x_3428_, 7);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3448_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3448_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3448_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_st_ref_get(v___x_3433_);
lean_dec(v___x_3433_);
lean_dec(v___x_3439_);
if (lean_obj_tag(v_a_3435_) == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = lean_box(v___x_3410_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3440_);
v___x_3442_ = v___x_3437_;
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
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_dec_ref_known(v_a_3435_, 1);
v___x_3444_ = lean_box(v___x_3412_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3444_);
v___x_3446_ = v___x_3437_;
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
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v___x_3433_);
v_a_3449_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3434_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3434_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
else
{
uint8_t v___x_3457_; uint8_t v___x_3458_; uint8_t v___x_3459_; lean_object* v___x_3460_; uint64_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_dec(v_snd_3401_);
lean_del_object(v___x_3398_);
v___x_3457_ = 1;
v___x_3458_ = 0;
v___x_3459_ = 2;
v___x_3460_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3460_, 0, v___x_3392_);
lean_ctor_set_uint8(v___x_3460_, 1, v___x_3392_);
lean_ctor_set_uint8(v___x_3460_, 2, v___x_3392_);
lean_ctor_set_uint8(v___x_3460_, 3, v___x_3392_);
lean_ctor_set_uint8(v___x_3460_, 4, v___x_3392_);
lean_ctor_set_uint8(v___x_3460_, 5, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 6, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 7, v___x_3392_);
lean_ctor_set_uint8(v___x_3460_, 8, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 9, v___x_3457_);
lean_ctor_set_uint8(v___x_3460_, 10, v___x_3458_);
lean_ctor_set_uint8(v___x_3460_, 11, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 12, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 13, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 14, v___x_3459_);
lean_ctor_set_uint8(v___x_3460_, 15, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 16, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 17, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 18, v___x_3410_);
lean_ctor_set_uint8(v___x_3460_, 19, v___x_3392_);
v___x_3461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set_uint64(v___x_3462_, sizeof(void*)*1, v___x_3461_);
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3466_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3467_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3468_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3468_, 0, v___x_3462_);
lean_ctor_set(v___x_3468_, 1, v___x_3089_);
lean_ctor_set(v___x_3468_, 2, v___x_3465_);
lean_ctor_set(v___x_3468_, 3, v___x_3466_);
lean_ctor_set(v___x_3468_, 4, v___x_3467_);
lean_ctor_set(v___x_3468_, 5, v___x_3463_);
lean_ctor_set(v___x_3468_, 6, v___x_3467_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7, v___x_3392_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7 + 1, v___x_3392_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7 + 2, v___x_3392_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*7 + 3, v_hasTrace_3097_);
v___x_3469_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3470_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3471_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3469_);
lean_ctor_set(v___x_3472_, 1, v___x_3470_);
lean_ctor_set(v___x_3472_, 2, v___x_3089_);
lean_ctor_set(v___x_3472_, 3, v___x_3464_);
lean_ctor_set(v___x_3472_, 4, v___x_3471_);
v___x_3473_ = lean_st_mk_ref(v___x_3472_);
v___x_3474_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3400_, v___x_3468_, v___x_3473_, v___y_3092_, v___y_3093_);
lean_dec_ref_known(v___x_3468_, 7);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3488_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3488_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3488_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_st_ref_get(v___x_3473_);
lean_dec(v___x_3473_);
lean_dec(v___x_3479_);
if (lean_obj_tag(v_a_3475_) == 0)
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3480_ = lean_box(v___x_3392_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3480_);
v___x_3482_ = v___x_3477_;
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
else
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
lean_dec_ref_known(v_a_3475_, 1);
v___x_3484_ = lean_box(v___x_3410_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3484_);
v___x_3486_ = v___x_3477_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v___x_3473_);
v_a_3489_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3474_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3474_);
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
}
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v___x_3395_);
lean_dec(v_name_3091_);
lean_dec(v___x_3089_);
v___x_3498_ = lean_box(v___x_3392_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
}
else
{
goto v___jp_3267_;
}
}
else
{
goto v___jp_3267_;
}
v___jp_3211_:
{
lean_object* v___x_3215_; double v___x_3216_; double v___x_3217_; double v___x_3218_; double v___x_3219_; double v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3215_ = lean_io_mono_nanos_now();
v___x_3216_ = lean_float_of_nat(v___y_3213_);
v___x_3217_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
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
v___x_3225_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3207_, v_hasTrace_3097_, v___x_3208_, v_options_3096_, v___x_3210_, v___y_3212_, v___f_3206_, v___x_3224_, v___y_3092_, v___y_3093_);
return v___x_3225_;
}
v___jp_3226_:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v_a_3229_);
v___y_3212_ = v___y_3227_;
v___y_3213_ = v___y_3228_;
v_a_3214_ = v___x_3230_;
goto v___jp_3211_;
}
v___jp_3231_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_box(v_a_3234_);
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
v___y_3212_ = v___y_3232_;
v___y_3213_ = v___y_3233_;
v_a_3214_ = v___x_3236_;
goto v___jp_3211_;
}
v___jp_3237_:
{
lean_object* v___x_3241_; double v___x_3242_; double v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3241_ = lean_io_get_num_heartbeats();
v___x_3242_ = lean_float_of_nat(v___y_3239_);
v___x_3243_ = lean_float_of_nat(v___x_3241_);
v___x_3244_ = lean_box_float(v___x_3242_);
v___x_3245_ = lean_box_float(v___x_3243_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_a_3240_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3207_, v_hasTrace_3097_, v___x_3208_, v_options_3096_, v___x_3210_, v___y_3238_, v___f_3206_, v___x_3247_, v___y_3092_, v___y_3093_);
return v___x_3248_;
}
v___jp_3249_:
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v_a_3252_);
v___y_3238_ = v___y_3250_;
v___y_3239_ = v___y_3251_;
v_a_3240_ = v___x_3253_;
goto v___jp_3237_;
}
v___jp_3254_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_box(v_a_3257_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
v___y_3238_ = v___y_3255_;
v___y_3239_ = v___y_3256_;
v_a_3240_ = v___x_3259_;
goto v___jp_3237_;
}
v___jp_3260_:
{
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_object* v_a_3264_; uint8_t v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___y_3263_, 1);
v___x_3265_ = lean_unbox(v_a_3264_);
lean_dec(v_a_3264_);
v___y_3255_ = v___y_3261_;
v___y_3256_ = v___y_3262_;
v_a_3257_ = v___x_3265_;
goto v___jp_3254_;
}
else
{
lean_object* v_a_3266_; 
v_a_3266_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___y_3263_, 1);
v___y_3250_ = v___y_3261_;
v___y_3251_ = v___y_3262_;
v_a_3252_ = v_a_3266_;
goto v___jp_3249_;
}
}
v___jp_3267_:
{
lean_object* v___x_3268_; lean_object* v_a_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3268_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3093_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3271_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3096_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v_env_3274_; lean_object* v___x_3275_; 
lean_dec_ref(v___f_3090_);
v___x_3272_ = lean_io_mono_nanos_now();
v___x_3273_ = lean_st_ref_get(v___y_3093_);
v_env_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc_ref(v_env_3274_);
lean_dec(v___x_3273_);
lean_inc(v_name_3091_);
v___x_3275_ = l_Lean_Meta_declFromEqLikeName(v_env_3274_, v_name_3091_);
if (lean_obj_tag(v___x_3275_) == 1)
{
lean_object* v_val_3276_; lean_object* v_fst_3277_; lean_object* v_snd_3278_; lean_object* v___x_3279_; lean_object* v_env_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v_val_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_val_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v_fst_3277_ = lean_ctor_get(v_val_3276_, 0);
lean_inc_n(v_fst_3277_, 2);
v_snd_3278_ = lean_ctor_get(v_val_3276_, 1);
lean_inc_n(v_snd_3278_, 2);
lean_dec(v_val_3276_);
v___x_3279_ = lean_st_ref_get(v___y_3093_);
v_env_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc_ref(v_env_3280_);
lean_dec(v___x_3279_);
v___x_3281_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3280_, v_fst_3277_, v_snd_3278_);
v___x_3282_ = lean_name_eq(v_name_3091_, v___x_3281_);
lean_dec(v___x_3281_);
lean_dec(v_name_3091_);
if (v___x_3282_ == 0)
{
lean_dec(v_snd_3278_);
lean_dec(v_fst_3277_);
lean_dec(v___x_3089_);
v___y_3232_ = v_a_3269_;
v___y_3233_ = v___x_3272_;
v_a_3234_ = v___x_3271_;
goto v___jp_3231_;
}
else
{
uint8_t v___x_3283_; 
lean_inc(v_snd_3278_);
v___x_3283_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3278_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3285_ = lean_string_dec_eq(v_snd_3278_, v___x_3284_);
lean_dec(v_snd_3278_);
if (v___x_3285_ == 0)
{
lean_dec(v_fst_3277_);
lean_dec(v___x_3089_);
v___y_3232_ = v_a_3269_;
v___y_3233_ = v___x_3272_;
v_a_3234_ = v___x_3271_;
goto v___jp_3231_;
}
else
{
uint8_t v___x_3286_; uint8_t v___x_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; uint64_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3286_ = 1;
v___x_3287_ = 0;
v___x_3288_ = 2;
v___x_3289_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3289_, 0, v___x_3283_);
lean_ctor_set_uint8(v___x_3289_, 1, v___x_3283_);
lean_ctor_set_uint8(v___x_3289_, 2, v___x_3283_);
lean_ctor_set_uint8(v___x_3289_, 3, v___x_3283_);
lean_ctor_set_uint8(v___x_3289_, 4, v___x_3283_);
lean_ctor_set_uint8(v___x_3289_, 5, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 6, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 7, v___x_3283_);
lean_ctor_set_uint8(v___x_3289_, 8, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 9, v___x_3286_);
lean_ctor_set_uint8(v___x_3289_, 10, v___x_3287_);
lean_ctor_set_uint8(v___x_3289_, 11, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 12, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 13, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 14, v___x_3288_);
lean_ctor_set_uint8(v___x_3289_, 15, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 16, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 17, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 18, v___x_3285_);
lean_ctor_set_uint8(v___x_3289_, 19, v___x_3283_);
v___x_3290_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3289_);
v___x_3291_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set_uint64(v___x_3291_, sizeof(void*)*1, v___x_3290_);
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3294_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3295_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3296_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3297_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3297_, 0, v___x_3291_);
lean_ctor_set(v___x_3297_, 1, v___x_3089_);
lean_ctor_set(v___x_3297_, 2, v___x_3294_);
lean_ctor_set(v___x_3297_, 3, v___x_3295_);
lean_ctor_set(v___x_3297_, 4, v___x_3296_);
lean_ctor_set(v___x_3297_, 5, v___x_3292_);
lean_ctor_set(v___x_3297_, 6, v___x_3296_);
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*7, v___x_3283_);
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*7 + 1, v___x_3283_);
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*7 + 2, v___x_3283_);
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*7 + 3, v_hasTrace_3097_);
v___x_3298_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3299_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3300_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3298_);
lean_ctor_set(v___x_3301_, 1, v___x_3299_);
lean_ctor_set(v___x_3301_, 2, v___x_3089_);
lean_ctor_set(v___x_3301_, 3, v___x_3293_);
lean_ctor_set(v___x_3301_, 4, v___x_3300_);
v___x_3302_ = lean_st_mk_ref(v___x_3301_);
v___x_3303_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3277_, v_hasTrace_3097_, v___x_3297_, v___x_3302_, v___y_3092_, v___y_3093_);
lean_dec_ref_known(v___x_3297_, 7);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3303_, 1);
v___x_3305_ = lean_st_ref_get(v___x_3302_);
lean_dec(v___x_3302_);
lean_dec(v___x_3305_);
if (lean_obj_tag(v_a_3304_) == 0)
{
v___y_3232_ = v_a_3269_;
v___y_3233_ = v___x_3272_;
v_a_3234_ = v___x_3283_;
goto v___jp_3231_;
}
else
{
lean_dec_ref_known(v_a_3304_, 1);
v___y_3232_ = v_a_3269_;
v___y_3233_ = v___x_3272_;
v_a_3234_ = v___x_3285_;
goto v___jp_3231_;
}
}
else
{
lean_object* v_a_3306_; 
lean_dec(v___x_3302_);
v_a_3306_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3303_, 1);
v___y_3227_ = v_a_3269_;
v___y_3228_ = v___x_3272_;
v_a_3229_ = v_a_3306_;
goto v___jp_3226_;
}
}
}
else
{
uint8_t v___x_3307_; uint8_t v___x_3308_; uint8_t v___x_3309_; lean_object* v___x_3310_; uint64_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec(v_snd_3278_);
v___x_3307_ = 1;
v___x_3308_ = 0;
v___x_3309_ = 2;
v___x_3310_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3310_, 0, v___x_3271_);
lean_ctor_set_uint8(v___x_3310_, 1, v___x_3271_);
lean_ctor_set_uint8(v___x_3310_, 2, v___x_3271_);
lean_ctor_set_uint8(v___x_3310_, 3, v___x_3271_);
lean_ctor_set_uint8(v___x_3310_, 4, v___x_3271_);
lean_ctor_set_uint8(v___x_3310_, 5, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 6, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 7, v___x_3271_);
lean_ctor_set_uint8(v___x_3310_, 8, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 9, v___x_3307_);
lean_ctor_set_uint8(v___x_3310_, 10, v___x_3308_);
lean_ctor_set_uint8(v___x_3310_, 11, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 12, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 13, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 14, v___x_3309_);
lean_ctor_set_uint8(v___x_3310_, 15, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 16, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 17, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 18, v___x_3283_);
lean_ctor_set_uint8(v___x_3310_, 19, v___x_3271_);
v___x_3311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set_uint64(v___x_3312_, sizeof(void*)*1, v___x_3311_);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3317_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3318_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3318_, 0, v___x_3312_);
lean_ctor_set(v___x_3318_, 1, v___x_3089_);
lean_ctor_set(v___x_3318_, 2, v___x_3315_);
lean_ctor_set(v___x_3318_, 3, v___x_3316_);
lean_ctor_set(v___x_3318_, 4, v___x_3317_);
lean_ctor_set(v___x_3318_, 5, v___x_3313_);
lean_ctor_set(v___x_3318_, 6, v___x_3317_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7, v___x_3271_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7 + 1, v___x_3271_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7 + 2, v___x_3271_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*7 + 3, v_hasTrace_3097_);
v___x_3319_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3320_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3319_);
lean_ctor_set(v___x_3322_, 1, v___x_3320_);
lean_ctor_set(v___x_3322_, 2, v___x_3089_);
lean_ctor_set(v___x_3322_, 3, v___x_3314_);
lean_ctor_set(v___x_3322_, 4, v___x_3321_);
v___x_3323_ = lean_st_mk_ref(v___x_3322_);
v___x_3324_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3277_, v___x_3318_, v___x_3323_, v___y_3092_, v___y_3093_);
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
if (lean_obj_tag(v_a_3325_) == 0)
{
v___y_3232_ = v_a_3269_;
v___y_3233_ = v___x_3272_;
v_a_3234_ = v___x_3271_;
goto v___jp_3231_;
}
else
{
lean_dec_ref_known(v_a_3325_, 1);
v___y_3232_ = v_a_3269_;
v___y_3233_ = v___x_3272_;
v_a_3234_ = v___x_3283_;
goto v___jp_3231_;
}
}
else
{
lean_object* v_a_3327_; 
lean_dec(v___x_3323_);
v_a_3327_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3324_, 1);
v___y_3227_ = v_a_3269_;
v___y_3228_ = v___x_3272_;
v_a_3229_ = v_a_3327_;
goto v___jp_3226_;
}
}
}
}
else
{
lean_dec(v___x_3275_);
lean_dec(v_name_3091_);
lean_dec(v___x_3089_);
v___y_3232_ = v_a_3269_;
v___y_3233_ = v___x_3272_;
v_a_3234_ = v___x_3271_;
goto v___jp_3231_;
}
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v_env_3330_; lean_object* v___x_3331_; 
v___x_3328_ = lean_io_get_num_heartbeats();
v___x_3329_ = lean_st_ref_get(v___y_3093_);
v_env_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc_ref(v_env_3330_);
lean_dec(v___x_3329_);
lean_inc(v_name_3091_);
v___x_3331_ = l_Lean_Meta_declFromEqLikeName(v_env_3330_, v_name_3091_);
if (lean_obj_tag(v___x_3331_) == 1)
{
lean_object* v_val_3332_; lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___x_3335_; lean_object* v_env_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_val_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v___x_3331_, 1);
v_fst_3333_ = lean_ctor_get(v_val_3332_, 0);
lean_inc_n(v_fst_3333_, 2);
v_snd_3334_ = lean_ctor_get(v_val_3332_, 1);
lean_inc_n(v_snd_3334_, 2);
lean_dec(v_val_3332_);
v___x_3335_ = lean_st_ref_get(v___y_3093_);
v_env_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc_ref(v_env_3336_);
lean_dec(v___x_3335_);
v___x_3337_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3336_, v_fst_3333_, v_snd_3334_);
v___x_3338_ = lean_name_eq(v_name_3091_, v___x_3337_);
lean_dec(v___x_3337_);
lean_dec(v_name_3091_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_dec(v_snd_3334_);
lean_dec(v_fst_3333_);
lean_dec(v___x_3089_);
v___x_3339_ = lean_box(0);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
v___x_3340_ = lean_apply_4(v___f_3090_, v___x_3339_, v___y_3092_, v___y_3093_, lean_box(0));
v___y_3261_ = v_a_3269_;
v___y_3262_ = v___x_3328_;
v___y_3263_ = v___x_3340_;
goto v___jp_3260_;
}
else
{
uint8_t v___x_3341_; 
lean_inc(v_snd_3334_);
v___x_3341_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3334_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; uint8_t v___x_3343_; 
v___x_3342_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3343_ = lean_string_dec_eq(v_snd_3334_, v___x_3342_);
lean_dec(v_snd_3334_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec(v_fst_3333_);
lean_dec(v___x_3089_);
v___x_3344_ = lean_box(0);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
v___x_3345_ = lean_apply_4(v___f_3090_, v___x_3344_, v___y_3092_, v___y_3093_, lean_box(0));
v___y_3261_ = v_a_3269_;
v___y_3262_ = v___x_3328_;
v___y_3263_ = v___x_3345_;
goto v___jp_3260_;
}
else
{
uint8_t v___x_3346_; uint8_t v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; uint64_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec_ref(v___f_3090_);
v___x_3346_ = 1;
v___x_3347_ = 0;
v___x_3348_ = 2;
v___x_3349_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3349_, 0, v___x_3341_);
lean_ctor_set_uint8(v___x_3349_, 1, v___x_3341_);
lean_ctor_set_uint8(v___x_3349_, 2, v___x_3341_);
lean_ctor_set_uint8(v___x_3349_, 3, v___x_3341_);
lean_ctor_set_uint8(v___x_3349_, 4, v___x_3341_);
lean_ctor_set_uint8(v___x_3349_, 5, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 6, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 7, v___x_3341_);
lean_ctor_set_uint8(v___x_3349_, 8, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 9, v___x_3346_);
lean_ctor_set_uint8(v___x_3349_, 10, v___x_3347_);
lean_ctor_set_uint8(v___x_3349_, 11, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 12, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 13, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 14, v___x_3348_);
lean_ctor_set_uint8(v___x_3349_, 15, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 16, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 17, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 18, v___x_3343_);
lean_ctor_set_uint8(v___x_3349_, 19, v___x_3341_);
v___x_3350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set_uint64(v___x_3351_, sizeof(void*)*1, v___x_3350_);
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3354_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3356_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3357_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3357_, 0, v___x_3351_);
lean_ctor_set(v___x_3357_, 1, v___x_3089_);
lean_ctor_set(v___x_3357_, 2, v___x_3354_);
lean_ctor_set(v___x_3357_, 3, v___x_3355_);
lean_ctor_set(v___x_3357_, 4, v___x_3356_);
lean_ctor_set(v___x_3357_, 5, v___x_3352_);
lean_ctor_set(v___x_3357_, 6, v___x_3356_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7, v___x_3341_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7 + 1, v___x_3341_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7 + 2, v___x_3341_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7 + 3, v___x_3271_);
v___x_3358_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3359_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3360_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3358_);
lean_ctor_set(v___x_3361_, 1, v___x_3359_);
lean_ctor_set(v___x_3361_, 2, v___x_3089_);
lean_ctor_set(v___x_3361_, 3, v___x_3353_);
lean_ctor_set(v___x_3361_, 4, v___x_3360_);
v___x_3362_ = lean_st_mk_ref(v___x_3361_);
v___x_3363_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3333_, v___x_3271_, v___x_3357_, v___x_3362_, v___y_3092_, v___y_3093_);
lean_dec_ref_known(v___x_3357_, 7);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v___x_3365_ = lean_st_ref_get(v___x_3362_);
lean_dec(v___x_3362_);
lean_dec(v___x_3365_);
if (lean_obj_tag(v_a_3364_) == 0)
{
v___y_3255_ = v_a_3269_;
v___y_3256_ = v___x_3328_;
v_a_3257_ = v___x_3341_;
goto v___jp_3254_;
}
else
{
lean_dec_ref_known(v_a_3364_, 1);
v___y_3255_ = v_a_3269_;
v___y_3256_ = v___x_3328_;
v_a_3257_ = v___x_3343_;
goto v___jp_3254_;
}
}
else
{
lean_object* v_a_3366_; 
lean_dec(v___x_3362_);
v_a_3366_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3363_, 1);
v___y_3250_ = v_a_3269_;
v___y_3251_ = v___x_3328_;
v_a_3252_ = v_a_3366_;
goto v___jp_3249_;
}
}
}
else
{
uint8_t v___x_3367_; uint8_t v___x_3368_; uint8_t v___x_3369_; uint8_t v___x_3370_; lean_object* v___x_3371_; uint64_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec(v_snd_3334_);
lean_dec_ref(v___f_3090_);
v___x_3367_ = 0;
v___x_3368_ = 1;
v___x_3369_ = 0;
v___x_3370_ = 2;
v___x_3371_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3371_, 0, v___x_3367_);
lean_ctor_set_uint8(v___x_3371_, 1, v___x_3367_);
lean_ctor_set_uint8(v___x_3371_, 2, v___x_3367_);
lean_ctor_set_uint8(v___x_3371_, 3, v___x_3367_);
lean_ctor_set_uint8(v___x_3371_, 4, v___x_3367_);
lean_ctor_set_uint8(v___x_3371_, 5, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 6, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 7, v___x_3367_);
lean_ctor_set_uint8(v___x_3371_, 8, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 9, v___x_3368_);
lean_ctor_set_uint8(v___x_3371_, 10, v___x_3369_);
lean_ctor_set_uint8(v___x_3371_, 11, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 12, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 13, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 14, v___x_3370_);
lean_ctor_set_uint8(v___x_3371_, 15, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 16, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 17, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 18, v___x_3341_);
lean_ctor_set_uint8(v___x_3371_, 19, v___x_3367_);
v___x_3372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3371_);
v___x_3373_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set_uint64(v___x_3373_, sizeof(void*)*1, v___x_3372_);
v___x_3374_ = lean_unsigned_to_nat(0u);
v___x_3375_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3376_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3378_ = lean_box(0);
lean_inc(v___x_3089_);
v___x_3379_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3379_, 0, v___x_3373_);
lean_ctor_set(v___x_3379_, 1, v___x_3089_);
lean_ctor_set(v___x_3379_, 2, v___x_3376_);
lean_ctor_set(v___x_3379_, 3, v___x_3377_);
lean_ctor_set(v___x_3379_, 4, v___x_3378_);
lean_ctor_set(v___x_3379_, 5, v___x_3374_);
lean_ctor_set(v___x_3379_, 6, v___x_3378_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*7, v___x_3367_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*7 + 1, v___x_3367_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*7 + 2, v___x_3367_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*7 + 3, v___x_3271_);
v___x_3380_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3381_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3382_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3380_);
lean_ctor_set(v___x_3383_, 1, v___x_3381_);
lean_ctor_set(v___x_3383_, 2, v___x_3089_);
lean_ctor_set(v___x_3383_, 3, v___x_3375_);
lean_ctor_set(v___x_3383_, 4, v___x_3382_);
v___x_3384_ = lean_st_mk_ref(v___x_3383_);
v___x_3385_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3333_, v___x_3379_, v___x_3384_, v___y_3092_, v___y_3093_);
lean_dec_ref_known(v___x_3379_, 7);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v___x_3387_ = lean_st_ref_get(v___x_3384_);
lean_dec(v___x_3384_);
lean_dec(v___x_3387_);
if (lean_obj_tag(v_a_3386_) == 0)
{
v___y_3255_ = v_a_3269_;
v___y_3256_ = v___x_3328_;
v_a_3257_ = v___x_3367_;
goto v___jp_3254_;
}
else
{
lean_dec_ref_known(v_a_3386_, 1);
v___y_3255_ = v_a_3269_;
v___y_3256_ = v___x_3328_;
v_a_3257_ = v___x_3341_;
goto v___jp_3254_;
}
}
else
{
lean_object* v_a_3388_; 
lean_dec(v___x_3384_);
v_a_3388_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3385_, 1);
v___y_3250_ = v_a_3269_;
v___y_3251_ = v___x_3328_;
v_a_3252_ = v_a_3388_;
goto v___jp_3249_;
}
}
}
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_dec(v___x_3331_);
lean_dec(v_name_3091_);
lean_dec(v___x_3089_);
v___x_3389_ = lean_box(0);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
v___x_3390_ = lean_apply_4(v___f_3090_, v___x_3389_, v___y_3092_, v___y_3093_, lean_box(0));
v___y_3261_ = v_a_3269_;
v___y_3262_ = v___x_3328_;
v___y_3263_ = v___x_3390_;
goto v___jp_3260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3500_, lean_object* v___f_3501_, lean_object* v_name_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3500_, v___f_3501_, v_name_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = lean_unsigned_to_nat(3137104340u);
v___x_3552_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3553_ = l_Lean_Name_num___override(v___x_3552_, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3556_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3557_ = l_Lean_Name_str___override(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3560_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3561_ = l_Lean_Name_str___override(v___x_3560_, v___x_3559_);
return v___x_3561_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_unsigned_to_nat(2u);
v___x_3563_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3564_ = l_Lean_Name_num___override(v___x_3563_, v___x_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3566_; lean_object* v___x_3567_; 
v___f_3566_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3567_ = l_Lean_registerReservedNameAction(v___f_3566_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v___x_3568_; uint8_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_dec_ref_known(v___x_3567_, 1);
v___x_3568_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3569_ = 0;
v___x_3570_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3571_ = l_Lean_registerTraceClass(v___x_3568_, v___x_3569_, v___x_3570_);
return v___x_3571_;
}
else
{
return v___x_3567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3574_, lean_object* v_x_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3575_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3580_, lean_object* v_x_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3580_, v_x_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
return v_res_3585_;
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
