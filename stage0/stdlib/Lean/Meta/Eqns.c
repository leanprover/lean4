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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__4 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__4_value;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__5 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__5_value;
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__5_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 70, 141, 178, 157, 107, 140, 91)}};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__6 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__6_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__7;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "saving equation-affecting options for "};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__8 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__8_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__9;
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
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = l_Lean_Meta_eqnAffectingOptions;
v___x_671_ = lean_array_get_size(v___x_670_);
return v___x_671_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_nat_dec_lt(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_675_; size_t v___x_676_; 
v___x_675_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_676_ = lean_usize_of_nat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_677_, lean_object* v_act_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___y_685_; uint16_t v___y_686_; lean_object* v_fileName_687_; lean_object* v_fileMap_688_; lean_object* v_currNamespace_689_; lean_object* v_openDecls_690_; lean_object* v_initHeartbeats_691_; lean_object* v_maxHeartbeats_692_; lean_object* v_quotContext_693_; lean_object* v_currMacroScope_694_; lean_object* v_cancelTk_x3f_695_; lean_object* v_inheritedTraceOptions_696_; lean_object* v_currRecDepth_697_; lean_object* v_ref_698_; uint8_t v_suppressElabErrors_699_; uint8_t v_checkDeprecated_700_; uint8_t v_isRecordingDeps_701_; lean_object* v___y_702_; lean_object* v___y_709_; uint16_t v___y_710_; uint8_t v___y_711_; lean_object* v___x_749_; lean_object* v_toCold_750_; lean_object* v_currRecDepth_751_; lean_object* v_ref_752_; uint8_t v_suppressElabErrors_753_; uint8_t v_checkDeprecated_754_; uint8_t v_isRecordingDeps_755_; lean_object* v_fileName_756_; lean_object* v_fileMap_757_; lean_object* v_options_758_; lean_object* v_currNamespace_759_; lean_object* v_openDecls_760_; lean_object* v_initHeartbeats_761_; lean_object* v_maxHeartbeats_762_; lean_object* v_quotContext_763_; lean_object* v_currMacroScope_764_; lean_object* v_cancelTk_x3f_765_; lean_object* v_inheritedTraceOptions_766_; lean_object* v___y_768_; 
v___x_749_ = lean_st_ref_get(v_a_682_);
v_toCold_750_ = lean_ctor_get(v_a_681_, 0);
v_currRecDepth_751_ = lean_ctor_get(v_a_681_, 1);
v_ref_752_ = lean_ctor_get(v_a_681_, 2);
v_suppressElabErrors_753_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3 + 2);
v_checkDeprecated_754_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3 + 3);
v_isRecordingDeps_755_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3 + 4);
v_fileName_756_ = lean_ctor_get(v_toCold_750_, 0);
v_fileMap_757_ = lean_ctor_get(v_toCold_750_, 1);
v_options_758_ = lean_ctor_get(v_toCold_750_, 2);
v_currNamespace_759_ = lean_ctor_get(v_toCold_750_, 4);
v_openDecls_760_ = lean_ctor_get(v_toCold_750_, 5);
v_initHeartbeats_761_ = lean_ctor_get(v_toCold_750_, 6);
v_maxHeartbeats_762_ = lean_ctor_get(v_toCold_750_, 7);
v_quotContext_763_ = lean_ctor_get(v_toCold_750_, 8);
v_currMacroScope_764_ = lean_ctor_get(v_toCold_750_, 9);
v_cancelTk_x3f_765_ = lean_ctor_get(v_toCold_750_, 10);
v_inheritedTraceOptions_766_ = lean_ctor_get(v_toCold_750_, 11);
if (v_isRecordingDeps_755_ == 0)
{
lean_object* v_env_779_; lean_object* v___x_780_; lean_object* v_toEnvExtension_781_; lean_object* v_asyncMode_782_; uint8_t v___x_783_; lean_object* v___x_784_; 
v_env_779_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_env_779_);
lean_dec(v___x_749_);
v___x_780_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_781_ = lean_ctor_get(v___x_780_, 0);
v_asyncMode_782_ = lean_ctor_get(v_toEnvExtension_781_, 2);
v___x_783_ = 0;
v___x_784_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_780_, v_env_779_, v_declName_677_, v_asyncMode_782_, v___x_783_);
if (lean_obj_tag(v___x_784_) == 1)
{
lean_object* v_val_785_; lean_object* v___y_787_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_val_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_791_ = l_Lean_Meta_eqnAffectingOptions;
v___x_792_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
if (v___x_792_ == 0)
{
lean_inc_ref(v_options_758_);
v___y_787_ = v_options_758_;
goto v___jp_786_;
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
lean_inc_ref(v_options_758_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_791_, v___x_793_, v___x_794_, v_options_758_);
v___y_787_ = v___x_795_;
goto v___jp_786_;
}
v___jp_786_:
{
size_t v_sz_788_; size_t v___x_789_; lean_object* v___x_790_; 
v_sz_788_ = lean_array_size(v_val_785_);
v___x_789_ = ((size_t)0ULL);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_785_, v_sz_788_, v___x_789_, v___y_787_);
lean_dec(v_val_785_);
v___y_768_ = v___x_790_;
goto v___jp_767_;
}
}
else
{
lean_object* v___x_796_; uint8_t v___x_797_; 
lean_dec(v___x_784_);
v___x_796_ = l_Lean_Meta_eqnAffectingOptions;
v___x_797_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
if (v___x_797_ == 0)
{
lean_inc_ref(v_options_758_);
v___y_768_ = v_options_758_;
goto v___jp_767_;
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
lean_inc_ref(v_options_758_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_796_, v___x_798_, v___x_799_, v_options_758_);
v___y_768_ = v___x_800_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v___x_801_; 
lean_dec(v___x_749_);
lean_dec(v_declName_677_);
lean_inc_ref(v_options_758_);
v___x_801_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_758_);
v___y_768_ = v___x_801_;
goto v___jp_767_;
}
v___jp_684_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_703_ = l_Lean_maxRecDepth;
v___x_704_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_685_, v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_705_, 0, v_fileName_687_);
lean_ctor_set(v___x_705_, 1, v_fileMap_688_);
lean_ctor_set(v___x_705_, 2, v___y_685_);
lean_ctor_set(v___x_705_, 3, v___x_704_);
lean_ctor_set(v___x_705_, 4, v_currNamespace_689_);
lean_ctor_set(v___x_705_, 5, v_openDecls_690_);
lean_ctor_set(v___x_705_, 6, v_initHeartbeats_691_);
lean_ctor_set(v___x_705_, 7, v_maxHeartbeats_692_);
lean_ctor_set(v___x_705_, 8, v_quotContext_693_);
lean_ctor_set(v___x_705_, 9, v_currMacroScope_694_);
lean_ctor_set(v___x_705_, 10, v_cancelTk_x3f_695_);
lean_ctor_set(v___x_705_, 11, v_inheritedTraceOptions_696_);
lean_inc(v_ref_698_);
lean_inc(v_currRecDepth_697_);
v___x_706_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_currRecDepth_697_);
lean_ctor_set(v___x_706_, 2, v_ref_698_);
lean_ctor_set_uint16(v___x_706_, sizeof(void*)*3, v___y_686_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3 + 2, v_suppressElabErrors_699_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3 + 3, v_checkDeprecated_700_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3 + 4, v_isRecordingDeps_701_);
lean_inc(v___y_702_);
lean_inc(v_a_680_);
lean_inc_ref(v_a_679_);
v___x_707_ = lean_apply_5(v_act_678_, v_a_679_, v_a_680_, v___x_706_, v___y_702_, lean_box(0));
return v___x_707_;
}
v___jp_708_:
{
lean_object* v___x_712_; lean_object* v_env_713_; lean_object* v_nextMacroScope_714_; lean_object* v_ngen_715_; lean_object* v_auxDeclNGen_716_; lean_object* v_traceState_717_; lean_object* v_recordedDeps_718_; lean_object* v_messages_719_; lean_object* v_infoState_720_; lean_object* v_snapshotTasks_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_747_; 
v___x_712_ = lean_st_ref_take(v_a_682_);
v_env_713_ = lean_ctor_get(v___x_712_, 0);
v_nextMacroScope_714_ = lean_ctor_get(v___x_712_, 1);
v_ngen_715_ = lean_ctor_get(v___x_712_, 2);
v_auxDeclNGen_716_ = lean_ctor_get(v___x_712_, 3);
v_traceState_717_ = lean_ctor_get(v___x_712_, 4);
v_recordedDeps_718_ = lean_ctor_get(v___x_712_, 6);
v_messages_719_ = lean_ctor_get(v___x_712_, 7);
v_infoState_720_ = lean_ctor_get(v___x_712_, 8);
v_snapshotTasks_721_ = lean_ctor_get(v___x_712_, 9);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_712_, 5);
lean_dec(v_unused_748_);
v___x_723_ = v___x_712_;
v_isShared_724_ = v_isSharedCheck_747_;
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
v_isShared_724_ = v_isSharedCheck_747_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = l_Lean_Kernel_enableDiag(v_env_713_, v___y_711_);
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
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_nextMacroScope_714_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_ngen_715_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_auxDeclNGen_716_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_traceState_717_);
lean_ctor_set(v_reuseFailAlloc_746_, 5, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_746_, 6, v_recordedDeps_718_);
lean_ctor_set(v_reuseFailAlloc_746_, 7, v_messages_719_);
lean_ctor_set(v_reuseFailAlloc_746_, 8, v_infoState_720_);
lean_ctor_set(v_reuseFailAlloc_746_, 9, v_snapshotTasks_721_);
v___x_728_ = v_reuseFailAlloc_746_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v_toCold_730_; lean_object* v_currRecDepth_731_; lean_object* v_ref_732_; uint8_t v_suppressElabErrors_733_; uint8_t v_checkDeprecated_734_; uint8_t v_isRecordingDeps_735_; lean_object* v_fileName_736_; lean_object* v_fileMap_737_; lean_object* v_currNamespace_738_; lean_object* v_openDecls_739_; lean_object* v_initHeartbeats_740_; lean_object* v_maxHeartbeats_741_; lean_object* v_quotContext_742_; lean_object* v_currMacroScope_743_; lean_object* v_cancelTk_x3f_744_; lean_object* v_inheritedTraceOptions_745_; 
v___x_729_ = lean_st_ref_put(v_a_682_, v___x_728_);
v_toCold_730_ = lean_ctor_get(v_a_681_, 0);
v_currRecDepth_731_ = lean_ctor_get(v_a_681_, 1);
v_ref_732_ = lean_ctor_get(v_a_681_, 2);
v_suppressElabErrors_733_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3 + 2);
v_checkDeprecated_734_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3 + 3);
v_isRecordingDeps_735_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3 + 4);
v_fileName_736_ = lean_ctor_get(v_toCold_730_, 0);
v_fileMap_737_ = lean_ctor_get(v_toCold_730_, 1);
v_currNamespace_738_ = lean_ctor_get(v_toCold_730_, 4);
v_openDecls_739_ = lean_ctor_get(v_toCold_730_, 5);
v_initHeartbeats_740_ = lean_ctor_get(v_toCold_730_, 6);
v_maxHeartbeats_741_ = lean_ctor_get(v_toCold_730_, 7);
v_quotContext_742_ = lean_ctor_get(v_toCold_730_, 8);
v_currMacroScope_743_ = lean_ctor_get(v_toCold_730_, 9);
v_cancelTk_x3f_744_ = lean_ctor_get(v_toCold_730_, 10);
v_inheritedTraceOptions_745_ = lean_ctor_get(v_toCold_730_, 11);
lean_inc_ref(v_inheritedTraceOptions_745_);
lean_inc(v_cancelTk_x3f_744_);
lean_inc(v_currMacroScope_743_);
lean_inc(v_quotContext_742_);
lean_inc(v_maxHeartbeats_741_);
lean_inc(v_initHeartbeats_740_);
lean_inc(v_openDecls_739_);
lean_inc(v_currNamespace_738_);
lean_inc_ref(v_fileMap_737_);
lean_inc_ref(v_fileName_736_);
v___y_685_ = v___y_709_;
v___y_686_ = v___y_710_;
v_fileName_687_ = v_fileName_736_;
v_fileMap_688_ = v_fileMap_737_;
v_currNamespace_689_ = v_currNamespace_738_;
v_openDecls_690_ = v_openDecls_739_;
v_initHeartbeats_691_ = v_initHeartbeats_740_;
v_maxHeartbeats_692_ = v_maxHeartbeats_741_;
v_quotContext_693_ = v_quotContext_742_;
v_currMacroScope_694_ = v_currMacroScope_743_;
v_cancelTk_x3f_695_ = v_cancelTk_x3f_744_;
v_inheritedTraceOptions_696_ = v_inheritedTraceOptions_745_;
v_currRecDepth_697_ = v_currRecDepth_731_;
v_ref_698_ = v_ref_732_;
v_suppressElabErrors_699_ = v_suppressElabErrors_733_;
v_checkDeprecated_700_ = v_checkDeprecated_734_;
v_isRecordingDeps_701_ = v_isRecordingDeps_735_;
v___y_702_ = v_a_682_;
goto v___jp_684_;
}
}
}
v___jp_767_:
{
uint16_t v___x_769_; lean_object* v___x_770_; lean_object* v_env_771_; uint8_t v___x_772_; uint16_t v___x_773_; uint16_t v___x_774_; uint16_t v___x_775_; uint8_t v___x_776_; 
v___x_769_ = l_Lean_OptionFlags_ofOptions(v___y_768_);
v___x_770_ = lean_st_ref_get(v_a_682_);
v_env_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_ref(v_env_771_);
lean_dec(v___x_770_);
v___x_772_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_771_);
lean_dec_ref(v_env_771_);
v___x_773_ = 512;
v___x_774_ = lean_uint16_land(v___x_769_, v___x_773_);
v___x_775_ = 0;
v___x_776_ = lean_uint16_dec_eq(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
if (v___x_772_ == 0)
{
uint8_t v___x_777_; 
v___x_777_ = 1;
v___y_709_ = v___y_768_;
v___y_710_ = v___x_769_;
v___y_711_ = v___x_777_;
goto v___jp_708_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_766_);
lean_inc(v_cancelTk_x3f_765_);
lean_inc(v_currMacroScope_764_);
lean_inc(v_quotContext_763_);
lean_inc(v_maxHeartbeats_762_);
lean_inc(v_initHeartbeats_761_);
lean_inc(v_openDecls_760_);
lean_inc(v_currNamespace_759_);
lean_inc_ref(v_fileMap_757_);
lean_inc_ref(v_fileName_756_);
v___y_685_ = v___y_768_;
v___y_686_ = v___x_769_;
v_fileName_687_ = v_fileName_756_;
v_fileMap_688_ = v_fileMap_757_;
v_currNamespace_689_ = v_currNamespace_759_;
v_openDecls_690_ = v_openDecls_760_;
v_initHeartbeats_691_ = v_initHeartbeats_761_;
v_maxHeartbeats_692_ = v_maxHeartbeats_762_;
v_quotContext_693_ = v_quotContext_763_;
v_currMacroScope_694_ = v_currMacroScope_764_;
v_cancelTk_x3f_695_ = v_cancelTk_x3f_765_;
v_inheritedTraceOptions_696_ = v_inheritedTraceOptions_766_;
v_currRecDepth_697_ = v_currRecDepth_751_;
v_ref_698_ = v_ref_752_;
v_suppressElabErrors_699_ = v_suppressElabErrors_753_;
v_checkDeprecated_700_ = v_checkDeprecated_754_;
v_isRecordingDeps_701_ = v_isRecordingDeps_755_;
v___y_702_ = v_a_682_;
goto v___jp_684_;
}
}
else
{
if (v___x_772_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_766_);
lean_inc(v_cancelTk_x3f_765_);
lean_inc(v_currMacroScope_764_);
lean_inc(v_quotContext_763_);
lean_inc(v_maxHeartbeats_762_);
lean_inc(v_initHeartbeats_761_);
lean_inc(v_openDecls_760_);
lean_inc(v_currNamespace_759_);
lean_inc_ref(v_fileMap_757_);
lean_inc_ref(v_fileName_756_);
v___y_685_ = v___y_768_;
v___y_686_ = v___x_769_;
v_fileName_687_ = v_fileName_756_;
v_fileMap_688_ = v_fileMap_757_;
v_currNamespace_689_ = v_currNamespace_759_;
v_openDecls_690_ = v_openDecls_760_;
v_initHeartbeats_691_ = v_initHeartbeats_761_;
v_maxHeartbeats_692_ = v_maxHeartbeats_762_;
v_quotContext_693_ = v_quotContext_763_;
v_currMacroScope_694_ = v_currMacroScope_764_;
v_cancelTk_x3f_695_ = v_cancelTk_x3f_765_;
v_inheritedTraceOptions_696_ = v_inheritedTraceOptions_766_;
v_currRecDepth_697_ = v_currRecDepth_751_;
v_ref_698_ = v_ref_752_;
v_suppressElabErrors_699_ = v_suppressElabErrors_753_;
v_checkDeprecated_700_ = v_checkDeprecated_754_;
v_isRecordingDeps_701_ = v_isRecordingDeps_755_;
v___y_702_ = v_a_682_;
goto v___jp_684_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = 0;
v___y_709_ = v___y_768_;
v___y_710_ = v___x_769_;
v___y_711_ = v___x_778_;
goto v___jp_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_802_, lean_object* v_act_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_802_, v_act_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_810_, lean_object* v_declName_811_, lean_object* v_act_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_811_, v_act_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_819_, lean_object* v_declName_820_, lean_object* v_act_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_819_, v_declName_820_, v_act_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_env_832_; lean_object* v_toConstantVal_833_; lean_object* v_value_834_; lean_object* v_all_835_; lean_object* v_type_842_; uint8_t v___x_843_; 
v___x_831_ = lean_st_ref_get(v___y_829_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref_n(v_env_832_, 2);
lean_dec(v___x_831_);
v_toConstantVal_833_ = lean_ctor_get(v_thm_828_, 0);
v_value_834_ = lean_ctor_get(v_thm_828_, 1);
v_all_835_ = lean_ctor_get(v_thm_828_, 2);
v_type_842_ = lean_ctor_get(v_toConstantVal_833_, 2);
v___x_843_ = l_Lean_Environment_hasUnsafe(v_env_832_, v_type_842_);
if (v___x_843_ == 0)
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Environment_hasUnsafe(v_env_832_, v_value_834_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_845_, 0, v_thm_828_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
else
{
lean_inc(v_all_835_);
lean_inc_ref(v_value_834_);
lean_inc_ref(v_toConstantVal_833_);
lean_dec_ref(v_thm_828_);
goto v___jp_836_;
}
}
else
{
lean_inc(v_all_835_);
lean_inc_ref(v_value_834_);
lean_inc_ref(v_toConstantVal_833_);
lean_dec_ref(v_env_832_);
lean_dec_ref(v_thm_828_);
goto v___jp_836_;
}
v___jp_836_:
{
lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_837_ = lean_box(0);
v___x_838_ = 0;
v___x_839_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_839_, 0, v_toConstantVal_833_);
lean_ctor_set(v___x_839_, 1, v_value_834_);
lean_ctor_set(v___x_839_, 2, v___x_837_);
lean_ctor_set(v___x_839_, 3, v_all_835_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*4, v___x_838_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_847_, v___y_848_);
lean_dec(v___y_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_851_, v___y_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_865_, lean_object* v_b_866_, lean_object* v_c_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
v___x_873_ = lean_apply_7(v_k_865_, v_b_866_, v_c_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, lean_box(0));
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_874_, lean_object* v_b_875_, lean_object* v_c_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_874_, v_b_875_, v_c_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_883_, lean_object* v_k_884_, uint8_t v_cleanupAnnotations_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___f_891_; uint8_t v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_891_, 0, v_k_884_);
v___x_892_ = 1;
v___x_893_ = 0;
v___x_894_ = lean_box(0);
v___x_895_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_883_, v___x_892_, v___x_893_, v___x_892_, v___x_893_, v___x_894_, v___f_891_, v_cleanupAnnotations_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
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
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_895_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_895_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_912_, lean_object* v_k_913_, lean_object* v_cleanupAnnotations_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_920_; lean_object* v_res_921_; 
v_cleanupAnnotations_boxed_920_ = lean_unbox(v_cleanupAnnotations_914_);
v_res_921_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_912_, v_k_913_, v_cleanupAnnotations_boxed_920_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_922_, lean_object* v_e_923_, lean_object* v_k_924_, uint8_t v_cleanupAnnotations_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_923_, v_k_924_, v_cleanupAnnotations_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_932_, lean_object* v_e_933_, lean_object* v_k_934_, lean_object* v_cleanupAnnotations_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_941_; lean_object* v_res_942_; 
v_cleanupAnnotations_boxed_941_ = lean_unbox(v_cleanupAnnotations_935_);
v_res_942_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_932_, v_e_933_, v_k_934_, v_cleanupAnnotations_boxed_941_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
if (lean_obj_tag(v_a_943_) == 0)
{
lean_object* v___x_945_; 
v___x_945_ = l_List_reverse___redArg(v_a_944_);
return v___x_945_;
}
else
{
lean_object* v_head_946_; lean_object* v_tail_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_956_; 
v_head_946_ = lean_ctor_get(v_a_943_, 0);
v_tail_947_ = lean_ctor_get(v_a_943_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_956_ == 0)
{
v___x_949_ = v_a_943_;
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_tail_947_);
lean_inc(v_head_946_);
lean_dec(v_a_943_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = l_Lean_mkLevelParam(v_head_946_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_a_944_);
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_a_944_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_a_943_ = v_tail_947_;
v_a_944_ = v___x_953_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_957_, lean_object* v_name_958_, lean_object* v_xs_959_, lean_object* v_body_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_name_966_; lean_object* v_levelParams_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1037_; 
v_name_966_ = lean_ctor_get(v_toConstantVal_957_, 0);
v_levelParams_967_ = lean_ctor_get(v_toConstantVal_957_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_toConstantVal_957_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_toConstantVal_957_, 2);
lean_dec(v_unused_1038_);
v___x_969_ = v_toConstantVal_957_;
v_isShared_970_ = v_isSharedCheck_1037_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_levelParams_967_);
lean_inc(v_name_966_);
lean_dec(v_toConstantVal_957_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1037_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_lhs_974_; lean_object* v___x_975_; 
v___x_971_ = lean_box(0);
lean_inc(v_levelParams_967_);
v___x_972_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_967_, v___x_971_);
v___x_973_ = l_Lean_mkConst(v_name_966_, v___x_972_);
v_lhs_974_ = l_Lean_mkAppN(v___x_973_, v_xs_959_);
lean_inc_ref(v_lhs_974_);
v___x_975_ = l_Lean_Meta_mkEq(v_lhs_974_, v_body_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; uint8_t v___x_977_; uint8_t v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = 0;
v___x_978_ = 1;
v___x_979_ = 1;
v___x_980_ = l_Lean_Meta_mkForallFVars(v_xs_959_, v_a_976_, v___x_977_, v___x_978_, v___x_978_, v___x_979_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = l_Lean_Meta_letToHave(v_a_981_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_Lean_Meta_mkEqRefl(v_lhs_974_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = l_Lean_Meta_mkLambdaFVars(v_xs_959_, v_a_985_, v___x_977_, v___x_978_, v___x_977_, v___x_978_, v___x_979_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
lean_inc(v_name_958_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 2, v_a_983_);
lean_ctor_set(v___x_969_, 0, v_name_958_);
v___x_989_ = v___x_969_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_name_958_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_levelParams_967_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_a_983_);
v___x_989_ = v_reuseFailAlloc_996_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___x_994_; 
lean_inc(v_name_958_);
v___x_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_990_, 0, v_name_958_);
lean_ctor_set(v___x_990_, 1, v___x_971_);
v___x_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v_a_987_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
v___x_992_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_991_, v___y_964_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v___x_992_);
v___x_994_ = l_Lean_addDecl(v_a_993_, v___x_977_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v___x_995_; 
lean_dec_ref_known(v___x_994_, 1);
v___x_995_ = l_Lean_inferDefEqAttr(v_name_958_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_995_;
}
else
{
lean_dec(v_name_958_);
return v___x_994_;
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_a_983_);
lean_del_object(v___x_969_);
lean_dec(v_levelParams_967_);
lean_dec(v_name_958_);
v_a_997_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_986_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_986_);
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
lean_dec(v_a_983_);
lean_del_object(v___x_969_);
lean_dec(v_levelParams_967_);
lean_dec(v_name_958_);
v_a_1005_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_984_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_984_);
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
lean_dec_ref(v_lhs_974_);
lean_del_object(v___x_969_);
lean_dec(v_levelParams_967_);
lean_dec(v_name_958_);
v_a_1013_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_982_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_982_);
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
lean_dec_ref(v_lhs_974_);
lean_del_object(v___x_969_);
lean_dec(v_levelParams_967_);
lean_dec(v_name_958_);
v_a_1021_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_980_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_980_);
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
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_lhs_974_);
lean_del_object(v___x_969_);
lean_dec(v_levelParams_967_);
lean_dec(v_name_958_);
v_a_1029_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_975_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_975_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1039_, lean_object* v_name_1040_, lean_object* v_xs_1041_, lean_object* v_body_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1039_, v_name_1040_, v_xs_1041_, v_body_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v_xs_1041_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1049_, lean_object* v_info_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_toConstantVal_1056_; lean_object* v_value_1057_; lean_object* v___f_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v_toConstantVal_1056_ = lean_ctor_get(v_info_1050_, 0);
lean_inc_ref(v_toConstantVal_1056_);
v_value_1057_ = lean_ctor_get(v_info_1050_, 1);
lean_inc_ref(v_value_1057_);
lean_dec_ref(v_info_1050_);
v___f_1058_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1058_, 0, v_toConstantVal_1056_);
lean_closure_set(v___f_1058_, 1, v_name_1049_);
v___x_1059_ = 1;
v___x_1060_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1057_, v___f_1058_, v___x_1059_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1061_, lean_object* v_info_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1061_, v_info_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1069_, lean_object* v_name_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1079_; lean_object* v_env_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = lean_st_ref_get(v_a_1074_);
v_env_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_env_1080_);
lean_dec(v___x_1079_);
v___x_1081_ = 0;
lean_inc(v_declName_1069_);
v___x_1082_ = l_Lean_Environment_find_x3f(v_env_1080_, v_declName_1069_, v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1110_; 
v_val_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1110_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1110_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
if (lean_obj_tag(v_val_1083_) == 1)
{
lean_object* v_val_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_val_1087_ = lean_ctor_get(v_val_1083_, 0);
lean_inc_ref(v_val_1087_);
lean_dec_ref_known(v_val_1083_, 1);
lean_inc_n(v_name_1070_, 2);
v___x_1088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1088_, 0, v_name_1070_);
lean_closure_set(v___x_1088_, 1, v_val_1087_);
lean_inc(v_declName_1069_);
v___x_1089_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1089_, 0, lean_box(0));
lean_closure_set(v___x_1089_, 1, v_declName_1069_);
lean_closure_set(v___x_1089_, 2, v___x_1088_);
v___x_1090_ = l_Lean_Meta_realizeConst(v_declName_1069_, v_name_1070_, v___x_1089_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1090_, 0);
lean_dec(v_unused_1101_);
v___x_1092_ = v___x_1090_;
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v___x_1090_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v_name_1070_);
v___x_1095_ = v___x_1085_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_name_1070_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_del_object(v___x_1085_);
lean_dec(v_name_1070_);
v_a_1102_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1090_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1090_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_del_object(v___x_1085_);
lean_dec(v_val_1083_);
lean_dec(v_name_1070_);
lean_dec(v_declName_1069_);
goto v___jp_1076_;
}
}
}
else
{
lean_dec(v___x_1082_);
lean_dec(v_name_1070_);
lean_dec(v_declName_1069_);
goto v___jp_1076_;
}
v___jp_1076_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1111_, lean_object* v_name_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1111_, v_name_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1119_, lean_object* v_vals_1120_, lean_object* v_i_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_array_get_size(v_keys_1119_);
v___x_1124_ = lean_nat_dec_lt(v_i_1121_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec(v_i_1121_);
v___x_1125_ = lean_box(0);
return v___x_1125_;
}
else
{
lean_object* v_k_x27_1126_; uint8_t v___x_1127_; 
v_k_x27_1126_ = lean_array_fget_borrowed(v_keys_1119_, v_i_1121_);
v___x_1127_ = lean_name_eq(v_k_1122_, v_k_x27_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v_i_1121_, v___x_1128_);
lean_dec(v_i_1121_);
v_i_1121_ = v___x_1129_;
goto _start;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_array_fget_borrowed(v_vals_1120_, v_i_1121_);
lean_dec(v_i_1121_);
lean_inc(v___x_1131_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1133_, lean_object* v_vals_1134_, lean_object* v_i_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1133_, v_vals_1134_, v_i_1135_, v_k_1136_);
lean_dec(v_k_1136_);
lean_dec_ref(v_vals_1134_);
lean_dec_ref(v_keys_1133_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1138_, size_t v_x_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
lean_object* v_es_1141_; lean_object* v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; lean_object* v_j_1145_; lean_object* v___x_1146_; 
v_es_1141_ = lean_ctor_get(v_x_1138_, 0);
v___x_1142_ = lean_box(2);
v___x_1143_ = ((size_t)31ULL);
v___x_1144_ = lean_usize_land(v_x_1139_, v___x_1143_);
v_j_1145_ = lean_usize_to_nat(v___x_1144_);
v___x_1146_ = lean_array_get_borrowed(v___x_1142_, v_es_1141_, v_j_1145_);
lean_dec(v_j_1145_);
switch(lean_obj_tag(v___x_1146_))
{
case 0:
{
lean_object* v_key_1147_; lean_object* v_val_1148_; uint8_t v___x_1149_; 
v_key_1147_ = lean_ctor_get(v___x_1146_, 0);
v_val_1148_ = lean_ctor_get(v___x_1146_, 1);
v___x_1149_ = lean_name_eq(v_x_1140_, v_key_1147_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_box(0);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; 
lean_inc(v_val_1148_);
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_val_1148_);
return v___x_1151_;
}
}
case 1:
{
lean_object* v_node_1152_; size_t v___x_1153_; size_t v___x_1154_; 
v_node_1152_ = lean_ctor_get(v___x_1146_, 0);
v___x_1153_ = ((size_t)5ULL);
v___x_1154_ = lean_usize_shift_right(v_x_1139_, v___x_1153_);
v_x_1138_ = v_node_1152_;
v_x_1139_ = v___x_1154_;
goto _start;
}
default: 
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_box(0);
return v___x_1156_;
}
}
}
else
{
lean_object* v_ks_1157_; lean_object* v_vs_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_ks_1157_ = lean_ctor_get(v_x_1138_, 0);
v_vs_1158_ = lean_ctor_get(v_x_1138_, 1);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1157_, v_vs_1158_, v___x_1159_, v_x_1140_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
size_t v_x_344__boxed_1164_; lean_object* v_res_1165_; 
v_x_344__boxed_1164_ = lean_unbox_usize(v_x_1162_);
lean_dec(v_x_1162_);
v_res_1165_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1161_, v_x_344__boxed_1164_, v_x_1163_);
lean_dec(v_x_1163_);
lean_dec_ref(v_x_1161_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
uint64_t v___y_1169_; 
if (lean_obj_tag(v_x_1167_) == 0)
{
uint64_t v___x_1172_; 
v___x_1172_ = 1723ULL;
v___y_1169_ = v___x_1172_;
goto v___jp_1168_;
}
else
{
uint64_t v_hash_1173_; 
v_hash_1173_ = lean_ctor_get_uint64(v_x_1167_, sizeof(void*)*2);
v___y_1169_ = v_hash_1173_;
goto v___jp_1168_;
}
v___jp_1168_:
{
size_t v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_uint64_to_usize(v___y_1169_);
v___x_1171_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1166_, v___x_1170_, v_x_1167_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1174_, v_x_1175_);
lean_dec(v_x_1175_);
lean_dec_ref(v_x_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_env_1182_; lean_object* v___x_1183_; lean_object* v_asyncMode_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1180_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1181_ = lean_st_ref_get(v_a_1178_);
v_env_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_env_1182_);
lean_dec(v___x_1181_);
v___x_1183_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1184_ = lean_ctor_get(v___x_1183_, 2);
v___x_1185_ = lean_box(0);
v___x_1186_ = 0;
v___x_1187_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1180_, v___x_1183_, v_env_1182_, v_asyncMode_1184_, v___x_1185_, v___x_1186_);
v___x_1188_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1187_, v_thmName_1177_);
lean_dec(v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1190_, v_a_1191_);
lean_dec(v_a_1191_);
lean_dec(v_thmName_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1194_, v_a_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_thmName_1199_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1205_, v_x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1208_, v_x_1209_, v_x_1210_);
lean_dec(v_x_1210_);
lean_dec_ref(v_x_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1212_, lean_object* v_x_1213_, size_t v_x_1214_, lean_object* v_x_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1213_, v_x_1214_, v_x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1217_, lean_object* v_x_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
size_t v_x_439__boxed_1221_; lean_object* v_res_1222_; 
v_x_439__boxed_1221_ = lean_unbox_usize(v_x_1219_);
lean_dec(v_x_1219_);
v_res_1222_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1217_, v_x_1218_, v_x_439__boxed_1221_, v_x_1220_);
lean_dec(v_x_1220_);
lean_dec_ref(v_x_1218_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1223_, lean_object* v_keys_1224_, lean_object* v_vals_1225_, lean_object* v_heq_1226_, lean_object* v_i_1227_, lean_object* v_k_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1224_, v_vals_1225_, v_i_1227_, v_k_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1230_, lean_object* v_keys_1231_, lean_object* v_vals_1232_, lean_object* v_heq_1233_, lean_object* v_i_1234_, lean_object* v_k_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1230_, v_keys_1231_, v_vals_1232_, v_heq_1233_, v_i_1234_, v_k_1235_);
lean_dec(v_k_1235_);
lean_dec_ref(v_vals_1232_);
lean_dec_ref(v_keys_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1237_, lean_object* v_i_1238_, lean_object* v_k_1239_){
_start:
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = lean_array_get_size(v_keys_1237_);
v___x_1241_ = lean_nat_dec_lt(v_i_1238_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_dec(v_i_1238_);
return v___x_1241_;
}
else
{
lean_object* v_k_x27_1242_; uint8_t v___x_1243_; 
v_k_x27_1242_ = lean_array_fget_borrowed(v_keys_1237_, v_i_1238_);
v___x_1243_ = lean_name_eq(v_k_1239_, v_k_x27_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_i_1238_, v___x_1244_);
lean_dec(v_i_1238_);
v_i_1238_ = v___x_1245_;
goto _start;
}
else
{
lean_dec(v_i_1238_);
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1247_, lean_object* v_i_1248_, lean_object* v_k_1249_){
_start:
{
uint8_t v_res_1250_; lean_object* v_r_1251_; 
v_res_1250_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1247_, v_i_1248_, v_k_1249_);
lean_dec(v_k_1249_);
lean_dec_ref(v_keys_1247_);
v_r_1251_ = lean_box(v_res_1250_);
return v_r_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1252_, size_t v_x_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v_es_1255_; lean_object* v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; lean_object* v_j_1259_; lean_object* v___x_1260_; 
v_es_1255_ = lean_ctor_get(v_x_1252_, 0);
v___x_1256_ = lean_box(2);
v___x_1257_ = ((size_t)31ULL);
v___x_1258_ = lean_usize_land(v_x_1253_, v___x_1257_);
v_j_1259_ = lean_usize_to_nat(v___x_1258_);
v___x_1260_ = lean_array_get_borrowed(v___x_1256_, v_es_1255_, v_j_1259_);
lean_dec(v_j_1259_);
switch(lean_obj_tag(v___x_1260_))
{
case 0:
{
lean_object* v_key_1261_; uint8_t v___x_1262_; 
v_key_1261_ = lean_ctor_get(v___x_1260_, 0);
v___x_1262_ = lean_name_eq(v_x_1254_, v_key_1261_);
return v___x_1262_;
}
case 1:
{
lean_object* v_node_1263_; size_t v___x_1264_; size_t v___x_1265_; 
v_node_1263_ = lean_ctor_get(v___x_1260_, 0);
v___x_1264_ = ((size_t)5ULL);
v___x_1265_ = lean_usize_shift_right(v_x_1253_, v___x_1264_);
v_x_1252_ = v_node_1263_;
v_x_1253_ = v___x_1265_;
goto _start;
}
default: 
{
uint8_t v___x_1267_; 
v___x_1267_ = 0;
return v___x_1267_;
}
}
}
else
{
lean_object* v_ks_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_ks_1268_ = lean_ctor_get(v_x_1252_, 0);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1268_, v___x_1269_, v_x_1254_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
size_t v_x_328__boxed_1274_; uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_x_328__boxed_1274_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_res_1275_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1271_, v_x_328__boxed_1274_, v_x_1273_);
lean_dec(v_x_1273_);
lean_dec_ref(v_x_1271_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
uint64_t v___y_1280_; 
if (lean_obj_tag(v_x_1278_) == 0)
{
uint64_t v___x_1283_; 
v___x_1283_ = 1723ULL;
v___y_1280_ = v___x_1283_;
goto v___jp_1279_;
}
else
{
uint64_t v_hash_1284_; 
v_hash_1284_ = lean_ctor_get_uint64(v_x_1278_, sizeof(void*)*2);
v___y_1280_ = v_hash_1284_;
goto v___jp_1279_;
}
v___jp_1279_:
{
size_t v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_uint64_to_usize(v___y_1280_);
v___x_1282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1277_, v___x_1281_, v_x_1278_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1285_, v_x_1286_);
lean_dec(v_x_1286_);
lean_dec_ref(v_x_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_env_1294_; lean_object* v___x_1295_; lean_object* v_asyncMode_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1292_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1293_ = lean_st_ref_get(v_a_1290_);
v_env_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc_ref(v_env_1294_);
lean_dec(v___x_1293_);
v___x_1295_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1296_ = lean_ctor_get(v___x_1295_, 2);
v___x_1297_ = lean_box(0);
v___x_1298_ = 0;
v___x_1299_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1292_, v___x_1295_, v_env_1294_, v_asyncMode_1296_, v___x_1297_, v___x_1298_);
v___x_1300_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1299_, v_thmName_1289_);
lean_dec(v___x_1299_);
v___x_1301_ = lean_box(v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec(v_thmName_1303_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1307_, v_a_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Meta_isEqnThm(v_thmName_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_thmName_1312_);
return v_res_1316_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1318_, v_x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1321_, v_x_1322_, v_x_1323_);
lean_dec(v_x_1323_);
lean_dec_ref(v_x_1322_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, size_t v_x_1328_, lean_object* v_x_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1327_, v_x_1328_, v_x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
size_t v_x_419__boxed_1335_; uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_x_419__boxed_1335_ = lean_unbox_usize(v_x_1333_);
lean_dec(v_x_1333_);
v_res_1336_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1331_, v_x_1332_, v_x_419__boxed_1335_, v_x_1334_);
lean_dec(v_x_1334_);
lean_dec_ref(v_x_1332_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1338_, lean_object* v_keys_1339_, lean_object* v_vals_1340_, lean_object* v_heq_1341_, lean_object* v_i_1342_, lean_object* v_k_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1339_, v_i_1342_, v_k_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1345_, lean_object* v_keys_1346_, lean_object* v_vals_1347_, lean_object* v_heq_1348_, lean_object* v_i_1349_, lean_object* v_k_1350_){
_start:
{
uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_res_1351_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1345_, v_keys_1346_, v_vals_1347_, v_heq_1348_, v_i_1349_, v_k_1350_);
lean_dec(v_k_1350_);
lean_dec_ref(v_vals_1347_);
lean_dec_ref(v_keys_1346_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_x1_1353_, lean_object* v_msg_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_panic_fn_borrowed(v_x1_1353_, v_msg_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_x1_1356_, lean_object* v_msg_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_panic___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_x1_1356_, v_msg_1357_);
lean_dec_ref(v_x1_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_ks_1363_; lean_object* v_vs_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1388_; 
v_ks_1363_ = lean_ctor_get(v_x_1359_, 0);
v_vs_1364_ = lean_ctor_get(v_x_1359_, 1);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1359_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1366_ = v_x_1359_;
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_vs_1364_);
lean_inc(v_ks_1363_);
lean_dec(v_x_1359_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = lean_array_get_size(v_ks_1363_);
v___x_1369_ = lean_nat_dec_lt(v_x_1360_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
lean_dec(v_x_1360_);
v___x_1370_ = lean_array_push(v_ks_1363_, v_x_1361_);
v___x_1371_ = lean_array_push(v_vs_1364_, v_x_1362_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___x_1371_);
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v_k_x27_1375_; uint8_t v___x_1376_; 
v_k_x27_1375_ = lean_array_fget_borrowed(v_ks_1363_, v_x_1360_);
v___x_1376_ = lean_name_eq(v_x_1361_, v_k_x27_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1378_; 
if (v_isShared_1367_ == 0)
{
v___x_1378_ = v___x_1366_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_ks_1363_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_vs_1364_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_nat_add(v_x_1360_, v___x_1379_);
lean_dec(v_x_1360_);
v_x_1359_ = v___x_1378_;
v_x_1360_ = v___x_1380_;
goto _start;
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = lean_array_fset(v_ks_1363_, v_x_1360_, v_x_1361_);
v___x_1384_ = lean_array_fset(v_vs_1364_, v_x_1360_, v_x_1362_);
lean_dec(v_x_1360_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___x_1384_);
lean_ctor_set(v___x_1366_, 0, v___x_1383_);
v___x_1386_ = v___x_1366_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1389_, lean_object* v_k_1390_, lean_object* v_v_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1389_, v___x_1392_, v_k_1390_, v_v_1391_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1395_, size_t v_x_1396_, size_t v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
lean_object* v_es_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v_j_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_es_1400_ = lean_ctor_get(v_x_1395_, 0);
v___x_1401_ = ((size_t)31ULL);
v___x_1402_ = lean_usize_land(v_x_1396_, v___x_1401_);
v_j_1403_ = lean_usize_to_nat(v___x_1402_);
v___x_1404_ = lean_array_get_size(v_es_1400_);
v___x_1405_ = lean_nat_dec_lt(v_j_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_dec(v_j_1403_);
lean_dec(v_x_1399_);
lean_dec(v_x_1398_);
return v_x_1395_;
}
else
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1444_; 
lean_inc_ref(v_es_1400_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_x_1395_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_x_1395_, 0);
lean_dec(v_unused_1445_);
v___x_1407_ = v_x_1395_;
v_isShared_1408_ = v_isSharedCheck_1444_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_x_1395_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1444_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_v_1409_; lean_object* v___x_1410_; lean_object* v_xs_x27_1411_; lean_object* v___y_1413_; 
v_v_1409_ = lean_array_fget(v_es_1400_, v_j_1403_);
v___x_1410_ = lean_box(0);
v_xs_x27_1411_ = lean_array_fset(v_es_1400_, v_j_1403_, v___x_1410_);
switch(lean_obj_tag(v_v_1409_))
{
case 0:
{
lean_object* v_key_1418_; lean_object* v_val_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1429_; 
v_key_1418_ = lean_ctor_get(v_v_1409_, 0);
v_val_1419_ = lean_ctor_get(v_v_1409_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_v_1409_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1421_ = v_v_1409_;
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_val_1419_);
lean_inc(v_key_1418_);
lean_dec(v_v_1409_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_name_eq(v_x_1398_, v_key_1418_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_del_object(v___x_1421_);
v___x_1424_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1418_, v_val_1419_, v_x_1398_, v_x_1399_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
v___y_1413_ = v___x_1425_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_val_1419_);
lean_dec(v_key_1418_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v_x_1399_);
lean_ctor_set(v___x_1421_, 0, v_x_1398_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_x_1398_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_x_1399_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
v___y_1413_ = v___x_1427_;
goto v___jp_1412_;
}
}
}
}
case 1:
{
lean_object* v_node_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1442_; 
v_node_1430_ = lean_ctor_get(v_v_1409_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_v_1409_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1432_ = v_v_1409_;
v_isShared_1433_ = v_isSharedCheck_1442_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_node_1430_);
lean_dec(v_v_1409_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1442_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
size_t v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1434_ = ((size_t)5ULL);
v___x_1435_ = lean_usize_shift_right(v_x_1396_, v___x_1434_);
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_x_1397_, v___x_1436_);
v___x_1438_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1430_, v___x_1435_, v___x_1437_, v_x_1398_, v_x_1399_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1438_);
v___x_1440_ = v___x_1432_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v___y_1413_ = v___x_1440_;
goto v___jp_1412_;
}
}
}
default: 
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_x_1398_);
lean_ctor_set(v___x_1443_, 1, v_x_1399_);
v___y_1413_ = v___x_1443_;
goto v___jp_1412_;
}
}
v___jp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_array_fset(v_xs_x27_1411_, v_j_1403_, v___y_1413_);
lean_dec(v_j_1403_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1414_);
v___x_1416_ = v___x_1407_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
lean_object* v_ks_1446_; lean_object* v_vs_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1465_; 
v_ks_1446_ = lean_ctor_get(v_x_1395_, 0);
v_vs_1447_ = lean_ctor_get(v_x_1395_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1395_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1449_ = v_x_1395_;
v_isShared_1450_ = v_isSharedCheck_1465_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_vs_1447_);
lean_inc(v_ks_1446_);
lean_dec(v_x_1395_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1465_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_ks_1446_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_vs_1447_);
v___x_1452_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v_newNode_1453_; size_t v___x_1454_; uint8_t v___x_1455_; 
v_newNode_1453_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v___x_1452_, v_x_1398_, v_x_1399_);
v___x_1454_ = ((size_t)7ULL);
v___x_1455_ = lean_usize_dec_le(v___x_1454_, v_x_1397_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1453_);
v___x_1457_ = lean_unsigned_to_nat(4u);
v___x_1458_ = lean_nat_dec_lt(v___x_1456_, v___x_1457_);
lean_dec(v___x_1456_);
if (v___x_1458_ == 0)
{
lean_object* v_ks_1459_; lean_object* v_vs_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_ks_1459_ = lean_ctor_get(v_newNode_1453_, 0);
lean_inc_ref(v_ks_1459_);
v_vs_1460_ = lean_ctor_get(v_newNode_1453_, 1);
lean_inc_ref(v_vs_1460_);
lean_dec_ref(v_newNode_1453_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_x_1397_, v_ks_1459_, v_vs_1460_, v___x_1461_, v___x_1462_);
lean_dec_ref(v_vs_1460_);
lean_dec_ref(v_ks_1459_);
return v___x_1463_;
}
else
{
return v_newNode_1453_;
}
}
else
{
return v_newNode_1453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(size_t v_depth_1466_, lean_object* v_keys_1467_, lean_object* v_vals_1468_, lean_object* v_i_1469_, lean_object* v_entries_1470_){
_start:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = lean_array_get_size(v_keys_1467_);
v___x_1472_ = lean_nat_dec_lt(v_i_1469_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_dec(v_i_1469_);
return v_entries_1470_;
}
else
{
lean_object* v_k_1473_; lean_object* v_v_1474_; uint64_t v___y_1476_; 
v_k_1473_ = lean_array_fget_borrowed(v_keys_1467_, v_i_1469_);
v_v_1474_ = lean_array_fget_borrowed(v_vals_1468_, v_i_1469_);
if (lean_obj_tag(v_k_1473_) == 0)
{
uint64_t v___x_1487_; 
v___x_1487_ = 1723ULL;
v___y_1476_ = v___x_1487_;
goto v___jp_1475_;
}
else
{
uint64_t v_hash_1488_; 
v_hash_1488_ = lean_ctor_get_uint64(v_k_1473_, sizeof(void*)*2);
v___y_1476_ = v_hash_1488_;
goto v___jp_1475_;
}
v___jp_1475_:
{
size_t v_h_1477_; size_t v___x_1478_; lean_object* v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; size_t v_h_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_h_1477_ = lean_uint64_to_usize(v___y_1476_);
v___x_1478_ = ((size_t)5ULL);
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_sub(v_depth_1466_, v___x_1480_);
v___x_1482_ = lean_usize_mul(v___x_1478_, v___x_1481_);
v_h_1483_ = lean_usize_shift_right(v_h_1477_, v___x_1482_);
v___x_1484_ = lean_nat_add(v_i_1469_, v___x_1479_);
lean_dec(v_i_1469_);
lean_inc(v_v_1474_);
lean_inc(v_k_1473_);
v___x_1485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1470_, v_h_1483_, v_depth_1466_, v_k_1473_, v_v_1474_);
v_i_1469_ = v___x_1484_;
v_entries_1470_ = v___x_1485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1489_, lean_object* v_keys_1490_, lean_object* v_vals_1491_, lean_object* v_i_1492_, lean_object* v_entries_1493_){
_start:
{
size_t v_depth_boxed_1494_; lean_object* v_res_1495_; 
v_depth_boxed_1494_ = lean_unbox_usize(v_depth_1489_);
lean_dec(v_depth_1489_);
v_res_1495_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1494_, v_keys_1490_, v_vals_1491_, v_i_1492_, v_entries_1493_);
lean_dec_ref(v_vals_1491_);
lean_dec_ref(v_keys_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
size_t v_x_905__boxed_1501_; size_t v_x_906__boxed_1502_; lean_object* v_res_1503_; 
v_x_905__boxed_1501_ = lean_unbox_usize(v_x_1497_);
lean_dec(v_x_1497_);
v_x_906__boxed_1502_ = lean_unbox_usize(v_x_1498_);
lean_dec(v_x_1498_);
v_res_1503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1496_, v_x_905__boxed_1501_, v_x_906__boxed_1502_, v_x_1499_, v_x_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_){
_start:
{
uint64_t v___y_1508_; 
if (lean_obj_tag(v_x_1505_) == 0)
{
uint64_t v___x_1512_; 
v___x_1512_ = 1723ULL;
v___y_1508_ = v___x_1512_;
goto v___jp_1507_;
}
else
{
uint64_t v_hash_1513_; 
v_hash_1513_ = lean_ctor_get_uint64(v_x_1505_, sizeof(void*)*2);
v___y_1508_ = v_hash_1513_;
goto v___jp_1507_;
}
v___jp_1507_:
{
size_t v___x_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_uint64_to_usize(v___y_1508_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1504_, v___x_1509_, v___x_1510_, v_x_1505_, v_x_1506_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(lean_object* v_declName_1519_, lean_object* v_as_1520_, size_t v_i_1521_, size_t v_stop_1522_, lean_object* v_b_1523_){
_start:
{
lean_object* v___y_1525_; uint8_t v___x_1529_; 
v___x_1529_ = lean_usize_dec_eq(v_i_1521_, v_stop_1522_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_array_uget_borrowed(v_as_1520_, v_i_1521_);
v___x_1531_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_b_1523_, v___x_1530_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; 
lean_inc(v_declName_1519_);
lean_inc(v___x_1530_);
v___x_1532_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1523_, v___x_1530_, v_declName_1519_);
v___y_1525_ = v___x_1532_;
goto v___jp_1524_;
}
else
{
lean_object* v_val_1533_; uint8_t v___x_1534_; 
v_val_1533_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1534_ = lean_name_eq(v_val_1533_, v_declName_1519_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1535_ = 1;
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__0));
v___x_1537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__1));
v___x_1538_ = lean_unsigned_to_nat(227u);
v___x_1539_ = lean_unsigned_to_nat(10u);
v___x_1540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__2));
lean_inc(v___x_1530_);
v___x_1541_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1530_, v___x_1535_);
v___x_1542_ = lean_string_append(v___x_1540_, v___x_1541_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__3));
v___x_1544_ = lean_string_append(v___x_1542_, v___x_1543_);
v___x_1545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1533_, v___x_1535_);
v___x_1546_ = lean_string_append(v___x_1544_, v___x_1545_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_1548_ = lean_string_append(v___x_1546_, v___x_1547_);
v___x_1549_ = l_mkPanicMessageWithDecl(v___x_1536_, v___x_1537_, v___x_1538_, v___x_1539_, v___x_1548_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = lean_panic_fn_borrowed(v_b_1523_, v___x_1549_);
lean_dec_ref(v_b_1523_);
v___y_1525_ = v___x_1550_;
goto v___jp_1524_;
}
else
{
lean_dec(v_val_1533_);
v___y_1525_ = v_b_1523_;
goto v___jp_1524_;
}
}
}
else
{
lean_dec(v_declName_1519_);
return v_b_1523_;
}
v___jp_1524_:
{
size_t v___x_1526_; size_t v___x_1527_; 
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_add(v_i_1521_, v___x_1526_);
v_i_1521_ = v___x_1527_;
v_b_1523_ = v___y_1525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___boxed(lean_object* v_declName_1551_, lean_object* v_as_1552_, lean_object* v_i_1553_, lean_object* v_stop_1554_, lean_object* v_b_1555_){
_start:
{
size_t v_i_boxed_1556_; size_t v_stop_boxed_1557_; lean_object* v_res_1558_; 
v_i_boxed_1556_ = lean_unbox_usize(v_i_1553_);
lean_dec(v_i_1553_);
v_stop_boxed_1557_ = lean_unbox_usize(v_stop_1554_);
lean_dec(v_stop_1554_);
v_res_1558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1551_, v_as_1552_, v_i_boxed_1556_, v_stop_boxed_1557_, v_b_1555_);
lean_dec_ref(v_as_1552_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1559_, lean_object* v_declName_1560_, lean_object* v_s_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = lean_array_get_size(v_eqThms_1559_);
v___x_1564_ = lean_nat_dec_lt(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_dec(v_declName_1560_);
return v_s_1561_;
}
else
{
size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = lean_usize_of_nat(v___x_1563_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2(v_declName_1560_, v_eqThms_1559_, v___x_1565_, v___x_1566_, v_s_1561_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1568_, lean_object* v_declName_1569_, lean_object* v_s_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1568_, v_declName_1569_, v_s_1570_);
lean_dec_ref(v_eqThms_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1572_, lean_object* v_eqThms_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v_env_1578_; lean_object* v_nextMacroScope_1579_; lean_object* v_ngen_1580_; lean_object* v_auxDeclNGen_1581_; lean_object* v_traceState_1582_; lean_object* v_recordedDeps_1583_; lean_object* v_messages_1584_; lean_object* v_infoState_1585_; lean_object* v_snapshotTasks_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1602_; 
v___f_1576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1576_, 0, v_eqThms_1573_);
lean_closure_set(v___f_1576_, 1, v_declName_1572_);
v___x_1577_ = lean_st_ref_take(v_a_1574_);
v_env_1578_ = lean_ctor_get(v___x_1577_, 0);
v_nextMacroScope_1579_ = lean_ctor_get(v___x_1577_, 1);
v_ngen_1580_ = lean_ctor_get(v___x_1577_, 2);
v_auxDeclNGen_1581_ = lean_ctor_get(v___x_1577_, 3);
v_traceState_1582_ = lean_ctor_get(v___x_1577_, 4);
v_recordedDeps_1583_ = lean_ctor_get(v___x_1577_, 6);
v_messages_1584_ = lean_ctor_get(v___x_1577_, 7);
v_infoState_1585_ = lean_ctor_get(v___x_1577_, 8);
v_snapshotTasks_1586_ = lean_ctor_get(v___x_1577_, 9);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v___x_1577_, 5);
lean_dec(v_unused_1603_);
v___x_1588_ = v___x_1577_;
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_snapshotTasks_1586_);
lean_inc(v_infoState_1585_);
lean_inc(v_messages_1584_);
lean_inc(v_recordedDeps_1583_);
lean_inc(v_traceState_1582_);
lean_inc(v_auxDeclNGen_1581_);
lean_inc(v_ngen_1580_);
lean_inc(v_nextMacroScope_1579_);
lean_inc(v_env_1578_);
lean_dec(v___x_1577_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v_asyncMode_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1590_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1591_ = lean_ctor_get(v___x_1590_, 2);
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_box(0);
v___x_1594_ = 1;
v___x_1595_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_1590_, v_env_1578_, v___f_1576_, v_asyncMode_1591_, v___x_1593_, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 5, v___x_1596_);
lean_ctor_set(v___x_1588_, 0, v___x_1595_);
v___x_1598_ = v___x_1588_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_nextMacroScope_1579_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_ngen_1580_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_auxDeclNGen_1581_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_traceState_1582_);
lean_ctor_set(v_reuseFailAlloc_1601_, 5, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1601_, 6, v_recordedDeps_1583_);
lean_ctor_set(v_reuseFailAlloc_1601_, 7, v_messages_1584_);
lean_ctor_set(v_reuseFailAlloc_1601_, 8, v_infoState_1585_);
lean_ctor_set(v_reuseFailAlloc_1601_, 9, v_snapshotTasks_1586_);
v___x_1598_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_st_ref_put(v_a_1574_, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1592_);
return v___x_1600_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1604_, lean_object* v_eqThms_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1604_, v_eqThms_1605_, v_a_1606_);
lean_dec(v_a_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1609_, lean_object* v_eqThms_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1609_, v_eqThms_1610_, v_a_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1615_, lean_object* v_eqThms_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1615_, v_eqThms_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1622_, v_x_1623_, v_x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, size_t v_x_1628_, size_t v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1627_, v_x_1628_, v_x_1629_, v_x_1630_, v_x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
size_t v_x_1219__boxed_1639_; size_t v_x_1220__boxed_1640_; lean_object* v_res_1641_; 
v_x_1219__boxed_1639_ = lean_unbox_usize(v_x_1635_);
lean_dec(v_x_1635_);
v_x_1220__boxed_1640_ = lean_unbox_usize(v_x_1636_);
lean_dec(v_x_1636_);
v_res_1641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1633_, v_x_1634_, v_x_1219__boxed_1639_, v_x_1220__boxed_1640_, v_x_1637_, v_x_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1642_, lean_object* v_n_1643_, lean_object* v_k_1644_, lean_object* v_v_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_n_1643_, v_k_1644_, v_v_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1647_, size_t v_depth_1648_, lean_object* v_keys_1649_, lean_object* v_vals_1650_, lean_object* v_heq_1651_, lean_object* v_i_1652_, lean_object* v_entries_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___redArg(v_depth_1648_, v_keys_1649_, v_vals_1650_, v_i_1652_, v_entries_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_depth_1656_, lean_object* v_keys_1657_, lean_object* v_vals_1658_, lean_object* v_heq_1659_, lean_object* v_i_1660_, lean_object* v_entries_1661_){
_start:
{
size_t v_depth_boxed_1662_; lean_object* v_res_1663_; 
v_depth_boxed_1662_ = lean_unbox_usize(v_depth_1656_);
lean_dec(v_depth_1656_);
v_res_1663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__3(v_00_u03b2_1655_, v_depth_boxed_1662_, v_keys_1657_, v_vals_1658_, v_heq_1659_, v_i_1660_, v_entries_1661_);
lean_dec_ref(v_vals_1658_);
lean_dec_ref(v_keys_1657_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1665_, v_x_1666_, v_x_1667_, v_x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1670_, lean_object* v_env_1671_, lean_object* v_idx_1672_, lean_object* v_eqs_1673_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_nextEq_1680_; uint8_t v___x_1681_; 
v___x_1675_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1676_ = lean_unsigned_to_nat(1u);
v___x_1677_ = lean_nat_add(v_idx_1672_, v___x_1676_);
lean_dec(v_idx_1672_);
lean_inc(v___x_1677_);
v___x_1678_ = l_Nat_reprFast(v___x_1677_);
v___x_1679_ = lean_string_append(v___x_1675_, v___x_1678_);
lean_dec_ref(v___x_1678_);
lean_inc(v_declName_1670_);
lean_inc_ref(v_env_1671_);
v_nextEq_1680_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1671_, v_declName_1670_, v___x_1679_);
v___x_1681_ = l_Lean_Environment_containsOnBranch(v_env_1671_, v_nextEq_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; 
lean_dec(v_nextEq_1680_);
lean_dec(v___x_1677_);
lean_dec_ref(v_env_1671_);
lean_dec(v_declName_1670_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_eqs_1673_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_array_push(v_eqs_1673_, v_nextEq_1680_);
v_idx_1672_ = v___x_1677_;
v_eqs_1673_ = v___x_1683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1685_, lean_object* v_env_1686_, lean_object* v_idx_1687_, lean_object* v_eqs_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1685_, v_env_1686_, v_idx_1687_, v_eqs_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1691_, lean_object* v_env_1692_, lean_object* v_idx_1693_, lean_object* v_eqs_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1691_, v_env_1692_, v_idx_1693_, v_eqs_1694_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1701_, lean_object* v_env_1702_, lean_object* v_idx_1703_, lean_object* v_eqs_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1701_, v_env_1702_, v_idx_1703_, v_eqs_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v_env_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; uint8_t v___x_1719_; 
v___x_1714_ = lean_st_ref_get(v_a_1712_);
v_env_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc_ref_n(v_env_1715_, 3);
lean_dec(v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1711_);
v___x_1717_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1715_, v_declName_1711_, v___x_1716_);
v___x_1718_ = 1;
lean_inc(v___x_1717_);
v___x_1719_ = l_Lean_Environment_contains(v_env_1715_, v___x_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec(v___x_1717_);
lean_dec_ref(v_env_1715_);
lean_dec(v_declName_1711_);
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_mk_empty_array_with_capacity(v___x_1722_);
v___x_1724_ = lean_array_push(v___x_1723_, v___x_1717_);
lean_inc(v_declName_1711_);
v___x_1725_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1711_, v_env_1715_, v___x_1722_, v___x_1724_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1735_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_n(v_a_1726_, 2);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1711_, v_a_1726_, v_a_1712_);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v___x_1727_, 0);
lean_dec(v_unused_1736_);
v___x_1729_ = v___x_1727_;
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v___x_1727_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1726_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1731_);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_declName_1711_);
v_a_1737_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1725_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1745_, v_a_1746_);
lean_dec(v_a_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1749_, v_a_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1763_, lean_object* v_localInsts_1764_, lean_object* v_x_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1763_, v_localInsts_1764_, v_x_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_a_1780_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1771_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1771_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1788_, lean_object* v_localInsts_1789_, lean_object* v_x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1788_, v_localInsts_1789_, v_x_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1797_, lean_object* v_lctx_1798_, lean_object* v_localInsts_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1798_, v_localInsts_1799_, v_x_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_lctx_1808_, lean_object* v_localInsts_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1807_, v_lctx_1808_, v_localInsts_1809_, v_x_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1820_, lean_object* v_as_x27_1821_, lean_object* v_b_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
if (lean_obj_tag(v_as_x27_1821_) == 0)
{
lean_object* v___x_1828_; 
lean_dec(v_declName_1820_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_b_1822_);
return v___x_1828_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec_ref(v_b_1822_);
v_head_1829_ = lean_ctor_get(v_as_x27_1821_, 0);
v_tail_1830_ = lean_ctor_get(v_as_x27_1821_, 1);
v___x_1831_ = lean_box(0);
v___x_1832_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1829_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
lean_inc(v_declName_1820_);
v___x_1833_ = lean_apply_6(v_head_1829_, v_declName_1820_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, lean_box(0));
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
if (lean_obj_tag(v_a_1834_) == 1)
{
lean_object* v_val_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
v_val_1835_ = lean_ctor_get(v_a_1834_, 0);
lean_inc(v_val_1835_);
v___x_1836_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1820_, v_val_1835_, v___y_1826_);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; 
v_unused_1846_ = lean_ctor_get(v___x_1836_, 0);
lean_dec(v_unused_1846_);
v___x_1838_ = v___x_1836_;
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
else
{
lean_dec(v___x_1836_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1834_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1831_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
else
{
lean_dec(v_a_1834_);
v_as_x27_1821_ = v_tail_1830_;
v_b_1822_ = v___x_1832_;
goto _start;
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_declName_1820_);
v_a_1848_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1833_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1833_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1856_, lean_object* v_as_x27_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1856_, v_as_x27_1857_, v_b_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_as_x27_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
lean_inc(v_declName_1865_);
v___x_1871_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1909_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1909_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1909_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_unbox(v_a_1872_);
lean_dec(v_a_1872_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_dec(v_declName_1865_);
v___x_1877_ = lean_box(0);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1877_);
v___x_1879_ = v___x_1874_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v___x_1881_; 
lean_del_object(v___x_1874_);
lean_inc(v_declName_1865_);
v___x_1881_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1865_, v___y_1869_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
if (lean_obj_tag(v_a_1882_) == 1)
{
lean_dec(v_declName_1865_);
return v___x_1881_;
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1884_ = lean_st_ref_get(v___x_1883_);
v___x_1885_ = lean_box(0);
v___x_1886_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1887_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1865_, v___x_1884_, v___x_1886_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___x_1884_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1900_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_fst_1892_; 
v_fst_1892_ = lean_ctor_get(v_a_1888_, 0);
lean_inc(v_fst_1892_);
lean_dec(v_a_1888_);
if (lean_obj_tag(v_fst_1892_) == 0)
{
lean_object* v___x_1894_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1885_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1885_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
else
{
lean_object* v_val_1896_; lean_object* v___x_1898_; 
v_val_1896_ = lean_ctor_get(v_fst_1892_, 0);
lean_inc(v_val_1896_);
lean_dec_ref_known(v_fst_1892_, 1);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v_val_1896_);
v___x_1898_ = v___x_1890_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_val_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1887_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1887_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
else
{
lean_dec(v_declName_1865_);
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_declName_1865_);
v_a_1910_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1871_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1871_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1927_ = lean_box(1);
v___x_1928_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1929_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v___x_1928_);
lean_ctor_set(v___x_1930_, 2, v___x_1927_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v___f_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___f_1939_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1939_, 0, v_declName_1933_);
v___x_1940_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1941_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1942_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1940_, v___x_1941_, v___f_1939_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1950_, lean_object* v_as_1951_, lean_object* v_as_x27_1952_, lean_object* v_b_1953_, lean_object* v_a_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1950_, v_as_x27_1952_, v_b_1953_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1961_, lean_object* v_as_1962_, lean_object* v_as_x27_1963_, lean_object* v_b_1964_, lean_object* v_a_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1961_, v_as_1962_, v_as_x27_1963_, v_b_1964_, v_a_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v_as_x27_1963_);
lean_dec(v_as_1962_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1978_ = lean_unsigned_to_nat(32u);
v___x_1979_ = lean_mk_empty_array_with_capacity(v___x_1978_);
lean_dec_ref(v___x_1979_);
v___x_1980_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1981_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1972_);
v___x_1982_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1982_, 0, v_declName_1972_);
v___x_1983_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1983_, 0, lean_box(0));
lean_closure_set(v___x_1983_, 1, v_declName_1972_);
lean_closure_set(v___x_1983_, 2, v___x_1982_);
v___x_1984_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1980_, v___x_1981_, v___x_1983_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
return v_res_1991_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_1992_, lean_object* v_opt_1993_){
_start:
{
lean_object* v_name_1994_; lean_object* v_defValue_1995_; lean_object* v_map_1996_; lean_object* v___x_1997_; 
v_name_1994_ = lean_ctor_get(v_opt_1993_, 0);
v_defValue_1995_ = lean_ctor_get(v_opt_1993_, 1);
v_map_1996_ = lean_ctor_get(v_opts_1992_, 0);
v___x_1997_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1996_, v_name_1994_);
if (lean_obj_tag(v___x_1997_) == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_unbox(v_defValue_1995_);
return v___x_1998_;
}
else
{
lean_object* v_val_1999_; 
v_val_1999_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_val_1999_);
lean_dec_ref_known(v___x_1997_, 1);
if (lean_obj_tag(v_val_1999_) == 1)
{
uint8_t v_v_2000_; 
v_v_2000_ = lean_ctor_get_uint8(v_val_1999_, 0);
lean_dec_ref_known(v_val_1999_, 0);
return v_v_2000_;
}
else
{
uint8_t v___x_2001_; 
lean_dec(v_val_1999_);
v___x_2001_ = lean_unbox(v_defValue_1995_);
return v___x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_2002_, lean_object* v_opt_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2002_, v_opt_2003_);
lean_dec_ref(v_opt_2003_);
lean_dec_ref(v_opts_2002_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_2006_, lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_){
_start:
{
lean_object* v_a_2013_; uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_b_2010_);
return v___x_2018_;
}
else
{
lean_object* v_a_2019_; lean_object* v_name_2020_; lean_object* v_defValue_2021_; uint8_t v___x_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2033_; 
v_a_2019_ = lean_array_uget(v_as_2007_, v_i_2009_);
v_name_2020_ = lean_ctor_get(v_a_2019_, 0);
lean_inc(v_name_2020_);
v_defValue_2021_ = lean_ctor_get(v_a_2019_, 1);
lean_inc(v_defValue_2021_);
v___x_2022_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2006_, v_a_2019_);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_a_2019_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; lean_object* v_unused_2035_; 
v_unused_2034_ = lean_ctor_get(v_a_2019_, 1);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_a_2019_, 0);
lean_dec(v_unused_2035_);
v___x_2024_ = v_a_2019_;
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v_a_2019_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_unbox(v_defValue_2021_);
lean_dec(v_defValue_2021_);
if (v___x_2032_ == 0)
{
if (v___x_2022_ == 0)
{
lean_del_object(v___x_2024_);
lean_dec(v_name_2020_);
v_a_2013_ = v_b_2010_;
goto v___jp_2012_;
}
else
{
goto v___jp_2026_;
}
}
else
{
if (v___x_2022_ == 0)
{
goto v___jp_2026_;
}
else
{
lean_del_object(v___x_2024_);
lean_dec(v_name_2020_);
v_a_2013_ = v_b_2010_;
goto v___jp_2012_;
}
}
v___jp_2026_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2027_, 0, v___x_2022_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_name_2020_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_array_push(v_b_2010_, v___x_2029_);
v_a_2013_ = v___x_2030_;
goto v___jp_2012_;
}
}
}
}
v___jp_2012_:
{
size_t v___x_2014_; size_t v___x_2015_; 
v___x_2014_ = ((size_t)1ULL);
v___x_2015_ = lean_usize_add(v_i_2009_, v___x_2014_);
v_i_2009_ = v___x_2015_;
v_b_2010_ = v_a_2013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_2036_, lean_object* v_as_2037_, lean_object* v_sz_2038_, lean_object* v_i_2039_, lean_object* v_b_2040_, lean_object* v___y_2041_){
_start:
{
size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2038_);
lean_dec(v_sz_2038_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2039_);
lean_dec(v_i_2039_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2036_, v_as_2037_, v_sz_boxed_2042_, v_i_boxed_2043_, v_b_2040_);
lean_dec_ref(v_as_2037_);
lean_dec_ref(v___x_2036_);
return v_res_2044_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___closed__0);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg();
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(lean_object* v_msgData_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v_env_2058_; uint8_t v___x_2059_; lean_object* v_env_2060_; lean_object* v___x_2061_; lean_object* v_toCold_2062_; lean_object* v_mctx_2063_; lean_object* v_lctx_2064_; lean_object* v_options_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2057_ = lean_st_ref_get(v___y_2055_);
v_env_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_ref(v_env_2058_);
lean_dec(v___x_2057_);
v___x_2059_ = 0;
v_env_2060_ = l_Lean_Environment_setRecordingDeps(v_env_2058_, v___x_2059_);
v___x_2061_ = lean_st_ref_get(v___y_2053_);
v_toCold_2062_ = lean_ctor_get(v___y_2054_, 0);
v_mctx_2063_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref(v_mctx_2063_);
lean_dec(v___x_2061_);
v_lctx_2064_ = lean_ctor_get(v___y_2052_, 2);
v_options_2065_ = lean_ctor_get(v_toCold_2062_, 2);
lean_inc_ref(v_options_2065_);
lean_inc_ref(v_lctx_2064_);
v___x_2066_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2066_, 0, v_env_2060_);
lean_ctor_set(v___x_2066_, 1, v_mctx_2063_);
lean_ctor_set(v___x_2066_, 2, v_lctx_2064_);
lean_ctor_set(v___x_2066_, 3, v_options_2065_);
v___x_2067_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v_msgData_2051_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4___boxed(lean_object* v_msgData_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msgData_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2075_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2076_; double v___x_2077_; 
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_float_of_nat(v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(lean_object* v_cls_2081_, lean_object* v_msg_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_ref_2088_; lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2135_; 
v_ref_2088_ = lean_ctor_get(v___y_2085_, 2);
v___x_2089_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msg_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2135_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2135_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v_traceState_2095_; lean_object* v_env_2096_; lean_object* v_nextMacroScope_2097_; lean_object* v_ngen_2098_; lean_object* v_auxDeclNGen_2099_; lean_object* v_cache_2100_; lean_object* v_recordedDeps_2101_; lean_object* v_messages_2102_; lean_object* v_infoState_2103_; lean_object* v_snapshotTasks_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2134_; 
v___x_2094_ = lean_st_ref_take(v___y_2086_);
v_traceState_2095_ = lean_ctor_get(v___x_2094_, 4);
v_env_2096_ = lean_ctor_get(v___x_2094_, 0);
v_nextMacroScope_2097_ = lean_ctor_get(v___x_2094_, 1);
v_ngen_2098_ = lean_ctor_get(v___x_2094_, 2);
v_auxDeclNGen_2099_ = lean_ctor_get(v___x_2094_, 3);
v_cache_2100_ = lean_ctor_get(v___x_2094_, 5);
v_recordedDeps_2101_ = lean_ctor_get(v___x_2094_, 6);
v_messages_2102_ = lean_ctor_get(v___x_2094_, 7);
v_infoState_2103_ = lean_ctor_get(v___x_2094_, 8);
v_snapshotTasks_2104_ = lean_ctor_get(v___x_2094_, 9);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2106_ = v___x_2094_;
v_isShared_2107_ = v_isSharedCheck_2134_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_snapshotTasks_2104_);
lean_inc(v_infoState_2103_);
lean_inc(v_messages_2102_);
lean_inc(v_recordedDeps_2101_);
lean_inc(v_cache_2100_);
lean_inc(v_traceState_2095_);
lean_inc(v_auxDeclNGen_2099_);
lean_inc(v_ngen_2098_);
lean_inc(v_nextMacroScope_2097_);
lean_inc(v_env_2096_);
lean_dec(v___x_2094_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2134_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
uint64_t v_tid_2108_; lean_object* v_traces_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2133_; 
v_tid_2108_ = lean_ctor_get_uint64(v_traceState_2095_, sizeof(void*)*1);
v_traces_2109_ = lean_ctor_get(v_traceState_2095_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_traceState_2095_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2111_ = v_traceState_2095_;
v_isShared_2112_ = v_isSharedCheck_2133_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_traces_2109_);
lean_dec(v_traceState_2095_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2133_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; double v___x_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0);
v___x_2116_ = 0;
v___x_2117_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1));
v___x_2118_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2118_, 0, v_cls_2081_);
lean_ctor_set(v___x_2118_, 1, v___x_2114_);
lean_ctor_set(v___x_2118_, 2, v___x_2117_);
lean_ctor_set_float(v___x_2118_, sizeof(void*)*3, v___x_2115_);
lean_ctor_set_float(v___x_2118_, sizeof(void*)*3 + 8, v___x_2115_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*3 + 16, v___x_2116_);
v___x_2119_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__2));
v___x_2120_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v_a_2090_);
lean_ctor_set(v___x_2120_, 2, v___x_2119_);
lean_inc(v_ref_2088_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_ref_2088_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = l_Lean_PersistentArray_push___redArg(v_traces_2109_, v___x_2121_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2122_);
v___x_2124_ = v___x_2111_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2122_);
lean_ctor_set_uint64(v_reuseFailAlloc_2132_, sizeof(void*)*1, v_tid_2108_);
v___x_2124_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 4, v___x_2124_);
v___x_2126_ = v___x_2106_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_env_2096_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_nextMacroScope_2097_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_ngen_2098_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_auxDeclNGen_2099_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2131_, 5, v_cache_2100_);
lean_ctor_set(v_reuseFailAlloc_2131_, 6, v_recordedDeps_2101_);
lean_ctor_set(v_reuseFailAlloc_2131_, 7, v_messages_2102_);
lean_ctor_set(v_reuseFailAlloc_2131_, 8, v_infoState_2103_);
lean_ctor_set(v_reuseFailAlloc_2131_, 9, v_snapshotTasks_2104_);
v___x_2126_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_st_ref_put(v___y_2086_, v___x_2126_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2113_);
v___x_2129_ = v___x_2092_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2113_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___boxed(lean_object* v_cls_2136_, lean_object* v_msg_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(v_cls_2136_, v_msg_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2143_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2146_; size_t v_sz_2147_; 
v___x_2146_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2147_ = lean_array_size(v___x_2146_);
return v_sz_2147_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___redArg();
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__3(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2150_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
v___x_2151_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v___x_2149_);
lean_ctor_set(v___x_2151_, 2, v___x_2149_);
lean_ctor_set(v___x_2151_, 3, v___x_2149_);
lean_ctor_set(v___x_2151_, 4, v___x_2149_);
lean_ctor_set(v___x_2151_, 5, v___x_2149_);
lean_ctor_set(v___x_2151_, 6, v___x_2149_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__7(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__6));
v___x_2159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2160_ = l_Lean_Name_append(v___x_2159_, v___x_2158_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__9(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__8));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; size_t v_sz_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2170_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2167_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2173_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2174_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2175_ = ((size_t)0ULL);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2170_, v___x_2173_, v_sz_2174_, v___x_2175_, v___x_2172_);
lean_dec_ref(v___x_2170_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2240_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2240_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2240_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___y_2184_; lean_object* v___y_2185_; 
v___x_2181_ = lean_array_get_size(v_a_2177_);
v___x_2182_ = lean_nat_dec_eq(v___x_2181_, v___x_2171_);
if (v___x_2182_ == 0)
{
lean_object* v_toCold_2227_; lean_object* v_options_2228_; uint8_t v_hasTrace_2229_; 
v_toCold_2227_ = lean_ctor_get(v_a_2167_, 0);
v_options_2228_ = lean_ctor_get(v_toCold_2227_, 2);
v_hasTrace_2229_ = lean_ctor_get_uint8(v_options_2228_, sizeof(void*)*1);
if (v_hasTrace_2229_ == 0)
{
v___y_2184_ = v_a_2166_;
v___y_2185_ = v_a_2168_;
goto v___jp_2183_;
}
else
{
lean_object* v_inheritedTraceOptions_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v_inheritedTraceOptions_2230_ = lean_ctor_get(v_toCold_2227_, 11);
v___x_2231_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__6));
v___x_2232_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__7, &l_Lean_Meta_saveEqnAffectingOptions___closed__7_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__7);
v___x_2233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2230_, v_options_2228_, v___x_2232_);
if (v___x_2233_ == 0)
{
v___y_2184_ = v_a_2166_;
v___y_2185_ = v_a_2168_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__9, &l_Lean_Meta_saveEqnAffectingOptions___closed__9_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__9);
lean_inc(v_declName_2164_);
v___x_2235_ = l_Lean_MessageData_ofName(v_declName_2164_);
v___x_2236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2234_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3(v___x_2231_, v___x_2236_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_dec_ref_known(v___x_2237_, 1);
v___y_2184_ = v_a_2166_;
v___y_2185_ = v_a_2168_;
goto v___jp_2183_;
}
else
{
lean_del_object(v___x_2179_);
lean_dec(v_a_2177_);
lean_dec(v_declName_2164_);
return v___x_2237_;
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_del_object(v___x_2179_);
lean_dec(v_a_2177_);
lean_dec(v_declName_2164_);
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
v___jp_2183_:
{
lean_object* v___x_2186_; lean_object* v_env_2187_; lean_object* v_nextMacroScope_2188_; lean_object* v_ngen_2189_; lean_object* v_auxDeclNGen_2190_; lean_object* v_traceState_2191_; lean_object* v_recordedDeps_2192_; lean_object* v_messages_2193_; lean_object* v_infoState_2194_; lean_object* v_snapshotTasks_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2225_; 
v___x_2186_ = lean_st_ref_take(v___y_2185_);
v_env_2187_ = lean_ctor_get(v___x_2186_, 0);
v_nextMacroScope_2188_ = lean_ctor_get(v___x_2186_, 1);
v_ngen_2189_ = lean_ctor_get(v___x_2186_, 2);
v_auxDeclNGen_2190_ = lean_ctor_get(v___x_2186_, 3);
v_traceState_2191_ = lean_ctor_get(v___x_2186_, 4);
v_recordedDeps_2192_ = lean_ctor_get(v___x_2186_, 6);
v_messages_2193_ = lean_ctor_get(v___x_2186_, 7);
v_infoState_2194_ = lean_ctor_get(v___x_2186_, 8);
v_snapshotTasks_2195_ = lean_ctor_get(v___x_2186_, 9);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v___x_2186_, 5);
lean_dec(v_unused_2226_);
v___x_2197_ = v___x_2186_;
v_isShared_2198_ = v_isSharedCheck_2225_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_snapshotTasks_2195_);
lean_inc(v_infoState_2194_);
lean_inc(v_messages_2193_);
lean_inc(v_recordedDeps_2192_);
lean_inc(v_traceState_2191_);
lean_inc(v_auxDeclNGen_2190_);
lean_inc(v_ngen_2189_);
lean_inc(v_nextMacroScope_2188_);
lean_inc(v_env_2187_);
lean_dec(v___x_2186_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2225_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2199_ = l_Lean_Meta_eqnOptionsExt;
v___x_2200_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2199_, v_env_2187_, v_declName_2164_, v_a_2177_, v___x_2182_);
v___x_2201_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 5, v___x_2201_);
lean_ctor_set(v___x_2197_, 0, v___x_2200_);
v___x_2203_ = v___x_2197_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_nextMacroScope_2188_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_ngen_2189_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_auxDeclNGen_2190_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_traceState_2191_);
lean_ctor_set(v_reuseFailAlloc_2224_, 5, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2224_, 6, v_recordedDeps_2192_);
lean_ctor_set(v_reuseFailAlloc_2224_, 7, v_messages_2193_);
lean_ctor_set(v_reuseFailAlloc_2224_, 8, v_infoState_2194_);
lean_ctor_set(v_reuseFailAlloc_2224_, 9, v_snapshotTasks_2195_);
v___x_2203_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_mctx_2206_; lean_object* v_zetaDeltaFVarIds_2207_; lean_object* v_postponed_2208_; lean_object* v_diag_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2222_; 
v___x_2204_ = lean_st_ref_put(v___y_2185_, v___x_2203_);
v___x_2205_ = lean_st_ref_take(v___y_2184_);
v_mctx_2206_ = lean_ctor_get(v___x_2205_, 0);
v_zetaDeltaFVarIds_2207_ = lean_ctor_get(v___x_2205_, 2);
v_postponed_2208_ = lean_ctor_get(v___x_2205_, 3);
v_diag_2209_ = lean_ctor_get(v___x_2205_, 4);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v___x_2205_, 1);
lean_dec(v_unused_2223_);
v___x_2211_ = v___x_2205_;
v_isShared_2212_ = v_isSharedCheck_2222_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_diag_2209_);
lean_inc(v_postponed_2208_);
lean_inc(v_zetaDeltaFVarIds_2207_);
lean_inc(v_mctx_2206_);
lean_dec(v___x_2205_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2222_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__3, &l_Lean_Meta_saveEqnAffectingOptions___closed__3_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__3);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___x_2214_);
v___x_2216_ = v___x_2211_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_mctx_2206_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_zetaDeltaFVarIds_2207_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_postponed_2208_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_diag_2209_);
v___x_2216_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = lean_st_ref_put(v___y_2184_, v___x_2216_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2213_);
v___x_2219_ = v___x_2179_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2213_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
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
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_declName_2164_);
v_a_2241_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2176_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2176_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2256_, lean_object* v_as_2257_, size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2256_, v_as_2257_, v_sz_2258_, v_i_2259_, v_b_2260_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2267_, lean_object* v_as_2268_, lean_object* v_sz_2269_, lean_object* v_i_2270_, lean_object* v_b_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
size_t v_sz_boxed_2277_; size_t v_i_boxed_2278_; lean_object* v_res_2279_; 
v_sz_boxed_2277_ = lean_unbox_usize(v_sz_2269_);
lean_dec(v_sz_2269_);
v_i_boxed_2278_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2267_, v_as_2268_, v_sz_boxed_2277_, v_i_boxed_2278_, v_b_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_as_2268_);
lean_dec_ref(v___x_2267_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_00_u03b2_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg(){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg___boxed(lean_object* v___dummy_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___redArg();
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_00_u03b2_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = lean_st_mk_ref(v___x_2289_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2294_){
_start:
{
uint8_t v___x_2296_; 
v___x_2296_ = l_Lean_initializing();
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v_f_2294_);
v___x_2297_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2299_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2300_ = lean_st_ref_take(v___x_2299_);
v___x_2301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_f_2294_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_st_ref_put(v___x_2299_, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2304_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2310_, lean_object* v_as_x27_2311_, lean_object* v_b_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
if (lean_obj_tag(v_as_x27_2311_) == 0)
{
lean_object* v___x_2318_; 
lean_dec(v_declName_2310_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_b_2312_);
return v___x_2318_;
}
else
{
lean_object* v_head_2319_; lean_object* v_tail_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_b_2312_);
v_head_2319_ = lean_ctor_get(v_as_x27_2311_, 0);
v_tail_2320_ = lean_ctor_get(v_as_x27_2311_, 1);
v___x_2321_ = lean_box(0);
v___x_2322_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2319_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
lean_inc(v_declName_2310_);
v___x_2323_ = lean_apply_6(v_head_2319_, v_declName_2310_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, lean_box(0));
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2334_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2334_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2334_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
if (lean_obj_tag(v_a_2324_) == 1)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
lean_dec(v_declName_2310_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2324_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2321_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
else
{
lean_del_object(v___x_2326_);
lean_dec(v_a_2324_);
v_as_x27_2311_ = v_tail_2320_;
v_b_2312_ = v___x_2322_;
goto _start;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_declName_2310_);
v_a_2335_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2323_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2323_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2343_, lean_object* v_as_x27_2344_, lean_object* v_b_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2343_, v_as_x27_2344_, v_b_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v_as_x27_2344_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2352_, lean_object* v_declName_2353_, uint8_t v_nonRec_2354_, lean_object* v___x_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2364_; lean_object* v_env_2365_; uint8_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2364_ = lean_st_ref_get(v___y_2359_);
v_env_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_ref(v_env_2365_);
lean_dec(v___x_2364_);
v___x_2366_ = 1;
lean_inc(v___x_2352_);
v___x_2367_ = l_Lean_Environment_contains(v_env_2365_, v___x_2352_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; 
lean_dec(v___x_2352_);
lean_inc(v_declName_2353_);
v___x_2368_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2353_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; uint8_t v___x_2370_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2370_ = lean_unbox(v_a_2369_);
lean_dec(v_a_2369_);
if (v___x_2370_ == 0)
{
lean_dec_ref(v___x_2355_);
lean_dec(v_declName_2353_);
goto v___jp_2361_;
}
else
{
lean_object* v___x_2371_; 
lean_inc(v_declName_2353_);
v___x_2371_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2353_, v___y_2359_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; uint8_t v___x_2373_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = lean_unbox(v_a_2372_);
lean_dec(v_a_2372_);
if (v___x_2373_ == 0)
{
if (v_nonRec_2354_ == 0)
{
lean_dec_ref(v___x_2355_);
lean_dec(v_declName_2353_);
goto v___jp_2361_;
}
else
{
lean_object* v___x_2374_; lean_object* v_env_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2374_ = lean_st_ref_get(v___y_2359_);
v_env_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc_ref(v_env_2375_);
lean_dec(v___x_2374_);
lean_inc(v_declName_2353_);
v___x_2376_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2375_, v_declName_2353_, v___x_2355_);
v___x_2377_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2353_, v___x_2376_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
return v___x_2377_;
}
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec_ref(v___x_2355_);
v___x_2378_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2379_ = lean_st_ref_get(v___x_2378_);
v___x_2380_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2381_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2353_, v___x_2379_, v___x_2380_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___x_2379_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2391_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_fst_2386_; 
v_fst_2386_ = lean_ctor_get(v_a_2382_, 0);
lean_inc(v_fst_2386_);
lean_dec(v_a_2382_);
if (lean_obj_tag(v_fst_2386_) == 0)
{
lean_del_object(v___x_2384_);
goto v___jp_2361_;
}
else
{
lean_object* v_val_2387_; lean_object* v___x_2389_; 
v_val_2387_ = lean_ctor_get(v_fst_2386_, 0);
lean_inc(v_val_2387_);
lean_dec_ref_known(v_fst_2386_, 1);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_val_2387_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_val_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2381_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2381_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec_ref(v___x_2355_);
lean_dec(v_declName_2353_);
v_a_2400_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2371_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2371_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec_ref(v___x_2355_);
lean_dec(v_declName_2353_);
v_a_2408_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2368_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2368_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec_ref(v___x_2355_);
lean_dec(v_declName_2353_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2352_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
v___jp_2361_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_box(0);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2418_, lean_object* v_declName_2419_, lean_object* v_nonRec_2420_, lean_object* v___x_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
uint8_t v_nonRec_boxed_2427_; lean_object* v_res_2428_; 
v_nonRec_boxed_2427_ = lean_unbox(v_nonRec_2420_);
v_res_2428_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2418_, v_declName_2419_, v_nonRec_boxed_2427_, v___x_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_ref_2435_; lean_object* v___x_2436_; lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2445_; 
v_ref_2435_ = lean_ctor_get(v___y_2432_, 2);
v___x_2436_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3_spec__4(v_msg_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
lean_inc(v_ref_2435_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_ref_2435_);
lean_ctor_set(v___x_2441_, 1, v_a_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set_tag(v___x_2439_, 1);
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2453_, uint8_t v_isExporting_2454_, lean_object* v___x_2455_, lean_object* v___y_2456_, lean_object* v___x_2457_, lean_object* v_a_x3f_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v_env_2461_; lean_object* v_nextMacroScope_2462_; lean_object* v_ngen_2463_; lean_object* v_auxDeclNGen_2464_; lean_object* v_traceState_2465_; lean_object* v_recordedDeps_2466_; lean_object* v_messages_2467_; lean_object* v_infoState_2468_; lean_object* v_snapshotTasks_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2494_; 
v___x_2460_ = lean_st_ref_take(v___y_2453_);
v_env_2461_ = lean_ctor_get(v___x_2460_, 0);
v_nextMacroScope_2462_ = lean_ctor_get(v___x_2460_, 1);
v_ngen_2463_ = lean_ctor_get(v___x_2460_, 2);
v_auxDeclNGen_2464_ = lean_ctor_get(v___x_2460_, 3);
v_traceState_2465_ = lean_ctor_get(v___x_2460_, 4);
v_recordedDeps_2466_ = lean_ctor_get(v___x_2460_, 6);
v_messages_2467_ = lean_ctor_get(v___x_2460_, 7);
v_infoState_2468_ = lean_ctor_get(v___x_2460_, 8);
v_snapshotTasks_2469_ = lean_ctor_get(v___x_2460_, 9);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v___x_2460_, 5);
lean_dec(v_unused_2495_);
v___x_2471_ = v___x_2460_;
v_isShared_2472_ = v_isSharedCheck_2494_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_snapshotTasks_2469_);
lean_inc(v_infoState_2468_);
lean_inc(v_messages_2467_);
lean_inc(v_recordedDeps_2466_);
lean_inc(v_traceState_2465_);
lean_inc(v_auxDeclNGen_2464_);
lean_inc(v_ngen_2463_);
lean_inc(v_nextMacroScope_2462_);
lean_inc(v_env_2461_);
lean_dec(v___x_2460_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2494_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = l_Lean_Environment_setExporting(v_env_2461_, v_isExporting_2454_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 5, v___x_2455_);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_nextMacroScope_2462_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_ngen_2463_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_auxDeclNGen_2464_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_traceState_2465_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_recordedDeps_2466_);
lean_ctor_set(v_reuseFailAlloc_2493_, 7, v_messages_2467_);
lean_ctor_set(v_reuseFailAlloc_2493_, 8, v_infoState_2468_);
lean_ctor_set(v_reuseFailAlloc_2493_, 9, v_snapshotTasks_2469_);
v___x_2475_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_mctx_2478_; lean_object* v_zetaDeltaFVarIds_2479_; lean_object* v_postponed_2480_; lean_object* v_diag_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2491_; 
v___x_2476_ = lean_st_ref_put(v___y_2453_, v___x_2475_);
v___x_2477_ = lean_st_ref_take(v___y_2456_);
v_mctx_2478_ = lean_ctor_get(v___x_2477_, 0);
v_zetaDeltaFVarIds_2479_ = lean_ctor_get(v___x_2477_, 2);
v_postponed_2480_ = lean_ctor_get(v___x_2477_, 3);
v_diag_2481_ = lean_ctor_get(v___x_2477_, 4);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2477_, 1);
lean_dec(v_unused_2492_);
v___x_2483_ = v___x_2477_;
v_isShared_2484_ = v_isSharedCheck_2491_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_diag_2481_);
lean_inc(v_postponed_2480_);
lean_inc(v_zetaDeltaFVarIds_2479_);
lean_inc(v_mctx_2478_);
lean_dec(v___x_2477_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2491_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2485_ = lean_box(0);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 1, v___x_2457_);
v___x_2487_ = v___x_2483_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_mctx_2478_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_zetaDeltaFVarIds_2479_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_postponed_2480_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_diag_2481_);
v___x_2487_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_st_ref_put(v___y_2456_, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2485_);
return v___x_2489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2496_, lean_object* v_isExporting_2497_, lean_object* v___x_2498_, lean_object* v___y_2499_, lean_object* v___x_2500_, lean_object* v_a_x3f_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v_isExporting_boxed_2503_; lean_object* v_res_2504_; 
v_isExporting_boxed_2503_ = lean_unbox(v_isExporting_2497_);
v_res_2504_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2496_, v_isExporting_boxed_2503_, v___x_2498_, v___y_2499_, v___x_2500_, v_a_x3f_2501_);
lean_dec(v_a_x3f_2501_);
lean_dec(v___y_2499_);
lean_dec(v___y_2496_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2505_, uint8_t v_isExporting_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v_env_2513_; lean_object* v___x_2514_; uint8_t v_isModule_2515_; 
v___x_2512_ = lean_st_ref_get(v___y_2510_);
v_env_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc_ref(v_env_2513_);
lean_dec(v___x_2512_);
v___x_2514_ = l_Lean_Environment_header(v_env_2513_);
v_isModule_2515_ = lean_ctor_get_uint8(v___x_2514_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2514_);
if (v_isModule_2515_ == 0)
{
lean_object* v___x_2516_; 
lean_dec_ref(v_env_2513_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
v___x_2516_ = lean_apply_5(v_x_2505_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
return v___x_2516_;
}
else
{
uint8_t v_isExporting_2517_; 
v_isExporting_2517_ = lean_ctor_get_uint8(v_env_2513_, sizeof(void*)*13);
lean_dec_ref(v_env_2513_);
if (v_isExporting_2506_ == 0)
{
if (v_isExporting_2517_ == 0)
{
lean_object* v___x_2584_; 
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
v___x_2584_ = lean_apply_5(v_x_2505_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
return v___x_2584_;
}
else
{
goto v___jp_2518_;
}
}
else
{
if (v_isExporting_2517_ == 0)
{
goto v___jp_2518_;
}
else
{
lean_object* v___x_2585_; 
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
v___x_2585_ = lean_apply_5(v_x_2505_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
return v___x_2585_;
}
}
v___jp_2518_:
{
lean_object* v___x_2519_; lean_object* v_env_2520_; lean_object* v_nextMacroScope_2521_; lean_object* v_ngen_2522_; lean_object* v_auxDeclNGen_2523_; lean_object* v_traceState_2524_; lean_object* v_recordedDeps_2525_; lean_object* v_messages_2526_; lean_object* v_infoState_2527_; lean_object* v_snapshotTasks_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2582_; 
v___x_2519_ = lean_st_ref_take(v___y_2510_);
v_env_2520_ = lean_ctor_get(v___x_2519_, 0);
v_nextMacroScope_2521_ = lean_ctor_get(v___x_2519_, 1);
v_ngen_2522_ = lean_ctor_get(v___x_2519_, 2);
v_auxDeclNGen_2523_ = lean_ctor_get(v___x_2519_, 3);
v_traceState_2524_ = lean_ctor_get(v___x_2519_, 4);
v_recordedDeps_2525_ = lean_ctor_get(v___x_2519_, 6);
v_messages_2526_ = lean_ctor_get(v___x_2519_, 7);
v_infoState_2527_ = lean_ctor_get(v___x_2519_, 8);
v_snapshotTasks_2528_ = lean_ctor_get(v___x_2519_, 9);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2519_, 5);
lean_dec(v_unused_2583_);
v___x_2530_ = v___x_2519_;
v_isShared_2531_ = v_isSharedCheck_2582_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_snapshotTasks_2528_);
lean_inc(v_infoState_2527_);
lean_inc(v_messages_2526_);
lean_inc(v_recordedDeps_2525_);
lean_inc(v_traceState_2524_);
lean_inc(v_auxDeclNGen_2523_);
lean_inc(v_ngen_2522_);
lean_inc(v_nextMacroScope_2521_);
lean_inc(v_env_2520_);
lean_dec(v___x_2519_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2582_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = l_Lean_Environment_setExporting(v_env_2520_, v_isExporting_2506_);
v___x_2533_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 5, v___x_2533_);
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_nextMacroScope_2521_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_ngen_2522_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_auxDeclNGen_2523_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_traceState_2524_);
lean_ctor_set(v_reuseFailAlloc_2581_, 5, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_recordedDeps_2525_);
lean_ctor_set(v_reuseFailAlloc_2581_, 7, v_messages_2526_);
lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_infoState_2527_);
lean_ctor_set(v_reuseFailAlloc_2581_, 9, v_snapshotTasks_2528_);
v___x_2535_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_mctx_2538_; lean_object* v_zetaDeltaFVarIds_2539_; lean_object* v_postponed_2540_; lean_object* v_diag_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2579_; 
v___x_2536_ = lean_st_ref_put(v___y_2510_, v___x_2535_);
v___x_2537_ = lean_st_ref_take(v___y_2508_);
v_mctx_2538_ = lean_ctor_get(v___x_2537_, 0);
v_zetaDeltaFVarIds_2539_ = lean_ctor_get(v___x_2537_, 2);
v_postponed_2540_ = lean_ctor_get(v___x_2537_, 3);
v_diag_2541_ = lean_ctor_get(v___x_2537_, 4);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2537_, 1);
lean_dec(v_unused_2580_);
v___x_2543_ = v___x_2537_;
v_isShared_2544_ = v_isSharedCheck_2579_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_diag_2541_);
lean_inc(v_postponed_2540_);
lean_inc(v_zetaDeltaFVarIds_2539_);
lean_inc(v_mctx_2538_);
lean_dec(v___x_2537_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2579_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__3, &l_Lean_Meta_saveEqnAffectingOptions___closed__3_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__3);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_mctx_2538_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_zetaDeltaFVarIds_2539_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_postponed_2540_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_diag_2541_);
v___x_2547_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v_r_2549_; 
v___x_2548_ = lean_st_ref_put(v___y_2508_, v___x_2547_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
v_r_2549_ = lean_apply_5(v_x_2505_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
if (lean_obj_tag(v_r_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2566_; 
v_a_2550_ = lean_ctor_get(v_r_2549_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_r_2549_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2552_ = v_r_2549_;
v_isShared_2553_ = v_isSharedCheck_2566_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v_r_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2566_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
lean_inc(v_a_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set_tag(v___x_2552_, 1);
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v___x_2556_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2510_, v_isExporting_2517_, v___x_2533_, v___y_2508_, v___x_2545_, v___x_2555_);
lean_dec_ref(v___x_2555_);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v___x_2556_, 0);
lean_dec(v_unused_2564_);
v___x_2558_ = v___x_2556_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_dec(v___x_2556_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v_a_2550_);
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2550_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_a_2567_ = lean_ctor_get(v_r_2549_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v_r_2549_, 1);
v___x_2568_ = lean_box(0);
v___x_2569_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2510_, v_isExporting_2517_, v___x_2533_, v___y_2508_, v___x_2545_, v___x_2568_);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; 
v_unused_2577_ = lean_ctor_get(v___x_2569_, 0);
lean_dec(v_unused_2577_);
v___x_2571_ = v___x_2569_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_dec(v___x_2569_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 1);
lean_ctor_set(v___x_2571_, 0, v_a_2567_);
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2567_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2586_, lean_object* v_isExporting_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
uint8_t v_isExporting_boxed_2593_; lean_object* v_res_2594_; 
v_isExporting_boxed_2593_ = lean_unbox(v_isExporting_2587_);
v_res_2594_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2586_, v_isExporting_boxed_2593_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2595_, uint8_t v_when_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
if (v_when_2596_ == 0)
{
lean_object* v___x_2602_; 
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
v___x_2602_ = lean_apply_5(v_x_2595_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, lean_box(0));
return v___x_2602_;
}
else
{
uint8_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = 0;
v___x_2604_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2595_, v___x_2603_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2605_, lean_object* v_when_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
uint8_t v_when_boxed_2612_; lean_object* v_res_2613_; 
v_when_boxed_2612_ = lean_unbox(v_when_2606_);
v_res_2613_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2605_, v_when_boxed_2612_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2613_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2619_ = l_Lean_stringToMessageData(v___x_2618_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__2___closed__4));
v___x_2621_ = l_Lean_stringToMessageData(v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2622_, uint8_t v_nonRec_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; lean_object* v_env_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___f_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2629_ = lean_st_ref_get(v___y_2627_);
v_env_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_ref(v_env_2630_);
lean_dec(v___x_2629_);
v___x_2631_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2622_);
v___x_2632_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2630_, v_declName_2622_, v___x_2631_);
v___x_2633_ = lean_box(v_nonRec_2623_);
lean_inc(v___x_2632_);
v___f_2634_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2634_, 0, v___x_2632_);
lean_closure_set(v___f_2634_, 1, v_declName_2622_);
lean_closure_set(v___f_2634_, 2, v___x_2633_);
lean_closure_set(v___f_2634_, 3, v___x_2631_);
v___x_2635_ = 1;
v___x_2636_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2634_, v___x_2635_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
if (lean_obj_tag(v_a_2637_) == 1)
{
lean_object* v_val_2638_; uint8_t v___x_2639_; 
v_val_2638_ = lean_ctor_get(v_a_2637_, 0);
v___x_2639_ = lean_name_eq(v_val_2638_, v___x_2632_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_inc(v_val_2638_);
lean_dec_ref_known(v___x_2636_, 1);
v___x_2640_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2641_ = l_Lean_MessageData_ofName(v_val_2638_);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_Lean_MessageData_ofName(v___x_2632_);
v___x_2646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2644_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2646_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2648_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
else
{
lean_dec(v___x_2632_);
return v___x_2636_;
}
}
else
{
lean_dec(v___x_2632_);
return v___x_2636_;
}
}
else
{
lean_dec(v___x_2632_);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2658_, lean_object* v_nonRec_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
uint8_t v_nonRec_boxed_2665_; lean_object* v_res_2666_; 
v_nonRec_boxed_2665_ = lean_unbox(v_nonRec_2659_);
v_res_2666_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2658_, v_nonRec_boxed_2665_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2667_, uint8_t v_nonRec_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v___x_2674_; lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2674_ = lean_box(v_nonRec_2668_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2675_, 0, v_declName_2667_);
lean_closure_set(v___f_2675_, 1, v___x_2674_);
v___x_2676_ = lean_unsigned_to_nat(32u);
v___x_2677_ = lean_mk_empty_array_with_capacity(v___x_2676_);
lean_dec_ref(v___x_2677_);
v___x_2678_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2680_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2678_, v___x_2679_, v___f_2675_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2681_, lean_object* v_nonRec_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
uint8_t v_nonRec_boxed_2688_; lean_object* v_res_2689_; 
v_nonRec_boxed_2688_ = lean_unbox(v_nonRec_2682_);
v_res_2689_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2681_, v_nonRec_boxed_2688_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2690_, lean_object* v_as_2691_, lean_object* v_as_x27_2692_, lean_object* v_b_2693_, lean_object* v_a_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2690_, v_as_x27_2692_, v_b_2693_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2701_, lean_object* v_as_2702_, lean_object* v_as_x27_2703_, lean_object* v_b_2704_, lean_object* v_a_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2701_, v_as_2702_, v_as_x27_2703_, v_b_2704_, v_a_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v_as_x27_2703_);
lean_dec(v_as_2702_);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2747_, lean_object* v_x_2748_, uint8_t v_isExporting_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2748_, v_isExporting_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_x_2757_, lean_object* v_isExporting_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v_isExporting_boxed_2764_; lean_object* v_res_2765_; 
v_isExporting_boxed_2764_ = lean_unbox(v_isExporting_2758_);
v_res_2765_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2756_, v_x_2757_, v_isExporting_boxed_2764_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2765_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_unsigned_to_nat(32u);
v___x_2767_ = lean_mk_empty_array_with_capacity(v___x_2766_);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2769_ = ((size_t)5ULL);
v___x_2770_ = lean_unsigned_to_nat(0u);
v___x_2771_ = lean_unsigned_to_nat(32u);
v___x_2772_ = lean_mk_empty_array_with_capacity(v___x_2771_);
v___x_2773_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2774_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___x_2772_);
lean_ctor_set(v___x_2774_, 2, v___x_2770_);
lean_ctor_set(v___x_2774_, 3, v___x_2770_);
lean_ctor_set_usize(v___x_2774_, 4, v___x_2769_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; lean_object* v_traceState_2778_; lean_object* v_traces_2779_; lean_object* v___x_2780_; lean_object* v_traceState_2781_; lean_object* v_env_2782_; lean_object* v_nextMacroScope_2783_; lean_object* v_ngen_2784_; lean_object* v_auxDeclNGen_2785_; lean_object* v_cache_2786_; lean_object* v_recordedDeps_2787_; lean_object* v_messages_2788_; lean_object* v_infoState_2789_; lean_object* v_snapshotTasks_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2809_; 
v___x_2777_ = lean_st_ref_get(v___y_2775_);
v_traceState_2778_ = lean_ctor_get(v___x_2777_, 4);
lean_inc_ref(v_traceState_2778_);
lean_dec(v___x_2777_);
v_traces_2779_ = lean_ctor_get(v_traceState_2778_, 0);
lean_inc_ref(v_traces_2779_);
lean_dec_ref(v_traceState_2778_);
v___x_2780_ = lean_st_ref_take(v___y_2775_);
v_traceState_2781_ = lean_ctor_get(v___x_2780_, 4);
v_env_2782_ = lean_ctor_get(v___x_2780_, 0);
v_nextMacroScope_2783_ = lean_ctor_get(v___x_2780_, 1);
v_ngen_2784_ = lean_ctor_get(v___x_2780_, 2);
v_auxDeclNGen_2785_ = lean_ctor_get(v___x_2780_, 3);
v_cache_2786_ = lean_ctor_get(v___x_2780_, 5);
v_recordedDeps_2787_ = lean_ctor_get(v___x_2780_, 6);
v_messages_2788_ = lean_ctor_get(v___x_2780_, 7);
v_infoState_2789_ = lean_ctor_get(v___x_2780_, 8);
v_snapshotTasks_2790_ = lean_ctor_get(v___x_2780_, 9);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2792_ = v___x_2780_;
v_isShared_2793_ = v_isSharedCheck_2809_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_snapshotTasks_2790_);
lean_inc(v_infoState_2789_);
lean_inc(v_messages_2788_);
lean_inc(v_recordedDeps_2787_);
lean_inc(v_cache_2786_);
lean_inc(v_traceState_2781_);
lean_inc(v_auxDeclNGen_2785_);
lean_inc(v_ngen_2784_);
lean_inc(v_nextMacroScope_2783_);
lean_inc(v_env_2782_);
lean_dec(v___x_2780_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2809_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
uint64_t v_tid_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2807_; 
v_tid_2794_ = lean_ctor_get_uint64(v_traceState_2781_, sizeof(void*)*1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_traceState_2781_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v_traceState_2781_, 0);
lean_dec(v_unused_2808_);
v___x_2796_ = v_traceState_2781_;
v_isShared_2797_ = v_isSharedCheck_2807_;
goto v_resetjp_2795_;
}
else
{
lean_dec(v_traceState_2781_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2807_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2798_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2798_);
v___x_2800_ = v___x_2796_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2798_);
lean_ctor_set_uint64(v_reuseFailAlloc_2806_, sizeof(void*)*1, v_tid_2794_);
v___x_2800_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2802_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 4, v___x_2800_);
v___x_2802_ = v___x_2792_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_env_2782_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_nextMacroScope_2783_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_ngen_2784_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_auxDeclNGen_2785_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2805_, 5, v_cache_2786_);
lean_ctor_set(v_reuseFailAlloc_2805_, 6, v_recordedDeps_2787_);
lean_ctor_set(v_reuseFailAlloc_2805_, 7, v_messages_2788_);
lean_ctor_set(v_reuseFailAlloc_2805_, 8, v_infoState_2789_);
lean_ctor_set(v_reuseFailAlloc_2805_, 9, v_snapshotTasks_2790_);
v___x_2802_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_st_ref_put(v___y_2775_, v___x_2802_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_traces_2779_);
return v___x_2804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2810_);
lean_dec(v___y_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = 0;
v___x_2826_ = lean_box(v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
return v_res_2832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2836_, lean_object* v_x_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2841_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2842_ = l_Lean_MessageData_ofName(v_name_2836_);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2845_, lean_object* v_x_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2845_, v_x_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_x_2846_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2851_){
_start:
{
if (lean_obj_tag(v_x_2851_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
v_a_2853_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v_x_2851_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v_x_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set_tag(v___x_2855_, 1);
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
v_a_2861_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v_x_2851_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v_x_2851_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set_tag(v___x_2863_, 0);
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2869_);
return v_res_2871_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2872_){
_start:
{
if (lean_obj_tag(v_e_2872_) == 0)
{
uint8_t v___x_2873_; 
v___x_2873_ = 2;
return v___x_2873_;
}
else
{
lean_object* v_a_2874_; uint8_t v___x_2875_; 
v_a_2874_ = lean_ctor_get(v_e_2872_, 0);
v___x_2875_ = lean_unbox(v_a_2874_);
if (v___x_2875_ == 0)
{
uint8_t v___x_2876_; 
v___x_2876_ = 1;
return v___x_2876_;
}
else
{
uint8_t v___x_2877_; 
v___x_2877_ = 0;
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2878_){
_start:
{
uint8_t v_res_2879_; lean_object* v_r_2880_; 
v_res_2879_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2878_);
lean_dec_ref(v_e_2878_);
v_r_2880_ = lean_box(v_res_2879_);
return v_r_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2881_, size_t v_i_2882_, lean_object* v_bs_2883_){
_start:
{
uint8_t v___x_2884_; 
v___x_2884_ = lean_usize_dec_lt(v_i_2882_, v_sz_2881_);
if (v___x_2884_ == 0)
{
return v_bs_2883_;
}
else
{
lean_object* v_v_2885_; lean_object* v_msg_2886_; lean_object* v___x_2887_; lean_object* v_bs_x27_2888_; size_t v___x_2889_; size_t v___x_2890_; lean_object* v___x_2891_; 
v_v_2885_ = lean_array_uget_borrowed(v_bs_2883_, v_i_2882_);
v_msg_2886_ = lean_ctor_get(v_v_2885_, 1);
lean_inc_ref(v_msg_2886_);
v___x_2887_ = lean_unsigned_to_nat(0u);
v_bs_x27_2888_ = lean_array_uset(v_bs_2883_, v_i_2882_, v___x_2887_);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_add(v_i_2882_, v___x_2889_);
v___x_2891_ = lean_array_uset(v_bs_x27_2888_, v_i_2882_, v_msg_2886_);
v_i_2882_ = v___x_2890_;
v_bs_2883_ = v___x_2891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2893_, lean_object* v_i_2894_, lean_object* v_bs_2895_){
_start:
{
size_t v_sz_boxed_2896_; size_t v_i_boxed_2897_; lean_object* v_res_2898_; 
v_sz_boxed_2896_ = lean_unbox_usize(v_sz_2893_);
lean_dec(v_sz_2893_);
v_i_boxed_2897_ = lean_unbox_usize(v_i_2894_);
lean_dec(v_i_2894_);
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2896_, v_i_boxed_2897_, v_bs_2895_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2899_, lean_object* v_data_2900_, lean_object* v_ref_2901_, lean_object* v_msg_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_toCold_2906_; lean_object* v_currRecDepth_2907_; lean_object* v_ref_2908_; uint16_t v_optionFlags_2909_; uint8_t v_suppressElabErrors_2910_; uint8_t v_checkDeprecated_2911_; uint8_t v_isRecordingDeps_2912_; lean_object* v_ref_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v_traceState_2916_; lean_object* v_traces_2917_; lean_object* v___x_2918_; size_t v_sz_2919_; size_t v___x_2920_; lean_object* v___x_2921_; lean_object* v_msg_2922_; lean_object* v___x_2923_; lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2962_; 
v_toCold_2906_ = lean_ctor_get(v___y_2903_, 0);
v_currRecDepth_2907_ = lean_ctor_get(v___y_2903_, 1);
v_ref_2908_ = lean_ctor_get(v___y_2903_, 2);
v_optionFlags_2909_ = lean_ctor_get_uint16(v___y_2903_, sizeof(void*)*3);
v_suppressElabErrors_2910_ = lean_ctor_get_uint8(v___y_2903_, sizeof(void*)*3 + 2);
v_checkDeprecated_2911_ = lean_ctor_get_uint8(v___y_2903_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2912_ = lean_ctor_get_uint8(v___y_2903_, sizeof(void*)*3 + 4);
v_ref_2913_ = l_Lean_replaceRef(v_ref_2901_, v_ref_2908_);
lean_inc(v_currRecDepth_2907_);
lean_inc_ref(v_toCold_2906_);
v___x_2914_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2914_, 0, v_toCold_2906_);
lean_ctor_set(v___x_2914_, 1, v_currRecDepth_2907_);
lean_ctor_set(v___x_2914_, 2, v_ref_2913_);
lean_ctor_set_uint16(v___x_2914_, sizeof(void*)*3, v_optionFlags_2909_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*3 + 2, v_suppressElabErrors_2910_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*3 + 3, v_checkDeprecated_2911_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*3 + 4, v_isRecordingDeps_2912_);
v___x_2915_ = lean_st_ref_get(v___y_2904_);
v_traceState_2916_ = lean_ctor_get(v___x_2915_, 4);
lean_inc_ref(v_traceState_2916_);
lean_dec(v___x_2915_);
v_traces_2917_ = lean_ctor_get(v_traceState_2916_, 0);
lean_inc_ref(v_traces_2917_);
lean_dec_ref(v_traceState_2916_);
v___x_2918_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2917_);
lean_dec_ref(v_traces_2917_);
v_sz_2919_ = lean_array_size(v___x_2918_);
v___x_2920_ = ((size_t)0ULL);
v___x_2921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2919_, v___x_2920_, v___x_2918_);
v_msg_2922_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2922_, 0, v_data_2900_);
lean_ctor_set(v_msg_2922_, 1, v_msg_2902_);
lean_ctor_set(v_msg_2922_, 2, v___x_2921_);
v___x_2923_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2922_, v___x_2914_, v___y_2904_);
lean_dec_ref_known(v___x_2914_, 3);
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2962_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2962_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v_traceState_2929_; lean_object* v_env_2930_; lean_object* v_nextMacroScope_2931_; lean_object* v_ngen_2932_; lean_object* v_auxDeclNGen_2933_; lean_object* v_cache_2934_; lean_object* v_recordedDeps_2935_; lean_object* v_messages_2936_; lean_object* v_infoState_2937_; lean_object* v_snapshotTasks_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2961_; 
v___x_2928_ = lean_st_ref_take(v___y_2904_);
v_traceState_2929_ = lean_ctor_get(v___x_2928_, 4);
v_env_2930_ = lean_ctor_get(v___x_2928_, 0);
v_nextMacroScope_2931_ = lean_ctor_get(v___x_2928_, 1);
v_ngen_2932_ = lean_ctor_get(v___x_2928_, 2);
v_auxDeclNGen_2933_ = lean_ctor_get(v___x_2928_, 3);
v_cache_2934_ = lean_ctor_get(v___x_2928_, 5);
v_recordedDeps_2935_ = lean_ctor_get(v___x_2928_, 6);
v_messages_2936_ = lean_ctor_get(v___x_2928_, 7);
v_infoState_2937_ = lean_ctor_get(v___x_2928_, 8);
v_snapshotTasks_2938_ = lean_ctor_get(v___x_2928_, 9);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2940_ = v___x_2928_;
v_isShared_2941_ = v_isSharedCheck_2961_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_snapshotTasks_2938_);
lean_inc(v_infoState_2937_);
lean_inc(v_messages_2936_);
lean_inc(v_recordedDeps_2935_);
lean_inc(v_cache_2934_);
lean_inc(v_traceState_2929_);
lean_inc(v_auxDeclNGen_2933_);
lean_inc(v_ngen_2932_);
lean_inc(v_nextMacroScope_2931_);
lean_inc(v_env_2930_);
lean_dec(v___x_2928_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2961_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
uint64_t v_tid_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2959_; 
v_tid_2942_ = lean_ctor_get_uint64(v_traceState_2929_, sizeof(void*)*1);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_traceState_2929_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v_traceState_2929_, 0);
lean_dec(v_unused_2960_);
v___x_2944_ = v_traceState_2929_;
v_isShared_2945_ = v_isSharedCheck_2959_;
goto v_resetjp_2943_;
}
else
{
lean_dec(v_traceState_2929_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2959_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v_ref_2901_);
lean_ctor_set(v___x_2947_, 1, v_a_2924_);
v___x_2948_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2899_, v___x_2947_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2948_);
v___x_2950_ = v___x_2944_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2948_);
lean_ctor_set_uint64(v_reuseFailAlloc_2958_, sizeof(void*)*1, v_tid_2942_);
v___x_2950_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2952_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_2950_);
v___x_2952_ = v___x_2940_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_env_2930_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_nextMacroScope_2931_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_ngen_2932_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_auxDeclNGen_2933_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2957_, 5, v_cache_2934_);
lean_ctor_set(v_reuseFailAlloc_2957_, 6, v_recordedDeps_2935_);
lean_ctor_set(v_reuseFailAlloc_2957_, 7, v_messages_2936_);
lean_ctor_set(v_reuseFailAlloc_2957_, 8, v_infoState_2937_);
lean_ctor_set(v_reuseFailAlloc_2957_, 9, v_snapshotTasks_2938_);
v___x_2952_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2953_ = lean_st_ref_put(v___y_2904_, v___x_2952_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2946_);
v___x_2955_ = v___x_2926_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2946_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2963_, lean_object* v_data_2964_, lean_object* v_ref_2965_, lean_object* v_msg_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2963_, v_data_2964_, v_ref_2965_, v_msg_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2970_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2973_ = l_Lean_stringToMessageData(v___x_2972_);
return v___x_2973_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2974_; double v___x_2975_; 
v___x_2974_ = lean_unsigned_to_nat(1000u);
v___x_2975_ = lean_float_of_nat(v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2976_, uint8_t v_collapsed_2977_, lean_object* v_tag_2978_, lean_object* v_opts_2979_, uint8_t v_clsEnabled_2980_, lean_object* v_oldTraces_2981_, lean_object* v_msg_2982_, lean_object* v_resStartStop_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_fst_2987_; lean_object* v_snd_2988_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v_data_2992_; lean_object* v_fst_3003_; lean_object* v_snd_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; lean_object* v___y_3008_; lean_object* v_a_3009_; uint8_t v___y_3024_; double v___y_3056_; 
v_fst_2987_ = lean_ctor_get(v_resStartStop_2983_, 0);
lean_inc(v_fst_2987_);
v_snd_2988_ = lean_ctor_get(v_resStartStop_2983_, 1);
lean_inc(v_snd_2988_);
lean_dec_ref(v_resStartStop_2983_);
v_fst_3003_ = lean_ctor_get(v_snd_2988_, 0);
lean_inc(v_fst_3003_);
v_snd_3004_ = lean_ctor_get(v_snd_2988_, 1);
lean_inc(v_snd_3004_);
lean_dec(v_snd_2988_);
v___x_3005_ = l_Lean_trace_profiler;
v___x_3006_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2979_, v___x_3005_);
if (v___x_3006_ == 0)
{
v___y_3024_ = v___x_3006_;
goto v___jp_3023_;
}
else
{
lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3061_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3062_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2979_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; double v___x_3065_; double v___x_3066_; double v___x_3067_; 
v___x_3063_ = l_Lean_trace_profiler_threshold;
v___x_3064_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2979_, v___x_3063_);
v___x_3065_ = lean_float_of_nat(v___x_3064_);
v___x_3066_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3067_ = lean_float_div(v___x_3065_, v___x_3066_);
v___y_3056_ = v___x_3067_;
goto v___jp_3055_;
}
else
{
lean_object* v___x_3068_; lean_object* v___x_3069_; double v___x_3070_; 
v___x_3068_ = l_Lean_trace_profiler_threshold;
v___x_3069_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2979_, v___x_3068_);
v___x_3070_ = lean_float_of_nat(v___x_3069_);
v___y_3056_ = v___x_3070_;
goto v___jp_3055_;
}
}
v___jp_2989_:
{
lean_object* v___x_2993_; 
lean_inc(v___y_2990_);
v___x_2993_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2981_, v_data_2992_, v___y_2990_, v___y_2991_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v___x_2994_; 
lean_dec_ref_known(v___x_2993_, 1);
v___x_2994_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2987_);
return v___x_2994_;
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_fst_2987_);
v_a_2995_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2993_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2993_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
v___jp_3007_:
{
uint8_t v_result_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; double v___x_3013_; lean_object* v_data_3014_; 
v_result_3010_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2987_);
v___x_3011_ = lean_box(v_result_3010_);
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
v___x_3013_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__0);
lean_inc_ref(v_tag_2978_);
lean_inc_ref(v___x_3012_);
lean_inc(v_cls_2976_);
v_data_3014_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3014_, 0, v_cls_2976_);
lean_ctor_set(v_data_3014_, 1, v___x_3012_);
lean_ctor_set(v_data_3014_, 2, v_tag_2978_);
lean_ctor_set_float(v_data_3014_, sizeof(void*)*3, v___x_3013_);
lean_ctor_set_float(v_data_3014_, sizeof(void*)*3 + 8, v___x_3013_);
lean_ctor_set_uint8(v_data_3014_, sizeof(void*)*3 + 16, v_collapsed_2977_);
if (v___x_3006_ == 0)
{
lean_dec_ref_known(v___x_3012_, 1);
lean_dec(v_snd_3004_);
lean_dec(v_fst_3003_);
lean_dec_ref(v_tag_2978_);
lean_dec(v_cls_2976_);
v___y_2990_ = v___y_3008_;
v___y_2991_ = v_a_3009_;
v_data_2992_ = v_data_3014_;
goto v___jp_2989_;
}
else
{
lean_object* v_data_3015_; double v___x_3016_; double v___x_3017_; 
lean_dec_ref_known(v_data_3014_, 3);
v_data_3015_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3015_, 0, v_cls_2976_);
lean_ctor_set(v_data_3015_, 1, v___x_3012_);
lean_ctor_set(v_data_3015_, 2, v_tag_2978_);
v___x_3016_ = lean_unbox_float(v_fst_3003_);
lean_dec(v_fst_3003_);
lean_ctor_set_float(v_data_3015_, sizeof(void*)*3, v___x_3016_);
v___x_3017_ = lean_unbox_float(v_snd_3004_);
lean_dec(v_snd_3004_);
lean_ctor_set_float(v_data_3015_, sizeof(void*)*3 + 8, v___x_3017_);
lean_ctor_set_uint8(v_data_3015_, sizeof(void*)*3 + 16, v_collapsed_2977_);
v___y_2990_ = v___y_3008_;
v___y_2991_ = v_a_3009_;
v_data_2992_ = v_data_3015_;
goto v___jp_2989_;
}
}
v___jp_3018_:
{
lean_object* v_ref_3019_; lean_object* v___x_3020_; 
v_ref_3019_ = lean_ctor_get(v___y_2984_, 2);
lean_inc(v___y_2985_);
lean_inc_ref(v___y_2984_);
lean_inc(v_fst_2987_);
v___x_3020_ = lean_apply_4(v_msg_2982_, v_fst_2987_, v___y_2984_, v___y_2985_, lean_box(0));
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___y_3008_ = v_ref_3019_;
v_a_3009_ = v_a_3021_;
goto v___jp_3007_;
}
else
{
lean_object* v___x_3022_; 
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_3008_ = v_ref_3019_;
v_a_3009_ = v___x_3022_;
goto v___jp_3007_;
}
}
v___jp_3023_:
{
if (v_clsEnabled_2980_ == 0)
{
if (v___y_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v_traceState_3026_; lean_object* v_env_3027_; lean_object* v_nextMacroScope_3028_; lean_object* v_ngen_3029_; lean_object* v_auxDeclNGen_3030_; lean_object* v_cache_3031_; lean_object* v_recordedDeps_3032_; lean_object* v_messages_3033_; lean_object* v_infoState_3034_; lean_object* v_snapshotTasks_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v_snd_3004_);
lean_dec(v_fst_3003_);
lean_dec_ref(v_msg_2982_);
lean_dec_ref(v_tag_2978_);
lean_dec(v_cls_2976_);
v___x_3025_ = lean_st_ref_take(v___y_2985_);
v_traceState_3026_ = lean_ctor_get(v___x_3025_, 4);
v_env_3027_ = lean_ctor_get(v___x_3025_, 0);
v_nextMacroScope_3028_ = lean_ctor_get(v___x_3025_, 1);
v_ngen_3029_ = lean_ctor_get(v___x_3025_, 2);
v_auxDeclNGen_3030_ = lean_ctor_get(v___x_3025_, 3);
v_cache_3031_ = lean_ctor_get(v___x_3025_, 5);
v_recordedDeps_3032_ = lean_ctor_get(v___x_3025_, 6);
v_messages_3033_ = lean_ctor_get(v___x_3025_, 7);
v_infoState_3034_ = lean_ctor_get(v___x_3025_, 8);
v_snapshotTasks_3035_ = lean_ctor_get(v___x_3025_, 9);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3037_ = v___x_3025_;
v_isShared_3038_ = v_isSharedCheck_3054_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_snapshotTasks_3035_);
lean_inc(v_infoState_3034_);
lean_inc(v_messages_3033_);
lean_inc(v_recordedDeps_3032_);
lean_inc(v_cache_3031_);
lean_inc(v_traceState_3026_);
lean_inc(v_auxDeclNGen_3030_);
lean_inc(v_ngen_3029_);
lean_inc(v_nextMacroScope_3028_);
lean_inc(v_env_3027_);
lean_dec(v___x_3025_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3054_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
uint64_t v_tid_3039_; lean_object* v_traces_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3053_; 
v_tid_3039_ = lean_ctor_get_uint64(v_traceState_3026_, sizeof(void*)*1);
v_traces_3040_ = lean_ctor_get(v_traceState_3026_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_traceState_3026_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3042_ = v_traceState_3026_;
v_isShared_3043_ = v_isSharedCheck_3053_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_traces_3040_);
lean_dec(v_traceState_3026_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3053_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3044_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2981_, v_traces_3040_);
lean_dec_ref(v_traces_3040_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3044_);
v___x_3046_ = v___x_3042_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3044_);
lean_ctor_set_uint64(v_reuseFailAlloc_3052_, sizeof(void*)*1, v_tid_3039_);
v___x_3046_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3048_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 4, v___x_3046_);
v___x_3048_ = v___x_3037_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_env_3027_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_nextMacroScope_3028_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_ngen_3029_);
lean_ctor_set(v_reuseFailAlloc_3051_, 3, v_auxDeclNGen_3030_);
lean_ctor_set(v_reuseFailAlloc_3051_, 4, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3051_, 5, v_cache_3031_);
lean_ctor_set(v_reuseFailAlloc_3051_, 6, v_recordedDeps_3032_);
lean_ctor_set(v_reuseFailAlloc_3051_, 7, v_messages_3033_);
lean_ctor_set(v_reuseFailAlloc_3051_, 8, v_infoState_3034_);
lean_ctor_set(v_reuseFailAlloc_3051_, 9, v_snapshotTasks_3035_);
v___x_3048_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = lean_st_ref_put(v___y_2985_, v___x_3048_);
v___x_3050_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2987_);
return v___x_3050_;
}
}
}
}
}
else
{
goto v___jp_3018_;
}
}
else
{
goto v___jp_3018_;
}
}
v___jp_3055_:
{
double v___x_3057_; double v___x_3058_; double v___x_3059_; uint8_t v___x_3060_; 
v___x_3057_ = lean_unbox_float(v_snd_3004_);
v___x_3058_ = lean_unbox_float(v_fst_3003_);
v___x_3059_ = lean_float_sub(v___x_3057_, v___x_3058_);
v___x_3060_ = lean_float_decLt(v___y_3056_, v___x_3059_);
v___y_3024_ = v___x_3060_;
goto v___jp_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3071_, lean_object* v_collapsed_3072_, lean_object* v_tag_3073_, lean_object* v_opts_3074_, lean_object* v_clsEnabled_3075_, lean_object* v_oldTraces_3076_, lean_object* v_msg_3077_, lean_object* v_resStartStop_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
uint8_t v_collapsed_boxed_3082_; uint8_t v_clsEnabled_boxed_3083_; lean_object* v_res_3084_; 
v_collapsed_boxed_3082_ = lean_unbox(v_collapsed_3072_);
v_clsEnabled_boxed_3083_ = lean_unbox(v_clsEnabled_3075_);
v_res_3084_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3071_, v_collapsed_boxed_3082_, v_tag_3073_, v_opts_3074_, v_clsEnabled_boxed_3083_, v_oldTraces_3076_, v_msg_3077_, v_resStartStop_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec_ref(v_opts_3074_);
return v_res_3084_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3087_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3088_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
lean_ctor_set(v___x_3090_, 2, v___x_3089_);
lean_ctor_set(v___x_3090_, 3, v___x_3089_);
lean_ctor_set(v___x_3090_, 4, v___x_3088_);
lean_ctor_set(v___x_3090_, 5, v___x_3088_);
lean_ctor_set(v___x_3090_, 6, v___x_3088_);
lean_ctor_set(v___x_3090_, 7, v___x_3088_);
lean_ctor_set(v___x_3090_, 8, v___x_3088_);
lean_ctor_set(v___x_3090_, 9, v___x_3088_);
lean_ctor_set(v___x_3090_, 10, v___x_3088_);
lean_ctor_set(v___x_3090_, 11, v___x_3087_);
return v___x_3090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3092_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
v___x_3093_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3091_);
lean_ctor_set(v___x_3093_, 2, v___x_3091_);
lean_ctor_set(v___x_3093_, 3, v___x_3091_);
lean_ctor_set(v___x_3093_, 4, v___x_3091_);
lean_ctor_set(v___x_3093_, 5, v___x_3091_);
lean_ctor_set(v___x_3093_, 6, v___x_3091_);
return v___x_3093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
lean_ctor_set(v___x_3095_, 2, v___x_3094_);
lean_ctor_set(v___x_3095_, 3, v___x_3094_);
lean_ctor_set(v___x_3095_, 4, v___x_3094_);
return v___x_3095_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3101_ = l_Lean_Name_append(v___x_3100_, v___x_3099_);
return v___x_3101_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3102_; double v___x_3103_; 
v___x_3102_ = lean_unsigned_to_nat(1000000000u);
v___x_3103_ = lean_float_of_nat(v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3104_, lean_object* v___f_3105_, lean_object* v_name_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_toCold_3110_; lean_object* v_options_3111_; uint8_t v_hasTrace_3112_; 
v_toCold_3110_ = lean_ctor_get(v___y_3107_, 0);
v_options_3111_ = lean_ctor_get(v_toCold_3110_, 2);
v_hasTrace_3112_ = lean_ctor_get_uint8(v_options_3111_, sizeof(void*)*1);
if (v_hasTrace_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v_env_3114_; lean_object* v___x_3115_; 
lean_dec_ref(v___f_3105_);
v___x_3113_ = lean_st_ref_get(v___y_3108_);
v_env_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc_ref(v_env_3114_);
lean_dec(v___x_3113_);
lean_inc(v_name_3106_);
v___x_3115_ = l_Lean_Meta_declFromEqLikeName(v_env_3114_, v_name_3106_);
if (lean_obj_tag(v___x_3115_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3217_; 
v_val_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3217_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_val_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3217_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_fst_3120_; lean_object* v_snd_3121_; lean_object* v___x_3122_; lean_object* v_env_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v_fst_3120_ = lean_ctor_get(v_val_3116_, 0);
lean_inc_n(v_fst_3120_, 2);
v_snd_3121_ = lean_ctor_get(v_val_3116_, 1);
lean_inc_n(v_snd_3121_, 2);
lean_dec(v_val_3116_);
v___x_3122_ = lean_st_ref_get(v___y_3108_);
v_env_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc_ref(v_env_3123_);
lean_dec(v___x_3122_);
v___x_3124_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3123_, v_fst_3120_, v_snd_3121_);
v___x_3125_ = lean_name_eq(v_name_3106_, v___x_3124_);
lean_dec(v___x_3124_);
lean_dec(v_name_3106_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
lean_dec(v_snd_3121_);
lean_dec(v_fst_3120_);
lean_dec(v___x_3104_);
v___x_3126_ = lean_box(v_hasTrace_3112_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3126_);
v___x_3128_ = v___x_3118_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
else
{
uint8_t v___x_3130_; 
lean_inc(v_snd_3121_);
v___x_3130_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3121_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3131_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3132_ = lean_string_dec_eq(v_snd_3121_, v___x_3131_);
lean_dec(v_snd_3121_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3135_; 
lean_dec(v_fst_3120_);
lean_dec(v___x_3104_);
v___x_3133_ = lean_box(v_hasTrace_3112_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3133_);
v___x_3135_ = v___x_3118_;
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
else
{
uint8_t v___x_3137_; uint8_t v___x_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; uint64_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_del_object(v___x_3118_);
v___x_3137_ = 1;
v___x_3138_ = 0;
v___x_3139_ = 2;
v___x_3140_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3140_, 0, v___x_3130_);
lean_ctor_set_uint8(v___x_3140_, 1, v___x_3130_);
lean_ctor_set_uint8(v___x_3140_, 2, v___x_3130_);
lean_ctor_set_uint8(v___x_3140_, 3, v___x_3130_);
lean_ctor_set_uint8(v___x_3140_, 4, v___x_3130_);
lean_ctor_set_uint8(v___x_3140_, 5, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 6, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 7, v___x_3130_);
lean_ctor_set_uint8(v___x_3140_, 8, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 9, v___x_3137_);
lean_ctor_set_uint8(v___x_3140_, 10, v___x_3138_);
lean_ctor_set_uint8(v___x_3140_, 11, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 12, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 13, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 14, v___x_3139_);
lean_ctor_set_uint8(v___x_3140_, 15, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 16, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 17, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 18, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 19, v___x_3130_);
v___x_3141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set_uint64(v___x_3142_, sizeof(void*)*1, v___x_3141_);
v___x_3143_ = lean_unsigned_to_nat(0u);
v___x_3144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3145_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3146_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3147_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3148_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3148_, 0, v___x_3142_);
lean_ctor_set(v___x_3148_, 1, v___x_3104_);
lean_ctor_set(v___x_3148_, 2, v___x_3145_);
lean_ctor_set(v___x_3148_, 3, v___x_3146_);
lean_ctor_set(v___x_3148_, 4, v___x_3147_);
lean_ctor_set(v___x_3148_, 5, v___x_3143_);
lean_ctor_set(v___x_3148_, 6, v___x_3147_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7, v___x_3130_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7 + 1, v___x_3130_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7 + 2, v___x_3130_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7 + 3, v___x_3125_);
v___x_3149_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3150_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3151_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3149_);
lean_ctor_set(v___x_3152_, 1, v___x_3150_);
lean_ctor_set(v___x_3152_, 2, v___x_3104_);
lean_ctor_set(v___x_3152_, 3, v___x_3144_);
lean_ctor_set(v___x_3152_, 4, v___x_3151_);
v___x_3153_ = lean_st_mk_ref(v___x_3152_);
v___x_3154_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3120_, v___x_3125_, v___x_3148_, v___x_3153_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3148_, 7);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3168_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3168_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3168_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_st_ref_get(v___x_3153_);
lean_dec(v___x_3153_);
lean_dec(v___x_3159_);
if (lean_obj_tag(v_a_3155_) == 0)
{
lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3160_ = lean_box(v___x_3130_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3160_);
v___x_3162_ = v___x_3157_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
lean_dec_ref_known(v_a_3155_, 1);
v___x_3164_ = lean_box(v___x_3132_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3164_);
v___x_3166_ = v___x_3157_;
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
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v___x_3153_);
v_a_3169_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3154_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3154_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
else
{
uint8_t v___x_3177_; uint8_t v___x_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; uint64_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_dec(v_snd_3121_);
lean_del_object(v___x_3118_);
v___x_3177_ = 1;
v___x_3178_ = 0;
v___x_3179_ = 2;
v___x_3180_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3180_, 0, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3180_, 1, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3180_, 2, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3180_, 3, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3180_, 4, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3180_, 5, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 6, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 7, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3180_, 8, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 9, v___x_3177_);
lean_ctor_set_uint8(v___x_3180_, 10, v___x_3178_);
lean_ctor_set_uint8(v___x_3180_, 11, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 12, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 13, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 14, v___x_3179_);
lean_ctor_set_uint8(v___x_3180_, 15, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 16, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 17, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 18, v___x_3130_);
lean_ctor_set_uint8(v___x_3180_, 19, v_hasTrace_3112_);
v___x_3181_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3180_);
v___x_3182_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3182_, 0, v___x_3180_);
lean_ctor_set_uint64(v___x_3182_, sizeof(void*)*1, v___x_3181_);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3185_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3186_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3187_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3188_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3188_, 0, v___x_3182_);
lean_ctor_set(v___x_3188_, 1, v___x_3104_);
lean_ctor_set(v___x_3188_, 2, v___x_3185_);
lean_ctor_set(v___x_3188_, 3, v___x_3186_);
lean_ctor_set(v___x_3188_, 4, v___x_3187_);
lean_ctor_set(v___x_3188_, 5, v___x_3183_);
lean_ctor_set(v___x_3188_, 6, v___x_3187_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*7, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*7 + 1, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*7 + 2, v_hasTrace_3112_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*7 + 3, v___x_3125_);
v___x_3189_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3190_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3191_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3189_);
lean_ctor_set(v___x_3192_, 1, v___x_3190_);
lean_ctor_set(v___x_3192_, 2, v___x_3104_);
lean_ctor_set(v___x_3192_, 3, v___x_3184_);
lean_ctor_set(v___x_3192_, 4, v___x_3191_);
v___x_3193_ = lean_st_mk_ref(v___x_3192_);
v___x_3194_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3120_, v___x_3188_, v___x_3193_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3188_, 7);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3208_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; 
v___x_3199_ = lean_st_ref_get(v___x_3193_);
lean_dec(v___x_3193_);
lean_dec(v___x_3199_);
if (lean_obj_tag(v_a_3195_) == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3200_ = lean_box(v_hasTrace_3112_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3200_);
v___x_3202_ = v___x_3197_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
lean_dec_ref_known(v_a_3195_, 1);
v___x_3204_ = lean_box(v___x_3130_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3204_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec(v___x_3193_);
v_a_3209_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3194_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3194_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec(v___x_3115_);
lean_dec(v_name_3106_);
lean_dec(v___x_3104_);
v___x_3218_ = lean_box(v_hasTrace_3112_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v_a_3229_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v_a_3244_; lean_object* v___y_3247_; lean_object* v___y_3248_; uint8_t v_a_3249_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v_a_3255_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v_a_3267_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint8_t v_a_3272_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; 
v_inheritedTraceOptions_3220_ = lean_ctor_get(v_toCold_3110_, 11);
lean_inc(v_name_3106_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3221_, 0, v_name_3106_);
v___x_3222_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3223_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__3___closed__1));
v___x_3224_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3225_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3220_, v_options_3111_, v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = l_Lean_trace_profiler;
v___x_3407_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3111_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v_env_3409_; lean_object* v___x_3410_; 
lean_dec_ref(v___f_3221_);
lean_dec_ref(v___f_3105_);
v___x_3408_ = lean_st_ref_get(v___y_3108_);
v_env_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc_ref(v_env_3409_);
lean_dec(v___x_3408_);
lean_inc(v_name_3106_);
v___x_3410_ = l_Lean_Meta_declFromEqLikeName(v_env_3409_, v_name_3106_);
if (lean_obj_tag(v___x_3410_) == 1)
{
lean_object* v_val_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3512_; 
v_val_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3512_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_val_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3512_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v_fst_3415_; lean_object* v_snd_3416_; lean_object* v___x_3417_; lean_object* v_env_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v_fst_3415_ = lean_ctor_get(v_val_3411_, 0);
lean_inc_n(v_fst_3415_, 2);
v_snd_3416_ = lean_ctor_get(v_val_3411_, 1);
lean_inc_n(v_snd_3416_, 2);
lean_dec(v_val_3411_);
v___x_3417_ = lean_st_ref_get(v___y_3108_);
v_env_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc_ref(v_env_3418_);
lean_dec(v___x_3417_);
v___x_3419_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3418_, v_fst_3415_, v_snd_3416_);
v___x_3420_ = lean_name_eq(v_name_3106_, v___x_3419_);
lean_dec(v___x_3419_);
lean_dec(v_name_3106_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
lean_dec(v_snd_3416_);
lean_dec(v_fst_3415_);
lean_dec(v___x_3104_);
v___x_3421_ = lean_box(v___x_3407_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3421_);
v___x_3423_ = v___x_3413_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
else
{
uint8_t v___x_3425_; 
lean_inc(v_snd_3416_);
v___x_3425_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3416_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3427_ = lean_string_dec_eq(v_snd_3416_, v___x_3426_);
lean_dec(v_snd_3416_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_dec(v_fst_3415_);
lean_dec(v___x_3104_);
v___x_3428_ = lean_box(v___x_3407_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3428_);
v___x_3430_ = v___x_3413_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
else
{
uint8_t v___x_3432_; uint8_t v___x_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; uint64_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_del_object(v___x_3413_);
v___x_3432_ = 1;
v___x_3433_ = 0;
v___x_3434_ = 2;
v___x_3435_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3435_, 0, v___x_3425_);
lean_ctor_set_uint8(v___x_3435_, 1, v___x_3425_);
lean_ctor_set_uint8(v___x_3435_, 2, v___x_3425_);
lean_ctor_set_uint8(v___x_3435_, 3, v___x_3425_);
lean_ctor_set_uint8(v___x_3435_, 4, v___x_3425_);
lean_ctor_set_uint8(v___x_3435_, 5, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 6, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 7, v___x_3425_);
lean_ctor_set_uint8(v___x_3435_, 8, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 9, v___x_3432_);
lean_ctor_set_uint8(v___x_3435_, 10, v___x_3433_);
lean_ctor_set_uint8(v___x_3435_, 11, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 12, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 13, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 14, v___x_3434_);
lean_ctor_set_uint8(v___x_3435_, 15, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 16, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 17, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 18, v___x_3427_);
lean_ctor_set_uint8(v___x_3435_, 19, v___x_3425_);
v___x_3436_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3435_);
v___x_3437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set_uint64(v___x_3437_, sizeof(void*)*1, v___x_3436_);
v___x_3438_ = lean_unsigned_to_nat(0u);
v___x_3439_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3440_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3442_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3443_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3443_, 0, v___x_3437_);
lean_ctor_set(v___x_3443_, 1, v___x_3104_);
lean_ctor_set(v___x_3443_, 2, v___x_3440_);
lean_ctor_set(v___x_3443_, 3, v___x_3441_);
lean_ctor_set(v___x_3443_, 4, v___x_3442_);
lean_ctor_set(v___x_3443_, 5, v___x_3438_);
lean_ctor_set(v___x_3443_, 6, v___x_3442_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7, v___x_3425_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7 + 1, v___x_3425_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7 + 2, v___x_3425_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7 + 3, v_hasTrace_3112_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3446_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3444_);
lean_ctor_set(v___x_3447_, 1, v___x_3445_);
lean_ctor_set(v___x_3447_, 2, v___x_3104_);
lean_ctor_set(v___x_3447_, 3, v___x_3439_);
lean_ctor_set(v___x_3447_, 4, v___x_3446_);
v___x_3448_ = lean_st_mk_ref(v___x_3447_);
v___x_3449_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3415_, v_hasTrace_3112_, v___x_3443_, v___x_3448_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3443_, 7);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3463_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_st_ref_get(v___x_3448_);
lean_dec(v___x_3448_);
lean_dec(v___x_3454_);
if (lean_obj_tag(v_a_3450_) == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3455_ = lean_box(v___x_3425_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3455_);
v___x_3457_ = v___x_3452_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
lean_dec_ref_known(v_a_3450_, 1);
v___x_3459_ = lean_box(v___x_3427_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3459_);
v___x_3461_ = v___x_3452_;
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
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v___x_3448_);
v_a_3464_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3449_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3449_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
else
{
uint8_t v___x_3472_; uint8_t v___x_3473_; uint8_t v___x_3474_; lean_object* v___x_3475_; uint64_t v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec(v_snd_3416_);
lean_del_object(v___x_3413_);
v___x_3472_ = 1;
v___x_3473_ = 0;
v___x_3474_ = 2;
v___x_3475_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3475_, 0, v___x_3407_);
lean_ctor_set_uint8(v___x_3475_, 1, v___x_3407_);
lean_ctor_set_uint8(v___x_3475_, 2, v___x_3407_);
lean_ctor_set_uint8(v___x_3475_, 3, v___x_3407_);
lean_ctor_set_uint8(v___x_3475_, 4, v___x_3407_);
lean_ctor_set_uint8(v___x_3475_, 5, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 6, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 7, v___x_3407_);
lean_ctor_set_uint8(v___x_3475_, 8, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 9, v___x_3472_);
lean_ctor_set_uint8(v___x_3475_, 10, v___x_3473_);
lean_ctor_set_uint8(v___x_3475_, 11, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 12, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 13, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 14, v___x_3474_);
lean_ctor_set_uint8(v___x_3475_, 15, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 16, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 17, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 18, v___x_3425_);
lean_ctor_set_uint8(v___x_3475_, 19, v___x_3407_);
v___x_3476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3475_);
v___x_3477_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set_uint64(v___x_3477_, sizeof(void*)*1, v___x_3476_);
v___x_3478_ = lean_unsigned_to_nat(0u);
v___x_3479_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3480_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3481_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3482_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3483_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3483_, 0, v___x_3477_);
lean_ctor_set(v___x_3483_, 1, v___x_3104_);
lean_ctor_set(v___x_3483_, 2, v___x_3480_);
lean_ctor_set(v___x_3483_, 3, v___x_3481_);
lean_ctor_set(v___x_3483_, 4, v___x_3482_);
lean_ctor_set(v___x_3483_, 5, v___x_3478_);
lean_ctor_set(v___x_3483_, 6, v___x_3482_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7, v___x_3407_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 1, v___x_3407_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 2, v___x_3407_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 3, v_hasTrace_3112_);
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3485_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3486_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3484_);
lean_ctor_set(v___x_3487_, 1, v___x_3485_);
lean_ctor_set(v___x_3487_, 2, v___x_3104_);
lean_ctor_set(v___x_3487_, 3, v___x_3479_);
lean_ctor_set(v___x_3487_, 4, v___x_3486_);
v___x_3488_ = lean_st_mk_ref(v___x_3487_);
v___x_3489_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3415_, v___x_3483_, v___x_3488_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3483_, 7);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3503_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3503_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3503_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; 
v___x_3494_ = lean_st_ref_get(v___x_3488_);
lean_dec(v___x_3488_);
lean_dec(v___x_3494_);
if (lean_obj_tag(v_a_3490_) == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = lean_box(v___x_3407_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3495_);
v___x_3497_ = v___x_3492_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_dec_ref_known(v_a_3490_, 1);
v___x_3499_ = lean_box(v___x_3425_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3499_);
v___x_3501_ = v___x_3492_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec(v___x_3488_);
v_a_3504_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3489_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3489_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_dec(v___x_3410_);
lean_dec(v_name_3106_);
lean_dec(v___x_3104_);
v___x_3513_ = lean_box(v___x_3407_);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
return v___x_3514_;
}
}
else
{
goto v___jp_3282_;
}
}
else
{
goto v___jp_3282_;
}
v___jp_3226_:
{
lean_object* v___x_3230_; double v___x_3231_; double v___x_3232_; double v___x_3233_; double v___x_3234_; double v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3230_ = lean_io_mono_nanos_now();
v___x_3231_ = lean_float_of_nat(v___y_3228_);
v___x_3232_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3233_ = lean_float_div(v___x_3231_, v___x_3232_);
v___x_3234_ = lean_float_of_nat(v___x_3230_);
v___x_3235_ = lean_float_div(v___x_3234_, v___x_3232_);
v___x_3236_ = lean_box_float(v___x_3233_);
v___x_3237_ = lean_box_float(v___x_3235_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3239_, 0, v_a_3229_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3222_, v_hasTrace_3112_, v___x_3223_, v_options_3111_, v___x_3225_, v___y_3227_, v___f_3221_, v___x_3239_, v___y_3107_, v___y_3108_);
return v___x_3240_;
}
v___jp_3241_:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_a_3244_);
v___y_3227_ = v___y_3242_;
v___y_3228_ = v___y_3243_;
v_a_3229_ = v___x_3245_;
goto v___jp_3226_;
}
v___jp_3246_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_box(v_a_3249_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
v___y_3227_ = v___y_3247_;
v___y_3228_ = v___y_3248_;
v_a_3229_ = v___x_3251_;
goto v___jp_3226_;
}
v___jp_3252_:
{
lean_object* v___x_3256_; double v___x_3257_; double v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3256_ = lean_io_get_num_heartbeats();
v___x_3257_ = lean_float_of_nat(v___y_3254_);
v___x_3258_ = lean_float_of_nat(v___x_3256_);
v___x_3259_ = lean_box_float(v___x_3257_);
v___x_3260_ = lean_box_float(v___x_3258_);
v___x_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3259_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v_a_3255_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3222_, v_hasTrace_3112_, v___x_3223_, v_options_3111_, v___x_3225_, v___y_3253_, v___f_3221_, v___x_3262_, v___y_3107_, v___y_3108_);
return v___x_3263_;
}
v___jp_3264_:
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_a_3267_);
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v_a_3255_ = v___x_3268_;
goto v___jp_3252_;
}
v___jp_3269_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_box(v_a_3272_);
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
v___y_3253_ = v___y_3270_;
v___y_3254_ = v___y_3271_;
v_a_3255_ = v___x_3274_;
goto v___jp_3252_;
}
v___jp_3275_:
{
if (lean_obj_tag(v___y_3278_) == 0)
{
lean_object* v_a_3279_; uint8_t v___x_3280_; 
v_a_3279_ = lean_ctor_get(v___y_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___y_3278_, 1);
v___x_3280_ = lean_unbox(v_a_3279_);
lean_dec(v_a_3279_);
v___y_3270_ = v___y_3276_;
v___y_3271_ = v___y_3277_;
v_a_3272_ = v___x_3280_;
goto v___jp_3269_;
}
else
{
lean_object* v_a_3281_; 
v_a_3281_ = lean_ctor_get(v___y_3278_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___y_3278_, 1);
v___y_3265_ = v___y_3276_;
v___y_3266_ = v___y_3277_;
v_a_3267_ = v_a_3281_;
goto v___jp_3264_;
}
}
v___jp_3282_:
{
lean_object* v___x_3283_; lean_object* v_a_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3283_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3108_);
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref(v___x_3283_);
v___x_3285_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3286_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3111_, v___x_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v_env_3289_; lean_object* v___x_3290_; 
lean_dec_ref(v___f_3105_);
v___x_3287_ = lean_io_mono_nanos_now();
v___x_3288_ = lean_st_ref_get(v___y_3108_);
v_env_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc_ref(v_env_3289_);
lean_dec(v___x_3288_);
lean_inc(v_name_3106_);
v___x_3290_ = l_Lean_Meta_declFromEqLikeName(v_env_3289_, v_name_3106_);
if (lean_obj_tag(v___x_3290_) == 1)
{
lean_object* v_val_3291_; lean_object* v_fst_3292_; lean_object* v_snd_3293_; lean_object* v___x_3294_; lean_object* v_env_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v_val_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v_fst_3292_ = lean_ctor_get(v_val_3291_, 0);
lean_inc_n(v_fst_3292_, 2);
v_snd_3293_ = lean_ctor_get(v_val_3291_, 1);
lean_inc_n(v_snd_3293_, 2);
lean_dec(v_val_3291_);
v___x_3294_ = lean_st_ref_get(v___y_3108_);
v_env_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc_ref(v_env_3295_);
lean_dec(v___x_3294_);
v___x_3296_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3295_, v_fst_3292_, v_snd_3293_);
v___x_3297_ = lean_name_eq(v_name_3106_, v___x_3296_);
lean_dec(v___x_3296_);
lean_dec(v_name_3106_);
if (v___x_3297_ == 0)
{
lean_dec(v_snd_3293_);
lean_dec(v_fst_3292_);
lean_dec(v___x_3104_);
v___y_3247_ = v_a_3284_;
v___y_3248_ = v___x_3287_;
v_a_3249_ = v___x_3286_;
goto v___jp_3246_;
}
else
{
uint8_t v___x_3298_; 
lean_inc(v_snd_3293_);
v___x_3298_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3293_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3300_ = lean_string_dec_eq(v_snd_3293_, v___x_3299_);
lean_dec(v_snd_3293_);
if (v___x_3300_ == 0)
{
lean_dec(v_fst_3292_);
lean_dec(v___x_3104_);
v___y_3247_ = v_a_3284_;
v___y_3248_ = v___x_3287_;
v_a_3249_ = v___x_3286_;
goto v___jp_3246_;
}
else
{
uint8_t v___x_3301_; uint8_t v___x_3302_; uint8_t v___x_3303_; lean_object* v___x_3304_; uint64_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3301_ = 1;
v___x_3302_ = 0;
v___x_3303_ = 2;
v___x_3304_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3304_, 0, v___x_3298_);
lean_ctor_set_uint8(v___x_3304_, 1, v___x_3298_);
lean_ctor_set_uint8(v___x_3304_, 2, v___x_3298_);
lean_ctor_set_uint8(v___x_3304_, 3, v___x_3298_);
lean_ctor_set_uint8(v___x_3304_, 4, v___x_3298_);
lean_ctor_set_uint8(v___x_3304_, 5, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 6, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 7, v___x_3298_);
lean_ctor_set_uint8(v___x_3304_, 8, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 9, v___x_3301_);
lean_ctor_set_uint8(v___x_3304_, 10, v___x_3302_);
lean_ctor_set_uint8(v___x_3304_, 11, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 12, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 13, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 14, v___x_3303_);
lean_ctor_set_uint8(v___x_3304_, 15, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 16, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 17, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 18, v___x_3300_);
lean_ctor_set_uint8(v___x_3304_, 19, v___x_3298_);
v___x_3305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3304_);
v___x_3306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set_uint64(v___x_3306_, sizeof(void*)*1, v___x_3305_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3309_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3310_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3311_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3312_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3312_, 0, v___x_3306_);
lean_ctor_set(v___x_3312_, 1, v___x_3104_);
lean_ctor_set(v___x_3312_, 2, v___x_3309_);
lean_ctor_set(v___x_3312_, 3, v___x_3310_);
lean_ctor_set(v___x_3312_, 4, v___x_3311_);
lean_ctor_set(v___x_3312_, 5, v___x_3307_);
lean_ctor_set(v___x_3312_, 6, v___x_3311_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*7, v___x_3298_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*7 + 1, v___x_3298_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*7 + 2, v___x_3298_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*7 + 3, v_hasTrace_3112_);
v___x_3313_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3314_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3313_);
lean_ctor_set(v___x_3316_, 1, v___x_3314_);
lean_ctor_set(v___x_3316_, 2, v___x_3104_);
lean_ctor_set(v___x_3316_, 3, v___x_3308_);
lean_ctor_set(v___x_3316_, 4, v___x_3315_);
v___x_3317_ = lean_st_mk_ref(v___x_3316_);
v___x_3318_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3292_, v_hasTrace_3112_, v___x_3312_, v___x_3317_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3312_, 7);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = lean_st_ref_get(v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v___x_3320_);
if (lean_obj_tag(v_a_3319_) == 0)
{
v___y_3247_ = v_a_3284_;
v___y_3248_ = v___x_3287_;
v_a_3249_ = v___x_3298_;
goto v___jp_3246_;
}
else
{
lean_dec_ref_known(v_a_3319_, 1);
v___y_3247_ = v_a_3284_;
v___y_3248_ = v___x_3287_;
v_a_3249_ = v___x_3300_;
goto v___jp_3246_;
}
}
else
{
lean_object* v_a_3321_; 
lean_dec(v___x_3317_);
v_a_3321_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3318_, 1);
v___y_3242_ = v_a_3284_;
v___y_3243_ = v___x_3287_;
v_a_3244_ = v_a_3321_;
goto v___jp_3241_;
}
}
}
else
{
uint8_t v___x_3322_; uint8_t v___x_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; uint64_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec(v_snd_3293_);
v___x_3322_ = 1;
v___x_3323_ = 0;
v___x_3324_ = 2;
v___x_3325_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3325_, 0, v___x_3286_);
lean_ctor_set_uint8(v___x_3325_, 1, v___x_3286_);
lean_ctor_set_uint8(v___x_3325_, 2, v___x_3286_);
lean_ctor_set_uint8(v___x_3325_, 3, v___x_3286_);
lean_ctor_set_uint8(v___x_3325_, 4, v___x_3286_);
lean_ctor_set_uint8(v___x_3325_, 5, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 6, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 7, v___x_3286_);
lean_ctor_set_uint8(v___x_3325_, 8, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 9, v___x_3322_);
lean_ctor_set_uint8(v___x_3325_, 10, v___x_3323_);
lean_ctor_set_uint8(v___x_3325_, 11, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 12, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 13, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 14, v___x_3324_);
lean_ctor_set_uint8(v___x_3325_, 15, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 16, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 17, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 18, v___x_3298_);
lean_ctor_set_uint8(v___x_3325_, 19, v___x_3286_);
v___x_3326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3325_);
v___x_3327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set_uint64(v___x_3327_, sizeof(void*)*1, v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3330_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3332_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3333_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3333_, 0, v___x_3327_);
lean_ctor_set(v___x_3333_, 1, v___x_3104_);
lean_ctor_set(v___x_3333_, 2, v___x_3330_);
lean_ctor_set(v___x_3333_, 3, v___x_3331_);
lean_ctor_set(v___x_3333_, 4, v___x_3332_);
lean_ctor_set(v___x_3333_, 5, v___x_3328_);
lean_ctor_set(v___x_3333_, 6, v___x_3332_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7, v___x_3286_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 1, v___x_3286_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 2, v___x_3286_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 3, v_hasTrace_3112_);
v___x_3334_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3335_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3336_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v___x_3335_);
lean_ctor_set(v___x_3337_, 2, v___x_3104_);
lean_ctor_set(v___x_3337_, 3, v___x_3329_);
lean_ctor_set(v___x_3337_, 4, v___x_3336_);
v___x_3338_ = lean_st_mk_ref(v___x_3337_);
v___x_3339_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3292_, v___x_3333_, v___x_3338_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3333_, 7);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = lean_st_ref_get(v___x_3338_);
lean_dec(v___x_3338_);
lean_dec(v___x_3341_);
if (lean_obj_tag(v_a_3340_) == 0)
{
v___y_3247_ = v_a_3284_;
v___y_3248_ = v___x_3287_;
v_a_3249_ = v___x_3286_;
goto v___jp_3246_;
}
else
{
lean_dec_ref_known(v_a_3340_, 1);
v___y_3247_ = v_a_3284_;
v___y_3248_ = v___x_3287_;
v_a_3249_ = v___x_3298_;
goto v___jp_3246_;
}
}
else
{
lean_object* v_a_3342_; 
lean_dec(v___x_3338_);
v_a_3342_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3339_, 1);
v___y_3242_ = v_a_3284_;
v___y_3243_ = v___x_3287_;
v_a_3244_ = v_a_3342_;
goto v___jp_3241_;
}
}
}
}
else
{
lean_dec(v___x_3290_);
lean_dec(v_name_3106_);
lean_dec(v___x_3104_);
v___y_3247_ = v_a_3284_;
v___y_3248_ = v___x_3287_;
v_a_3249_ = v___x_3286_;
goto v___jp_3246_;
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v_env_3345_; lean_object* v___x_3346_; 
v___x_3343_ = lean_io_get_num_heartbeats();
v___x_3344_ = lean_st_ref_get(v___y_3108_);
v_env_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc_ref(v_env_3345_);
lean_dec(v___x_3344_);
lean_inc(v_name_3106_);
v___x_3346_ = l_Lean_Meta_declFromEqLikeName(v_env_3345_, v_name_3106_);
if (lean_obj_tag(v___x_3346_) == 1)
{
lean_object* v_val_3347_; lean_object* v_fst_3348_; lean_object* v_snd_3349_; lean_object* v___x_3350_; lean_object* v_env_3351_; lean_object* v___x_3352_; uint8_t v___x_3353_; 
v_val_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v_fst_3348_ = lean_ctor_get(v_val_3347_, 0);
lean_inc_n(v_fst_3348_, 2);
v_snd_3349_ = lean_ctor_get(v_val_3347_, 1);
lean_inc_n(v_snd_3349_, 2);
lean_dec(v_val_3347_);
v___x_3350_ = lean_st_ref_get(v___y_3108_);
v_env_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_ref(v_env_3351_);
lean_dec(v___x_3350_);
v___x_3352_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3351_, v_fst_3348_, v_snd_3349_);
v___x_3353_ = lean_name_eq(v_name_3106_, v___x_3352_);
lean_dec(v___x_3352_);
lean_dec(v_name_3106_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec(v_snd_3349_);
lean_dec(v_fst_3348_);
lean_dec(v___x_3104_);
v___x_3354_ = lean_box(0);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v___x_3355_ = lean_apply_4(v___f_3105_, v___x_3354_, v___y_3107_, v___y_3108_, lean_box(0));
v___y_3276_ = v_a_3284_;
v___y_3277_ = v___x_3343_;
v___y_3278_ = v___x_3355_;
goto v___jp_3275_;
}
else
{
uint8_t v___x_3356_; 
lean_inc(v_snd_3349_);
v___x_3356_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3349_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3358_ = lean_string_dec_eq(v_snd_3349_, v___x_3357_);
lean_dec(v_snd_3349_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec(v_fst_3348_);
lean_dec(v___x_3104_);
v___x_3359_ = lean_box(0);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v___x_3360_ = lean_apply_4(v___f_3105_, v___x_3359_, v___y_3107_, v___y_3108_, lean_box(0));
v___y_3276_ = v_a_3284_;
v___y_3277_ = v___x_3343_;
v___y_3278_ = v___x_3360_;
goto v___jp_3275_;
}
else
{
uint8_t v___x_3361_; uint8_t v___x_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; uint64_t v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec_ref(v___f_3105_);
v___x_3361_ = 1;
v___x_3362_ = 0;
v___x_3363_ = 2;
v___x_3364_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3364_, 0, v___x_3356_);
lean_ctor_set_uint8(v___x_3364_, 1, v___x_3356_);
lean_ctor_set_uint8(v___x_3364_, 2, v___x_3356_);
lean_ctor_set_uint8(v___x_3364_, 3, v___x_3356_);
lean_ctor_set_uint8(v___x_3364_, 4, v___x_3356_);
lean_ctor_set_uint8(v___x_3364_, 5, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 6, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 7, v___x_3356_);
lean_ctor_set_uint8(v___x_3364_, 8, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 9, v___x_3361_);
lean_ctor_set_uint8(v___x_3364_, 10, v___x_3362_);
lean_ctor_set_uint8(v___x_3364_, 11, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 12, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 13, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 14, v___x_3363_);
lean_ctor_set_uint8(v___x_3364_, 15, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 16, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 17, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 18, v___x_3358_);
lean_ctor_set_uint8(v___x_3364_, 19, v___x_3356_);
v___x_3365_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3366_, 0, v___x_3364_);
lean_ctor_set_uint64(v___x_3366_, sizeof(void*)*1, v___x_3365_);
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3369_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3371_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3372_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3372_, 0, v___x_3366_);
lean_ctor_set(v___x_3372_, 1, v___x_3104_);
lean_ctor_set(v___x_3372_, 2, v___x_3369_);
lean_ctor_set(v___x_3372_, 3, v___x_3370_);
lean_ctor_set(v___x_3372_, 4, v___x_3371_);
lean_ctor_set(v___x_3372_, 5, v___x_3367_);
lean_ctor_set(v___x_3372_, 6, v___x_3371_);
lean_ctor_set_uint8(v___x_3372_, sizeof(void*)*7, v___x_3356_);
lean_ctor_set_uint8(v___x_3372_, sizeof(void*)*7 + 1, v___x_3356_);
lean_ctor_set_uint8(v___x_3372_, sizeof(void*)*7 + 2, v___x_3356_);
lean_ctor_set_uint8(v___x_3372_, sizeof(void*)*7 + 3, v___x_3286_);
v___x_3373_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3374_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3375_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3373_);
lean_ctor_set(v___x_3376_, 1, v___x_3374_);
lean_ctor_set(v___x_3376_, 2, v___x_3104_);
lean_ctor_set(v___x_3376_, 3, v___x_3368_);
lean_ctor_set(v___x_3376_, 4, v___x_3375_);
v___x_3377_ = lean_st_mk_ref(v___x_3376_);
v___x_3378_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3348_, v___x_3286_, v___x_3372_, v___x_3377_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3372_, 7);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v___x_3380_ = lean_st_ref_get(v___x_3377_);
lean_dec(v___x_3377_);
lean_dec(v___x_3380_);
if (lean_obj_tag(v_a_3379_) == 0)
{
v___y_3270_ = v_a_3284_;
v___y_3271_ = v___x_3343_;
v_a_3272_ = v___x_3356_;
goto v___jp_3269_;
}
else
{
lean_dec_ref_known(v_a_3379_, 1);
v___y_3270_ = v_a_3284_;
v___y_3271_ = v___x_3343_;
v_a_3272_ = v___x_3358_;
goto v___jp_3269_;
}
}
else
{
lean_object* v_a_3381_; 
lean_dec(v___x_3377_);
v_a_3381_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3378_, 1);
v___y_3265_ = v_a_3284_;
v___y_3266_ = v___x_3343_;
v_a_3267_ = v_a_3381_;
goto v___jp_3264_;
}
}
}
else
{
uint8_t v___x_3382_; uint8_t v___x_3383_; uint8_t v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; uint64_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec(v_snd_3349_);
lean_dec_ref(v___f_3105_);
v___x_3382_ = 0;
v___x_3383_ = 1;
v___x_3384_ = 0;
v___x_3385_ = 2;
v___x_3386_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3386_, 0, v___x_3382_);
lean_ctor_set_uint8(v___x_3386_, 1, v___x_3382_);
lean_ctor_set_uint8(v___x_3386_, 2, v___x_3382_);
lean_ctor_set_uint8(v___x_3386_, 3, v___x_3382_);
lean_ctor_set_uint8(v___x_3386_, 4, v___x_3382_);
lean_ctor_set_uint8(v___x_3386_, 5, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 6, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 7, v___x_3382_);
lean_ctor_set_uint8(v___x_3386_, 8, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 9, v___x_3383_);
lean_ctor_set_uint8(v___x_3386_, 10, v___x_3384_);
lean_ctor_set_uint8(v___x_3386_, 11, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 12, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 13, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 14, v___x_3385_);
lean_ctor_set_uint8(v___x_3386_, 15, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 16, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 17, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 18, v___x_3356_);
lean_ctor_set_uint8(v___x_3386_, 19, v___x_3382_);
v___x_3387_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set_uint64(v___x_3388_, sizeof(void*)*1, v___x_3387_);
v___x_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3391_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3393_ = lean_box(0);
lean_inc(v___x_3104_);
v___x_3394_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3394_, 0, v___x_3388_);
lean_ctor_set(v___x_3394_, 1, v___x_3104_);
lean_ctor_set(v___x_3394_, 2, v___x_3391_);
lean_ctor_set(v___x_3394_, 3, v___x_3392_);
lean_ctor_set(v___x_3394_, 4, v___x_3393_);
lean_ctor_set(v___x_3394_, 5, v___x_3389_);
lean_ctor_set(v___x_3394_, 6, v___x_3393_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7, v___x_3382_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7 + 1, v___x_3382_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7 + 2, v___x_3382_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7 + 3, v___x_3286_);
v___x_3395_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3397_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3395_);
lean_ctor_set(v___x_3398_, 1, v___x_3396_);
lean_ctor_set(v___x_3398_, 2, v___x_3104_);
lean_ctor_set(v___x_3398_, 3, v___x_3390_);
lean_ctor_set(v___x_3398_, 4, v___x_3397_);
v___x_3399_ = lean_st_mk_ref(v___x_3398_);
v___x_3400_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3348_, v___x_3394_, v___x_3399_, v___y_3107_, v___y_3108_);
lean_dec_ref_known(v___x_3394_, 7);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = lean_st_ref_get(v___x_3399_);
lean_dec(v___x_3399_);
lean_dec(v___x_3402_);
if (lean_obj_tag(v_a_3401_) == 0)
{
v___y_3270_ = v_a_3284_;
v___y_3271_ = v___x_3343_;
v_a_3272_ = v___x_3382_;
goto v___jp_3269_;
}
else
{
lean_dec_ref_known(v_a_3401_, 1);
v___y_3270_ = v_a_3284_;
v___y_3271_ = v___x_3343_;
v_a_3272_ = v___x_3356_;
goto v___jp_3269_;
}
}
else
{
lean_object* v_a_3403_; 
lean_dec(v___x_3399_);
v_a_3403_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3400_, 1);
v___y_3265_ = v_a_3284_;
v___y_3266_ = v___x_3343_;
v_a_3267_ = v_a_3403_;
goto v___jp_3264_;
}
}
}
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec(v___x_3346_);
lean_dec(v_name_3106_);
lean_dec(v___x_3104_);
v___x_3404_ = lean_box(0);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v___x_3405_ = lean_apply_4(v___f_3105_, v___x_3404_, v___y_3107_, v___y_3108_, lean_box(0));
v___y_3276_ = v_a_3284_;
v___y_3277_ = v___x_3343_;
v___y_3278_ = v___x_3405_;
goto v___jp_3275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3515_, lean_object* v___f_3516_, lean_object* v_name_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3515_, v___f_3516_, v_name_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
return v_res_3521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_unsigned_to_nat(3137104340u);
v___x_3567_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3568_ = l_Lean_Name_num___override(v___x_3567_, v___x_3566_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3571_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3572_ = l_Lean_Name_str___override(v___x_3571_, v___x_3570_);
return v___x_3572_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3575_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3576_ = l_Lean_Name_str___override(v___x_3575_, v___x_3574_);
return v___x_3576_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = lean_unsigned_to_nat(2u);
v___x_3578_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3579_ = l_Lean_Name_num___override(v___x_3578_, v___x_3577_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3581_; lean_object* v___x_3582_; 
v___f_3581_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3582_ = l_Lean_registerReservedNameAction(v___f_3581_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3583_; uint8_t v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec_ref_known(v___x_3582_, 1);
v___x_3583_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__6));
v___x_3584_ = 0;
v___x_3585_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3586_ = l_Lean_registerTraceClass(v___x_3583_, v___x_3584_, v___x_3585_);
return v___x_3586_;
}
else
{
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3589_, lean_object* v_x_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3590_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3595_, v_x_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
return v_res_3600_;
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
