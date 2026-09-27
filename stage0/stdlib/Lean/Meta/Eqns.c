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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_string_utf8_byte_size(v_s_190_);
v___x_192_ = lean_unsigned_to_nat(3u);
v___x_193_ = lean_nat_dec_le(v___x_192_, v___x_191_);
if (v___x_193_ == 0)
{
lean_dec_ref(v_s_190_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_194_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_string_memcmp(v_s_190_, v___x_194_, v___x_195_, v___x_195_, v___x_192_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_s_190_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
lean_inc_ref(v_s_190_);
v___x_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_197_, 0, v_s_190_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
lean_ctor_set(v___x_197_, 2, v___x_191_);
v___x_198_ = l_String_Slice_Pos_nextn(v___x_197_, v___x_195_, v___x_192_);
lean_dec_ref_known(v___x_197_, 3);
v___x_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_199_, 0, v_s_190_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
lean_ctor_set(v___x_199_, 2, v___x_191_);
v___x_200_ = l_String_Slice_isNat(v___x_199_);
lean_dec_ref_known(v___x_199_, 3);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_210_ = lean_string_dec_eq(v_s_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_212_ = lean_string_dec_eq(v_s_208_, v___x_211_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
v___x_213_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_208_);
return v___x_213_;
}
else
{
lean_dec_ref(v_s_208_);
return v___x_212_;
}
}
else
{
lean_dec_ref(v_s_208_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Lean_Meta_isEqnLikeSuffix(v_s_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_220_, lean_object* v_env_221_, uint8_t v___x_222_, lean_object* v_as_x27_223_, lean_object* v_b_224_){
_start:
{
if (lean_obj_tag(v_as_x27_223_) == 0)
{
lean_dec_ref(v_env_221_);
lean_dec_ref(v_str_220_);
lean_inc_ref(v_b_224_);
return v_b_224_;
}
else
{
lean_object* v_head_225_; lean_object* v_tail_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___y_230_; uint8_t v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_head_225_ = lean_ctor_get(v_as_x27_223_, 0);
v_tail_226_ = lean_ctor_get(v_as_x27_223_, 1);
v___x_227_ = lean_box(0);
v___x_228_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_236_ = 0;
lean_inc_ref(v_env_221_);
v___x_237_ = l_Lean_Environment_setExporting(v_env_221_, v___x_236_);
lean_inc(v_head_225_);
v___x_238_ = l_Lean_Environment_isSafeDefinition(v___x_237_, v_head_225_);
if (v___x_238_ == 0)
{
v___y_230_ = v___x_238_;
goto v___jp_229_;
}
else
{
uint8_t v___x_239_; 
lean_inc(v_head_225_);
lean_inc_ref(v_env_221_);
v___x_239_ = l_Lean_Meta_isMatcherCore(v_env_221_, v_head_225_);
if (v___x_239_ == 0)
{
v___y_230_ = v___x_222_;
goto v___jp_229_;
}
else
{
v_as_x27_223_ = v_tail_226_;
v_b_224_ = v___x_228_;
goto _start;
}
}
v___jp_229_:
{
if (v___y_230_ == 0)
{
v_as_x27_223_ = v_tail_226_;
v_b_224_ = v___x_228_;
goto _start;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec_ref(v_env_221_);
lean_inc(v_head_225_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_head_225_);
lean_ctor_set(v___x_232_, 1, v_str_220_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_227_);
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_241_, lean_object* v_env_242_, lean_object* v___x_243_, lean_object* v_as_x27_244_, lean_object* v_b_245_){
_start:
{
uint8_t v___x_616__boxed_246_; lean_object* v_res_247_; 
v___x_616__boxed_246_ = lean_unbox(v___x_243_);
v_res_247_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_241_, v_env_242_, v___x_616__boxed_246_, v_as_x27_244_, v_b_245_);
lean_dec_ref(v_b_245_);
lean_dec(v_as_x27_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_248_, lean_object* v_name_249_){
_start:
{
if (lean_obj_tag(v_name_249_) == 1)
{
lean_object* v_pre_250_; lean_object* v_str_251_; uint8_t v___x_252_; 
v_pre_250_ = lean_ctor_get(v_name_249_, 0);
lean_inc(v_pre_250_);
v_str_251_ = lean_ctor_get(v_name_249_, 1);
lean_inc_ref_n(v_str_251_, 2);
lean_dec_ref_known(v_name_249_, 2);
v___x_252_ = l_Lean_Meta_isEqnLikeSuffix(v_str_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v_str_251_);
lean_dec(v_pre_250_);
lean_dec_ref(v_env_248_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_fst_261_; 
lean_inc(v_pre_250_);
v___x_254_ = l_Lean_privateToUserName(v_pre_250_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v_pre_250_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_box(0);
v___x_259_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_260_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_251_, v_env_248_, v___x_252_, v___x_257_, v___x_259_);
lean_dec_ref_known(v___x_257_, 2);
v_fst_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_fst_261_);
lean_dec_ref(v___x_260_);
if (lean_obj_tag(v_fst_261_) == 0)
{
return v___x_258_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v_fst_261_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v_fst_261_, 1);
return v_val_262_;
}
}
}
else
{
lean_object* v___x_263_; 
lean_dec(v_name_249_);
lean_dec_ref(v_env_248_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_264_, lean_object* v_env_265_, uint8_t v___x_266_, lean_object* v_as_267_, lean_object* v_as_x27_268_, lean_object* v_b_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_264_, v_env_265_, v___x_266_, v_as_x27_268_, v_b_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_272_, lean_object* v_env_273_, lean_object* v___x_274_, lean_object* v_as_275_, lean_object* v_as_x27_276_, lean_object* v_b_277_, lean_object* v_a_278_){
_start:
{
uint8_t v___x_687__boxed_279_; lean_object* v_res_280_; 
v___x_687__boxed_279_ = lean_unbox(v___x_274_);
v_res_280_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_272_, v_env_273_, v___x_687__boxed_279_, v_as_275_, v_as_x27_276_, v_b_277_, v_a_278_);
lean_dec_ref(v_b_277_);
lean_dec(v_as_x27_276_);
lean_dec(v_as_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_281_, lean_object* v_declName_282_, lean_object* v_suffix_283_){
_start:
{
uint8_t v_isExposed_284_; lean_object* v_name_285_; 
lean_inc(v_declName_282_);
lean_inc_ref(v_env_281_);
v_isExposed_284_ = l_Lean_Environment_hasExposedBody(v_env_281_, v_declName_282_);
v_name_285_ = l_Lean_Name_str___override(v_declName_282_, v_suffix_283_);
if (v_isExposed_284_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_mkPrivateName(v_env_281_, v_name_285_);
lean_dec_ref(v_env_281_);
return v___x_286_;
}
else
{
lean_dec_ref(v_env_281_);
return v_name_285_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_287_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_ctor_set(v___x_292_, 2, v___x_291_);
lean_ctor_set(v___x_292_, 3, v___x_291_);
lean_ctor_set(v___x_292_, 4, v___x_290_);
lean_ctor_set(v___x_292_, 5, v___x_290_);
lean_ctor_set(v___x_292_, 6, v___x_290_);
lean_ctor_set(v___x_292_, 7, v___x_290_);
lean_ctor_set(v___x_292_, 8, v___x_290_);
lean_ctor_set(v___x_292_, 9, v___x_290_);
lean_ctor_set(v___x_292_, 10, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(32u);
v___x_294_ = lean_mk_empty_array_with_capacity(v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_296_ = ((size_t)5ULL);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_unsigned_to_nat(32u);
v___x_299_ = lean_mk_empty_array_with_capacity(v___x_298_);
v___x_300_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_301_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
lean_ctor_set(v___x_301_, 2, v___x_297_);
lean_ctor_set(v___x_301_, 3, v___x_297_);
lean_ctor_set_usize(v___x_301_, 4, v___x_296_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_box(1);
v___x_303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_304_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v_toCold_311_; lean_object* v_env_312_; lean_object* v_options_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_310_ = lean_st_ref_get(v___y_308_);
v_toCold_311_ = lean_ctor_get(v___y_307_, 0);
v_env_312_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_310_);
v_options_313_ = lean_ctor_get(v_toCold_311_, 2);
v___x_314_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_313_);
v___x_316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_316_, 0, v_env_312_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
lean_ctor_set(v___x_316_, 3, v_options_313_);
v___x_317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_msgData_306_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_ref_328_; lean_object* v___x_329_; lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_ref_328_ = lean_ctor_get(v___y_325_, 2);
v___x_329_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_324_, v___y_325_, v___y_326_);
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_338_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
lean_inc(v_ref_328_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_ref_328_);
lean_ctor_set(v___x_334_, 1, v_a_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_346_ = l_Lean_stringToMessageData(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_353_, lean_object* v_reservedName_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_358_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_359_ = 0;
v___x_360_ = l_Lean_MessageData_ofConstName(v_declName_353_, v___x_359_);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = 1;
v___x_365_ = l_Lean_MessageData_ofConstName(v_reservedName_354_, v___x_364_);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_368_, v___y_355_, v___y_356_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_370_, lean_object* v_reservedName_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_370_, v_reservedName_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_376_, lean_object* v_suffix_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_reservedName_381_; lean_object* v___x_382_; lean_object* v_env_383_; uint8_t v___x_384_; uint8_t v___x_385_; 
lean_inc(v_declName_376_);
v_reservedName_381_ = l_Lean_Name_str___override(v_declName_376_, v_suffix_377_);
v___x_382_ = lean_st_ref_get(v___y_379_);
v_env_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc_ref(v_env_383_);
lean_dec(v___x_382_);
v___x_384_ = 1;
lean_inc(v_reservedName_381_);
v___x_385_ = l_Lean_Environment_contains(v_env_383_, v_reservedName_381_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_reservedName_381_);
lean_dec(v_declName_376_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_376_, v_reservedName_381_, v___y_378_, v___y_379_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_389_, lean_object* v_suffix_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_389_, v_suffix_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_395_);
v___x_400_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_395_, v___x_399_, v_a_396_, v_a_397_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref_known(v___x_400_, 1);
v___x_401_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_395_);
v___x_402_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_395_, v___x_401_, v_a_396_, v_a_397_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v___x_402_, 1);
v___x_403_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_404_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_395_, v___x_403_, v_a_396_, v_a_397_);
return v___x_404_;
}
else
{
lean_dec(v_declName_395_);
return v___x_402_;
}
}
else
{
lean_dec(v_declName_395_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_411_, v___y_412_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_416_, v_msg_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_421_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_422_, lean_object* v_n_423_){
_start:
{
lean_object* v___x_424_; 
lean_inc(v_n_423_);
lean_inc_ref(v_env_422_);
v___x_424_ = l_Lean_Meta_declFromEqLikeName(v_env_422_, v_n_423_);
if (lean_obj_tag(v___x_424_) == 1)
{
lean_object* v_val_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_val_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v___x_424_, 1);
v_fst_426_ = lean_ctor_get(v_val_425_, 0);
lean_inc(v_fst_426_);
v_snd_427_ = lean_ctor_get(v_val_425_, 1);
lean_inc(v_snd_427_);
lean_dec(v_val_425_);
v___x_428_ = l_Lean_Meta_mkEqLikeNameFor(v_env_422_, v_fst_426_, v_snd_427_);
v___x_429_ = lean_name_eq(v_n_423_, v___x_428_);
lean_dec(v___x_428_);
lean_dec(v_n_423_);
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
lean_dec(v___x_424_);
lean_dec(v_n_423_);
lean_dec_ref(v_env_422_);
v___x_430_ = 0;
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_431_, lean_object* v_n_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_431_, v_n_432_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_437_; lean_object* v___x_438_; 
v___f_437_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_438_ = l_Lean_registerReservedNamePredicate(v___f_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
v___x_443_ = lean_st_mk_ref(v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_446_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_449_ = lean_mk_io_user_error(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_450_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_initializing();
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref(v_f_450_);
v___x_453_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_456_ = lean_st_ref_take(v___x_455_);
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v_f_450_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_st_ref_put(v___x_455_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_registerGetEqnsFn(v_f_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_473_; lean_object* v_env_474_; uint8_t v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_st_ref_get(v_a_467_);
v_env_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_env_474_);
lean_dec(v___x_473_);
v___x_475_ = 0;
lean_inc(v_declName_463_);
v___x_476_ = l_Lean_Environment_findAsync_x3f(v_env_474_, v_declName_463_, v___x_475_);
if (lean_obj_tag(v___x_476_) == 1)
{
lean_object* v_val_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_508_; 
v_val_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_508_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_508_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_val_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_508_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint8_t v_kind_481_; 
v_kind_481_ = lean_ctor_get_uint8(v_val_477_, sizeof(void*)*3);
if (v_kind_481_ == 0)
{
lean_object* v_sig_482_; lean_object* v___x_483_; lean_object* v_env_484_; uint8_t v___x_485_; 
v_sig_482_ = lean_ctor_get(v_val_477_, 1);
lean_inc_ref(v_sig_482_);
lean_dec(v_val_477_);
v___x_483_ = lean_st_ref_get(v_a_467_);
v_env_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_env_484_);
lean_dec(v___x_483_);
v___x_485_ = l_Lean_Meta_isMatcherCore(v_env_484_, v_declName_463_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v_type_487_; lean_object* v___x_488_; 
lean_del_object(v___x_479_);
v___x_486_ = lean_task_get_own(v_sig_482_);
v_type_487_ = lean_ctor_get(v___x_486_, 2);
lean_inc_ref(v_type_487_);
lean_dec(v___x_486_);
v___x_488_ = l_Lean_Meta_isProp(v_type_487_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_503_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_503_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
uint8_t v___x_493_; 
v___x_493_ = lean_unbox(v_a_489_);
lean_dec(v_a_489_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_494_ = 1;
v___x_495_ = lean_box(v___x_494_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_495_);
v___x_497_ = v___x_491_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_box(v___x_485_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_499_);
v___x_501_ = v___x_491_;
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
}
}
else
{
return v___x_488_;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec_ref(v_sig_482_);
v___x_504_ = lean_box(v___x_475_);
if (v_isShared_480_ == 0)
{
lean_ctor_set_tag(v___x_479_, 0);
lean_ctor_set(v___x_479_, 0, v___x_504_);
v___x_506_ = v___x_479_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_del_object(v___x_479_);
lean_dec(v_val_477_);
lean_dec(v_declName_463_);
goto v___jp_469_;
}
}
}
else
{
lean_dec(v___x_476_);
lean_dec(v_declName_463_);
goto v___jp_469_;
}
v___jp_469_:
{
uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = 0;
v___x_471_ = lean_box(v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_523_);
return v_res_525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_526_; lean_object* v___f_527_; 
v___x_526_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_527_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_527_, 0, v___x_526_);
return v___f_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___f_529_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_530_ = lean_box(0);
v___x_531_ = lean_box(1);
v___x_532_ = l_Lean_registerEnvExtension___redArg(v___f_529_, v___x_530_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_535_, lean_object* v_opt_536_){
_start:
{
lean_object* v_name_537_; lean_object* v_defValue_538_; lean_object* v_map_539_; lean_object* v___x_540_; 
v_name_537_ = lean_ctor_get(v_opt_536_, 0);
v_defValue_538_ = lean_ctor_get(v_opt_536_, 1);
v_map_539_ = lean_ctor_get(v_opts_535_, 0);
v___x_540_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_539_, v_name_537_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_inc(v_defValue_538_);
return v_defValue_538_;
}
else
{
lean_object* v_val_541_; 
v_val_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_540_, 1);
if (lean_obj_tag(v_val_541_) == 3)
{
lean_object* v_v_542_; 
v_v_542_ = lean_ctor_get(v_val_541_, 0);
lean_inc(v_v_542_);
lean_dec_ref_known(v_val_541_, 1);
return v_v_542_;
}
else
{
lean_dec(v_val_541_);
lean_inc(v_defValue_538_);
return v_defValue_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_543_, lean_object* v_opt_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_543_, v_opt_544_);
lean_dec_ref(v_opt_544_);
lean_dec_ref(v_opts_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_b_552_){
_start:
{
lean_object* v_a_554_; uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_558_ == 0)
{
return v_b_552_;
}
else
{
lean_object* v_a_559_; lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v_map_562_; uint8_t v_hasTrace_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_576_; 
v_a_559_ = lean_array_uget_borrowed(v_as_549_, v_i_551_);
v_fst_560_ = lean_ctor_get(v_a_559_, 0);
v_snd_561_ = lean_ctor_get(v_a_559_, 1);
v_map_562_ = lean_ctor_get(v_b_552_, 0);
v_hasTrace_563_ = lean_ctor_get_uint8(v_b_552_, sizeof(void*)*1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_b_552_);
if (v_isSharedCheck_576_ == 0)
{
v___x_565_ = v_b_552_;
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_map_562_);
lean_dec(v_b_552_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; 
lean_inc(v_snd_561_);
lean_inc(v_fst_560_);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_560_, v_snd_561_, v_map_562_);
if (v_hasTrace_563_ == 0)
{
lean_object* v___x_568_; uint8_t v___x_569_; lean_object* v___x_571_; 
v___x_568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_569_ = l_Lean_Name_isPrefixOf(v___x_568_, v_fst_560_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_567_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*1, v___x_569_);
v_a_554_ = v___x_571_;
goto v___jp_553_;
}
}
else
{
lean_object* v___x_574_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_574_ = v___x_565_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_567_);
lean_ctor_set_uint8(v_reuseFailAlloc_575_, sizeof(void*)*1, v_hasTrace_563_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
v_a_554_ = v___x_574_;
goto v___jp_553_;
}
}
}
}
v___jp_553_:
{
size_t v___x_555_; size_t v___x_556_; 
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_551_, v___x_555_);
v_i_551_ = v___x_556_;
v_b_552_ = v_a_554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_577_, lean_object* v_sz_578_, lean_object* v_i_579_, lean_object* v_b_580_){
_start:
{
size_t v_sz_boxed_581_; size_t v_i_boxed_582_; lean_object* v_res_583_; 
v_sz_boxed_581_ = lean_unbox_usize(v_sz_578_);
lean_dec(v_sz_578_);
v_i_boxed_582_ = lean_unbox_usize(v_i_579_);
lean_dec(v_i_579_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_577_, v_sz_boxed_581_, v_i_boxed_582_, v_b_580_);
lean_dec_ref(v_as_577_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_584_, lean_object* v_k_585_, uint8_t v_v_586_){
_start:
{
lean_object* v_map_587_; uint8_t v_hasTrace_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_602_; 
v_map_587_ = lean_ctor_get(v_o_584_, 0);
v_hasTrace_588_ = lean_ctor_get_uint8(v_o_584_, sizeof(void*)*1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_o_584_);
if (v_isSharedCheck_602_ == 0)
{
v___x_590_ = v_o_584_;
v_isShared_591_ = v_isSharedCheck_602_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_map_587_);
lean_dec(v_o_584_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_602_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_592_, 0, v_v_586_);
lean_inc(v_k_585_);
v___x_593_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_585_, v___x_592_, v_map_587_);
if (v_hasTrace_588_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_597_; 
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_595_ = l_Lean_Name_isPrefixOf(v___x_594_, v_k_585_);
lean_dec(v_k_585_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_593_);
v___x_597_ = v___x_590_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_593_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*1, v___x_595_);
return v___x_597_;
}
}
else
{
lean_object* v___x_600_; 
lean_dec(v_k_585_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_593_);
v___x_600_ = v___x_590_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_593_);
lean_ctor_set_uint8(v_reuseFailAlloc_601_, sizeof(void*)*1, v_hasTrace_588_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_603_, lean_object* v_k_604_, lean_object* v_v_605_){
_start:
{
uint8_t v_v_boxed_606_; lean_object* v_res_607_; 
v_v_boxed_606_ = lean_unbox(v_v_605_);
v_res_607_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_603_, v_k_604_, v_v_boxed_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_608_, lean_object* v_opt_609_, uint8_t v_val_610_){
_start:
{
lean_object* v_name_611_; lean_object* v___x_612_; 
v_name_611_ = lean_ctor_get(v_opt_609_, 0);
lean_inc(v_name_611_);
lean_dec_ref(v_opt_609_);
v___x_612_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_608_, v_name_611_, v_val_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_613_, lean_object* v_opt_614_, lean_object* v_val_615_){
_start:
{
uint8_t v_val_boxed_616_; lean_object* v_res_617_; 
v_val_boxed_616_ = lean_unbox(v_val_615_);
v_res_617_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_613_, v_opt_614_, v_val_boxed_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_618_, size_t v_i_619_, size_t v_stop_620_, lean_object* v_b_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_eq(v_i_619_, v_stop_620_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v_defValue_624_; uint8_t v___x_625_; lean_object* v___x_626_; size_t v___x_627_; size_t v___x_628_; 
v___x_623_ = lean_array_uget_borrowed(v_as_618_, v_i_619_);
v_defValue_624_ = lean_ctor_get(v___x_623_, 1);
v___x_625_ = lean_unbox(v_defValue_624_);
lean_inc(v___x_623_);
v___x_626_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_621_, v___x_623_, v___x_625_);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_619_, v___x_627_);
v_i_619_ = v___x_628_;
v_b_621_ = v___x_626_;
goto _start;
}
else
{
return v_b_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_630_, lean_object* v_i_631_, lean_object* v_stop_632_, lean_object* v_b_633_){
_start:
{
size_t v_i_boxed_634_; size_t v_stop_boxed_635_; lean_object* v_res_636_; 
v_i_boxed_634_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_stop_boxed_635_ = lean_unbox_usize(v_stop_632_);
lean_dec(v_stop_632_);
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_630_, v_i_boxed_634_, v_stop_boxed_635_, v_b_633_);
lean_dec_ref(v_as_630_);
return v_res_636_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Array_instInhabited___redArg();
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_Lean_Meta_eqnAffectingOptions;
v___x_643_ = lean_array_get_size(v___x_642_);
return v___x_643_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_644_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_nat_dec_lt(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_648_ = lean_nat_dec_le(v___x_647_, v___x_647_);
return v___x_648_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_649_; size_t v___x_650_; 
v___x_649_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_650_ = lean_usize_of_nat(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_651_, lean_object* v_act_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___y_659_; uint16_t v___y_660_; lean_object* v_fileName_661_; lean_object* v_fileMap_662_; lean_object* v_currNamespace_663_; lean_object* v_openDecls_664_; lean_object* v_initHeartbeats_665_; lean_object* v_maxHeartbeats_666_; lean_object* v_quotContext_667_; lean_object* v_currMacroScope_668_; lean_object* v_cancelTk_x3f_669_; lean_object* v_inheritedTraceOptions_670_; lean_object* v_currRecDepth_671_; lean_object* v_ref_672_; uint8_t v_suppressElabErrors_673_; uint8_t v_isRecordingDeps_674_; lean_object* v___y_675_; lean_object* v___y_682_; uint16_t v___y_683_; uint8_t v___y_684_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_toCold_723_; lean_object* v_currRecDepth_724_; lean_object* v_ref_725_; uint8_t v_suppressElabErrors_726_; uint8_t v_isRecordingDeps_727_; lean_object* v_fileName_728_; lean_object* v_fileMap_729_; lean_object* v_options_730_; lean_object* v_currNamespace_731_; lean_object* v_openDecls_732_; lean_object* v_initHeartbeats_733_; lean_object* v_maxHeartbeats_734_; lean_object* v_quotContext_735_; lean_object* v_currMacroScope_736_; lean_object* v_cancelTk_x3f_737_; lean_object* v_inheritedTraceOptions_738_; lean_object* v___y_740_; 
v___x_721_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_722_ = lean_st_ref_get(v_a_656_);
v_toCold_723_ = lean_ctor_get(v_a_655_, 0);
v_currRecDepth_724_ = lean_ctor_get(v_a_655_, 1);
v_ref_725_ = lean_ctor_get(v_a_655_, 2);
v_suppressElabErrors_726_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*3 + 2);
v_isRecordingDeps_727_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*3 + 3);
v_fileName_728_ = lean_ctor_get(v_toCold_723_, 0);
v_fileMap_729_ = lean_ctor_get(v_toCold_723_, 1);
v_options_730_ = lean_ctor_get(v_toCold_723_, 2);
v_currNamespace_731_ = lean_ctor_get(v_toCold_723_, 4);
v_openDecls_732_ = lean_ctor_get(v_toCold_723_, 5);
v_initHeartbeats_733_ = lean_ctor_get(v_toCold_723_, 6);
v_maxHeartbeats_734_ = lean_ctor_get(v_toCold_723_, 7);
v_quotContext_735_ = lean_ctor_get(v_toCold_723_, 8);
v_currMacroScope_736_ = lean_ctor_get(v_toCold_723_, 9);
v_cancelTk_x3f_737_ = lean_ctor_get(v_toCold_723_, 10);
v_inheritedTraceOptions_738_ = lean_ctor_get(v_toCold_723_, 11);
if (v_isRecordingDeps_727_ == 0)
{
lean_object* v_env_751_; lean_object* v___x_752_; lean_object* v_toEnvExtension_753_; lean_object* v_asyncMode_754_; uint8_t v___x_755_; lean_object* v___x_756_; 
v_env_751_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_env_751_);
lean_dec(v___x_722_);
v___x_752_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_753_ = lean_ctor_get(v___x_752_, 0);
v_asyncMode_754_ = lean_ctor_get(v_toEnvExtension_753_, 2);
v___x_755_ = 0;
v___x_756_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_721_, v___x_752_, v_env_751_, v_declName_651_, v_asyncMode_754_, v___x_755_);
if (lean_obj_tag(v___x_756_) == 1)
{
lean_object* v_val_757_; lean_object* v___y_759_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_val_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v___x_756_, 1);
v___x_763_ = l_Lean_Meta_eqnAffectingOptions;
v___x_764_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_764_ == 0)
{
lean_inc_ref(v_options_730_);
v___y_759_ = v_options_730_;
goto v___jp_758_;
}
else
{
uint8_t v___x_765_; 
v___x_765_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_765_ == 0)
{
if (v___x_764_ == 0)
{
lean_inc_ref(v_options_730_);
v___y_759_ = v_options_730_;
goto v___jp_758_;
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_730_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_763_, v___x_766_, v___x_767_, v_options_730_);
v___y_759_ = v___x_768_;
goto v___jp_758_;
}
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_730_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_763_, v___x_769_, v___x_770_, v_options_730_);
v___y_759_ = v___x_771_;
goto v___jp_758_;
}
}
v___jp_758_:
{
size_t v_sz_760_; size_t v___x_761_; lean_object* v___x_762_; 
v_sz_760_ = lean_array_size(v_val_757_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_757_, v_sz_760_, v___x_761_, v___y_759_);
lean_dec(v_val_757_);
v___y_740_ = v___x_762_;
goto v___jp_739_;
}
}
else
{
lean_object* v___x_772_; uint8_t v___x_773_; 
lean_dec(v___x_756_);
v___x_772_ = l_Lean_Meta_eqnAffectingOptions;
v___x_773_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_773_ == 0)
{
lean_inc_ref(v_options_730_);
v___y_740_ = v_options_730_;
goto v___jp_739_;
}
else
{
uint8_t v___x_774_; 
v___x_774_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_774_ == 0)
{
if (v___x_773_ == 0)
{
lean_inc_ref(v_options_730_);
v___y_740_ = v_options_730_;
goto v___jp_739_;
}
else
{
size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_730_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_772_, v___x_775_, v___x_776_, v_options_730_);
v___y_740_ = v___x_777_;
goto v___jp_739_;
}
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_730_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_772_, v___x_778_, v___x_779_, v_options_730_);
v___y_740_ = v___x_780_;
goto v___jp_739_;
}
}
}
}
else
{
lean_object* v___x_781_; 
lean_dec(v___x_722_);
lean_dec(v_declName_651_);
lean_inc_ref(v_options_730_);
v___x_781_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_730_);
v___y_740_ = v___x_781_;
goto v___jp_739_;
}
v___jp_658_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = l_Lean_maxRecDepth;
v___x_677_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_659_, v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_678_, 0, v_fileName_661_);
lean_ctor_set(v___x_678_, 1, v_fileMap_662_);
lean_ctor_set(v___x_678_, 2, v___y_659_);
lean_ctor_set(v___x_678_, 3, v___x_677_);
lean_ctor_set(v___x_678_, 4, v_currNamespace_663_);
lean_ctor_set(v___x_678_, 5, v_openDecls_664_);
lean_ctor_set(v___x_678_, 6, v_initHeartbeats_665_);
lean_ctor_set(v___x_678_, 7, v_maxHeartbeats_666_);
lean_ctor_set(v___x_678_, 8, v_quotContext_667_);
lean_ctor_set(v___x_678_, 9, v_currMacroScope_668_);
lean_ctor_set(v___x_678_, 10, v_cancelTk_x3f_669_);
lean_ctor_set(v___x_678_, 11, v_inheritedTraceOptions_670_);
lean_inc(v_ref_672_);
lean_inc(v_currRecDepth_671_);
v___x_679_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v_currRecDepth_671_);
lean_ctor_set(v___x_679_, 2, v_ref_672_);
lean_ctor_set_uint16(v___x_679_, sizeof(void*)*3, v___y_660_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*3 + 2, v_suppressElabErrors_673_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*3 + 3, v_isRecordingDeps_674_);
lean_inc(v___y_675_);
lean_inc(v_a_654_);
lean_inc_ref(v_a_653_);
v___x_680_ = lean_apply_5(v_act_652_, v_a_653_, v_a_654_, v___x_679_, v___y_675_, lean_box(0));
return v___x_680_;
}
v___jp_681_:
{
lean_object* v___x_685_; lean_object* v_env_686_; lean_object* v_nextMacroScope_687_; lean_object* v_ngen_688_; lean_object* v_auxDeclNGen_689_; lean_object* v_traceState_690_; lean_object* v_recordedDeps_691_; lean_object* v_messages_692_; lean_object* v_infoState_693_; lean_object* v_snapshotTasks_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_719_; 
v___x_685_ = lean_st_ref_take(v_a_656_);
v_env_686_ = lean_ctor_get(v___x_685_, 0);
v_nextMacroScope_687_ = lean_ctor_get(v___x_685_, 1);
v_ngen_688_ = lean_ctor_get(v___x_685_, 2);
v_auxDeclNGen_689_ = lean_ctor_get(v___x_685_, 3);
v_traceState_690_ = lean_ctor_get(v___x_685_, 4);
v_recordedDeps_691_ = lean_ctor_get(v___x_685_, 6);
v_messages_692_ = lean_ctor_get(v___x_685_, 7);
v_infoState_693_ = lean_ctor_get(v___x_685_, 8);
v_snapshotTasks_694_ = lean_ctor_get(v___x_685_, 9);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_685_, 5);
lean_dec(v_unused_720_);
v___x_696_ = v___x_685_;
v_isShared_697_ = v_isSharedCheck_719_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snapshotTasks_694_);
lean_inc(v_infoState_693_);
lean_inc(v_messages_692_);
lean_inc(v_recordedDeps_691_);
lean_inc(v_traceState_690_);
lean_inc(v_auxDeclNGen_689_);
lean_inc(v_ngen_688_);
lean_inc(v_nextMacroScope_687_);
lean_inc(v_env_686_);
lean_dec(v___x_685_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_719_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_698_ = l_Lean_Kernel_enableDiag(v_env_686_, v___y_684_);
v___x_699_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 5, v___x_699_);
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_701_ = v___x_696_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_nextMacroScope_687_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_ngen_688_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_auxDeclNGen_689_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_traceState_690_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_recordedDeps_691_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_messages_692_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_infoState_693_);
lean_ctor_set(v_reuseFailAlloc_718_, 9, v_snapshotTasks_694_);
v___x_701_ = v_reuseFailAlloc_718_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v_toCold_703_; lean_object* v_currRecDepth_704_; lean_object* v_ref_705_; uint8_t v_suppressElabErrors_706_; uint8_t v_isRecordingDeps_707_; lean_object* v_fileName_708_; lean_object* v_fileMap_709_; lean_object* v_currNamespace_710_; lean_object* v_openDecls_711_; lean_object* v_initHeartbeats_712_; lean_object* v_maxHeartbeats_713_; lean_object* v_quotContext_714_; lean_object* v_currMacroScope_715_; lean_object* v_cancelTk_x3f_716_; lean_object* v_inheritedTraceOptions_717_; 
v___x_702_ = lean_st_ref_put(v_a_656_, v___x_701_);
v_toCold_703_ = lean_ctor_get(v_a_655_, 0);
v_currRecDepth_704_ = lean_ctor_get(v_a_655_, 1);
v_ref_705_ = lean_ctor_get(v_a_655_, 2);
v_suppressElabErrors_706_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*3 + 2);
v_isRecordingDeps_707_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*3 + 3);
v_fileName_708_ = lean_ctor_get(v_toCold_703_, 0);
v_fileMap_709_ = lean_ctor_get(v_toCold_703_, 1);
v_currNamespace_710_ = lean_ctor_get(v_toCold_703_, 4);
v_openDecls_711_ = lean_ctor_get(v_toCold_703_, 5);
v_initHeartbeats_712_ = lean_ctor_get(v_toCold_703_, 6);
v_maxHeartbeats_713_ = lean_ctor_get(v_toCold_703_, 7);
v_quotContext_714_ = lean_ctor_get(v_toCold_703_, 8);
v_currMacroScope_715_ = lean_ctor_get(v_toCold_703_, 9);
v_cancelTk_x3f_716_ = lean_ctor_get(v_toCold_703_, 10);
v_inheritedTraceOptions_717_ = lean_ctor_get(v_toCold_703_, 11);
lean_inc_ref(v_inheritedTraceOptions_717_);
lean_inc(v_cancelTk_x3f_716_);
lean_inc(v_currMacroScope_715_);
lean_inc(v_quotContext_714_);
lean_inc(v_maxHeartbeats_713_);
lean_inc(v_initHeartbeats_712_);
lean_inc(v_openDecls_711_);
lean_inc(v_currNamespace_710_);
lean_inc_ref(v_fileMap_709_);
lean_inc_ref(v_fileName_708_);
v___y_659_ = v___y_682_;
v___y_660_ = v___y_683_;
v_fileName_661_ = v_fileName_708_;
v_fileMap_662_ = v_fileMap_709_;
v_currNamespace_663_ = v_currNamespace_710_;
v_openDecls_664_ = v_openDecls_711_;
v_initHeartbeats_665_ = v_initHeartbeats_712_;
v_maxHeartbeats_666_ = v_maxHeartbeats_713_;
v_quotContext_667_ = v_quotContext_714_;
v_currMacroScope_668_ = v_currMacroScope_715_;
v_cancelTk_x3f_669_ = v_cancelTk_x3f_716_;
v_inheritedTraceOptions_670_ = v_inheritedTraceOptions_717_;
v_currRecDepth_671_ = v_currRecDepth_704_;
v_ref_672_ = v_ref_705_;
v_suppressElabErrors_673_ = v_suppressElabErrors_706_;
v_isRecordingDeps_674_ = v_isRecordingDeps_707_;
v___y_675_ = v_a_656_;
goto v___jp_658_;
}
}
}
v___jp_739_:
{
uint16_t v___x_741_; lean_object* v___x_742_; lean_object* v_env_743_; uint8_t v___x_744_; uint16_t v___x_745_; uint16_t v___x_746_; uint16_t v___x_747_; uint8_t v___x_748_; 
v___x_741_ = l_Lean_OptionFlags_ofOptions(v___y_740_);
v___x_742_ = lean_st_ref_get(v_a_656_);
v_env_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_env_743_);
lean_dec(v___x_742_);
v___x_744_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_743_);
lean_dec_ref(v_env_743_);
v___x_745_ = 512;
v___x_746_ = lean_uint16_land(v___x_741_, v___x_745_);
v___x_747_ = 0;
v___x_748_ = lean_uint16_dec_eq(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
if (v___x_744_ == 0)
{
uint8_t v___x_749_; 
v___x_749_ = 1;
v___y_682_ = v___y_740_;
v___y_683_ = v___x_741_;
v___y_684_ = v___x_749_;
goto v___jp_681_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_738_);
lean_inc(v_cancelTk_x3f_737_);
lean_inc(v_currMacroScope_736_);
lean_inc(v_quotContext_735_);
lean_inc(v_maxHeartbeats_734_);
lean_inc(v_initHeartbeats_733_);
lean_inc(v_openDecls_732_);
lean_inc(v_currNamespace_731_);
lean_inc_ref(v_fileMap_729_);
lean_inc_ref(v_fileName_728_);
v___y_659_ = v___y_740_;
v___y_660_ = v___x_741_;
v_fileName_661_ = v_fileName_728_;
v_fileMap_662_ = v_fileMap_729_;
v_currNamespace_663_ = v_currNamespace_731_;
v_openDecls_664_ = v_openDecls_732_;
v_initHeartbeats_665_ = v_initHeartbeats_733_;
v_maxHeartbeats_666_ = v_maxHeartbeats_734_;
v_quotContext_667_ = v_quotContext_735_;
v_currMacroScope_668_ = v_currMacroScope_736_;
v_cancelTk_x3f_669_ = v_cancelTk_x3f_737_;
v_inheritedTraceOptions_670_ = v_inheritedTraceOptions_738_;
v_currRecDepth_671_ = v_currRecDepth_724_;
v_ref_672_ = v_ref_725_;
v_suppressElabErrors_673_ = v_suppressElabErrors_726_;
v_isRecordingDeps_674_ = v_isRecordingDeps_727_;
v___y_675_ = v_a_656_;
goto v___jp_658_;
}
}
else
{
if (v___x_744_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_738_);
lean_inc(v_cancelTk_x3f_737_);
lean_inc(v_currMacroScope_736_);
lean_inc(v_quotContext_735_);
lean_inc(v_maxHeartbeats_734_);
lean_inc(v_initHeartbeats_733_);
lean_inc(v_openDecls_732_);
lean_inc(v_currNamespace_731_);
lean_inc_ref(v_fileMap_729_);
lean_inc_ref(v_fileName_728_);
v___y_659_ = v___y_740_;
v___y_660_ = v___x_741_;
v_fileName_661_ = v_fileName_728_;
v_fileMap_662_ = v_fileMap_729_;
v_currNamespace_663_ = v_currNamespace_731_;
v_openDecls_664_ = v_openDecls_732_;
v_initHeartbeats_665_ = v_initHeartbeats_733_;
v_maxHeartbeats_666_ = v_maxHeartbeats_734_;
v_quotContext_667_ = v_quotContext_735_;
v_currMacroScope_668_ = v_currMacroScope_736_;
v_cancelTk_x3f_669_ = v_cancelTk_x3f_737_;
v_inheritedTraceOptions_670_ = v_inheritedTraceOptions_738_;
v_currRecDepth_671_ = v_currRecDepth_724_;
v_ref_672_ = v_ref_725_;
v_suppressElabErrors_673_ = v_suppressElabErrors_726_;
v_isRecordingDeps_674_ = v_isRecordingDeps_727_;
v___y_675_ = v_a_656_;
goto v___jp_658_;
}
else
{
uint8_t v___x_750_; 
v___x_750_ = 0;
v___y_682_ = v___y_740_;
v___y_683_ = v___x_741_;
v___y_684_ = v___x_750_;
goto v___jp_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_782_, lean_object* v_act_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_782_, v_act_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_790_, lean_object* v_declName_791_, lean_object* v_act_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_791_, v_act_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_799_, lean_object* v_declName_800_, lean_object* v_act_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_799_, v_declName_800_, v_act_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v_env_812_; lean_object* v_toConstantVal_813_; lean_object* v_value_814_; lean_object* v_all_815_; uint8_t v___y_817_; lean_object* v_type_825_; uint8_t v___x_826_; 
v___x_811_ = lean_st_ref_get(v___y_809_);
v_env_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref_n(v_env_812_, 2);
lean_dec(v___x_811_);
v_toConstantVal_813_ = lean_ctor_get(v_thm_808_, 0);
v_value_814_ = lean_ctor_get(v_thm_808_, 1);
v_all_815_ = lean_ctor_get(v_thm_808_, 2);
v_type_825_ = lean_ctor_get(v_toConstantVal_813_, 2);
v___x_826_ = l_Lean_Environment_hasUnsafe(v_env_812_, v_type_825_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_Environment_hasUnsafe(v_env_812_, v_value_814_);
v___y_817_ = v___x_827_;
goto v___jp_816_;
}
else
{
lean_dec_ref(v_env_812_);
v___y_817_ = v___x_826_;
goto v___jp_816_;
}
v___jp_816_:
{
if (v___y_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_818_, 0, v_thm_808_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc(v_all_815_);
lean_inc_ref(v_value_814_);
lean_inc_ref(v_toConstantVal_813_);
lean_dec_ref(v_thm_808_);
v___x_820_ = lean_box(0);
v___x_821_ = 0;
v___x_822_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_822_, 0, v_toConstantVal_813_);
lean_ctor_set(v___x_822_, 1, v_value_814_);
lean_ctor_set(v___x_822_, 2, v___x_820_);
lean_ctor_set(v___x_822_, 3, v_all_815_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*4, v___x_821_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_828_, v___y_829_);
lean_dec(v___y_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_832_, v___y_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_846_, lean_object* v_b_847_, lean_object* v_c_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
v___x_854_ = lean_apply_7(v_k_846_, v_b_847_, v_c_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, lean_box(0));
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_855_, lean_object* v_b_856_, lean_object* v_c_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_855_, v_b_856_, v_c_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_864_, lean_object* v_k_865_, uint8_t v_cleanupAnnotations_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___f_872_; uint8_t v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___f_872_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_872_, 0, v_k_865_);
v___x_873_ = 1;
v___x_874_ = 0;
v___x_875_ = lean_box(0);
v___x_876_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_864_, v___x_873_, v___x_874_, v___x_873_, v___x_874_, v___x_875_, v___f_872_, v_cleanupAnnotations_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_876_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_876_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_893_, lean_object* v_k_894_, lean_object* v_cleanupAnnotations_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_901_; lean_object* v_res_902_; 
v_cleanupAnnotations_boxed_901_ = lean_unbox(v_cleanupAnnotations_895_);
v_res_902_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_893_, v_k_894_, v_cleanupAnnotations_boxed_901_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_903_, lean_object* v_e_904_, lean_object* v_k_905_, uint8_t v_cleanupAnnotations_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_904_, v_k_905_, v_cleanupAnnotations_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_913_, lean_object* v_e_914_, lean_object* v_k_915_, lean_object* v_cleanupAnnotations_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_922_; lean_object* v_res_923_; 
v_cleanupAnnotations_boxed_922_ = lean_unbox(v_cleanupAnnotations_916_);
v_res_923_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_913_, v_e_914_, v_k_915_, v_cleanupAnnotations_boxed_922_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
if (lean_obj_tag(v_a_924_) == 0)
{
lean_object* v___x_926_; 
v___x_926_ = l_List_reverse___redArg(v_a_925_);
return v___x_926_;
}
else
{
lean_object* v_head_927_; lean_object* v_tail_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_937_; 
v_head_927_ = lean_ctor_get(v_a_924_, 0);
v_tail_928_ = lean_ctor_get(v_a_924_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_930_ = v_a_924_;
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_tail_928_);
lean_inc(v_head_927_);
lean_dec(v_a_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = l_Lean_mkLevelParam(v_head_927_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v_a_925_);
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_a_925_);
v___x_934_ = v_reuseFailAlloc_936_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
v_a_924_ = v_tail_928_;
v_a_925_ = v___x_934_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_938_, lean_object* v_name_939_, lean_object* v_xs_940_, lean_object* v_body_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_name_947_; lean_object* v_levelParams_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1018_; 
v_name_947_ = lean_ctor_get(v_toConstantVal_938_, 0);
v_levelParams_948_ = lean_ctor_get(v_toConstantVal_938_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_toConstantVal_938_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_toConstantVal_938_, 2);
lean_dec(v_unused_1019_);
v___x_950_ = v_toConstantVal_938_;
v_isShared_951_ = v_isSharedCheck_1018_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_levelParams_948_);
lean_inc(v_name_947_);
lean_dec(v_toConstantVal_938_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1018_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_lhs_955_; lean_object* v___x_956_; 
v___x_952_ = lean_box(0);
lean_inc(v_levelParams_948_);
v___x_953_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_948_, v___x_952_);
v___x_954_ = l_Lean_mkConst(v_name_947_, v___x_953_);
v_lhs_955_ = l_Lean_mkAppN(v___x_954_, v_xs_940_);
lean_inc_ref(v_lhs_955_);
v___x_956_ = l_Lean_Meta_mkEq(v_lhs_955_, v_body_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; uint8_t v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = 0;
v___x_959_ = 1;
v___x_960_ = 1;
v___x_961_ = l_Lean_Meta_mkForallFVars(v_xs_940_, v_a_957_, v___x_958_, v___x_959_, v___x_959_, v___x_960_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = l_Lean_Meta_letToHave(v_a_962_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = l_Lean_Meta_mkEqRefl(v_lhs_955_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Meta_mkLambdaFVars(v_xs_940_, v_a_966_, v___x_958_, v___x_959_, v___x_958_, v___x_959_, v___x_960_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
lean_inc(v_name_939_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 2, v_a_964_);
lean_ctor_set(v___x_950_, 0, v_name_939_);
v___x_970_ = v___x_950_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_name_939_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_levelParams_948_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_a_964_);
v___x_970_ = v_reuseFailAlloc_977_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_a_974_; lean_object* v___x_975_; 
lean_inc(v_name_939_);
v___x_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_971_, 0, v_name_939_);
lean_ctor_set(v___x_971_, 1, v___x_952_);
v___x_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v_a_968_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
v___x_973_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_972_, v___y_945_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = l_Lean_addDecl(v_a_974_, v___x_958_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_976_; 
lean_dec_ref_known(v___x_975_, 1);
v___x_976_ = l_Lean_inferDefEqAttr(v_name_939_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_976_;
}
else
{
lean_dec(v_name_939_);
return v___x_975_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_a_964_);
lean_del_object(v___x_950_);
lean_dec(v_levelParams_948_);
lean_dec(v_name_939_);
v_a_978_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_967_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_967_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_a_964_);
lean_del_object(v___x_950_);
lean_dec(v_levelParams_948_);
lean_dec(v_name_939_);
v_a_986_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_965_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_965_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v_lhs_955_);
lean_del_object(v___x_950_);
lean_dec(v_levelParams_948_);
lean_dec(v_name_939_);
v_a_994_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_963_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_963_);
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
lean_dec_ref(v_lhs_955_);
lean_del_object(v___x_950_);
lean_dec(v_levelParams_948_);
lean_dec(v_name_939_);
v_a_1002_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_961_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_961_);
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
lean_dec_ref(v_lhs_955_);
lean_del_object(v___x_950_);
lean_dec(v_levelParams_948_);
lean_dec(v_name_939_);
v_a_1010_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_956_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_956_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1020_, lean_object* v_name_1021_, lean_object* v_xs_1022_, lean_object* v_body_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1020_, v_name_1021_, v_xs_1022_, v_body_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_xs_1022_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1030_, lean_object* v_info_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_toConstantVal_1037_; lean_object* v_value_1038_; lean_object* v___f_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; 
v_toConstantVal_1037_ = lean_ctor_get(v_info_1031_, 0);
lean_inc_ref(v_toConstantVal_1037_);
v_value_1038_ = lean_ctor_get(v_info_1031_, 1);
lean_inc_ref(v_value_1038_);
lean_dec_ref(v_info_1031_);
v___f_1039_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1039_, 0, v_toConstantVal_1037_);
lean_closure_set(v___f_1039_, 1, v_name_1030_);
v___x_1040_ = 1;
v___x_1041_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1038_, v___f_1039_, v___x_1040_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1042_, lean_object* v_info_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1042_, v_info_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1050_, lean_object* v_name_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1060_; lean_object* v_env_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1060_ = lean_st_ref_get(v_a_1055_);
v_env_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc_ref(v_env_1061_);
lean_dec(v___x_1060_);
v___x_1062_ = 0;
lean_inc(v_declName_1050_);
v___x_1063_ = l_Lean_Environment_find_x3f(v_env_1061_, v_declName_1050_, v___x_1062_);
if (lean_obj_tag(v___x_1063_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1091_; 
v_val_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1091_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1091_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
if (lean_obj_tag(v_val_1064_) == 1)
{
lean_object* v_val_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_val_1068_ = lean_ctor_get(v_val_1064_, 0);
lean_inc_ref(v_val_1068_);
lean_dec_ref_known(v_val_1064_, 1);
lean_inc_n(v_name_1051_, 2);
v___x_1069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1069_, 0, v_name_1051_);
lean_closure_set(v___x_1069_, 1, v_val_1068_);
lean_inc(v_declName_1050_);
v___x_1070_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1070_, 0, lean_box(0));
lean_closure_set(v___x_1070_, 1, v_declName_1050_);
lean_closure_set(v___x_1070_, 2, v___x_1069_);
v___x_1071_ = l_Lean_Meta_realizeConst(v_declName_1050_, v_name_1051_, v___x_1070_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1081_; 
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_1071_, 0);
lean_dec(v_unused_1082_);
v___x_1073_ = v___x_1071_;
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v___x_1071_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v_name_1051_);
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_name_1051_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1076_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_del_object(v___x_1066_);
lean_dec(v_name_1051_);
v_a_1083_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1071_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1071_);
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
lean_del_object(v___x_1066_);
lean_dec(v_val_1064_);
lean_dec(v_name_1051_);
lean_dec(v_declName_1050_);
goto v___jp_1057_;
}
}
}
else
{
lean_dec(v___x_1063_);
lean_dec(v_name_1051_);
lean_dec(v_declName_1050_);
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1092_, lean_object* v_name_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1092_, v_name_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_i_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_array_get_size(v_keys_1100_);
v___x_1105_ = lean_nat_dec_lt(v_i_1102_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_dec(v_i_1102_);
v___x_1106_ = lean_box(0);
return v___x_1106_;
}
else
{
lean_object* v_k_x27_1107_; uint8_t v___x_1108_; 
v_k_x27_1107_ = lean_array_fget_borrowed(v_keys_1100_, v_i_1102_);
v___x_1108_ = lean_name_eq(v_k_1103_, v_k_x27_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_add(v_i_1102_, v___x_1109_);
lean_dec(v_i_1102_);
v_i_1102_ = v___x_1110_;
goto _start;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_array_fget_borrowed(v_vals_1101_, v_i_1102_);
lean_dec(v_i_1102_);
lean_inc(v___x_1112_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1114_, lean_object* v_vals_1115_, lean_object* v_i_1116_, lean_object* v_k_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1114_, v_vals_1115_, v_i_1116_, v_k_1117_);
lean_dec(v_k_1117_);
lean_dec_ref(v_vals_1115_);
lean_dec_ref(v_keys_1114_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1119_, size_t v_x_1120_, lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1119_) == 0)
{
lean_object* v_es_1122_; lean_object* v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; lean_object* v_j_1126_; lean_object* v___x_1127_; 
v_es_1122_ = lean_ctor_get(v_x_1119_, 0);
v___x_1123_ = lean_box(2);
v___x_1124_ = ((size_t)31ULL);
v___x_1125_ = lean_usize_land(v_x_1120_, v___x_1124_);
v_j_1126_ = lean_usize_to_nat(v___x_1125_);
v___x_1127_ = lean_array_get_borrowed(v___x_1123_, v_es_1122_, v_j_1126_);
lean_dec(v_j_1126_);
switch(lean_obj_tag(v___x_1127_))
{
case 0:
{
lean_object* v_key_1128_; lean_object* v_val_1129_; uint8_t v___x_1130_; 
v_key_1128_ = lean_ctor_get(v___x_1127_, 0);
v_val_1129_ = lean_ctor_get(v___x_1127_, 1);
v___x_1130_ = lean_name_eq(v_x_1121_, v_key_1128_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; 
lean_inc(v_val_1129_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_val_1129_);
return v___x_1132_;
}
}
case 1:
{
lean_object* v_node_1133_; size_t v___x_1134_; size_t v___x_1135_; 
v_node_1133_ = lean_ctor_get(v___x_1127_, 0);
v___x_1134_ = ((size_t)5ULL);
v___x_1135_ = lean_usize_shift_right(v_x_1120_, v___x_1134_);
v_x_1119_ = v_node_1133_;
v_x_1120_ = v___x_1135_;
goto _start;
}
default: 
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_box(0);
return v___x_1137_;
}
}
}
else
{
lean_object* v_ks_1138_; lean_object* v_vs_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_ks_1138_ = lean_ctor_get(v_x_1119_, 0);
v_vs_1139_ = lean_ctor_get(v_x_1119_, 1);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1138_, v_vs_1139_, v___x_1140_, v_x_1121_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
size_t v_x_342__boxed_1145_; lean_object* v_res_1146_; 
v_x_342__boxed_1145_ = lean_unbox_usize(v_x_1143_);
lean_dec(v_x_1143_);
v_res_1146_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1142_, v_x_342__boxed_1145_, v_x_1144_);
lean_dec(v_x_1144_);
lean_dec_ref(v_x_1142_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
uint64_t v___y_1150_; 
if (lean_obj_tag(v_x_1148_) == 0)
{
uint64_t v___x_1153_; 
v___x_1153_ = 1723ULL;
v___y_1150_ = v___x_1153_;
goto v___jp_1149_;
}
else
{
uint64_t v_hash_1154_; 
v_hash_1154_ = lean_ctor_get_uint64(v_x_1148_, sizeof(void*)*2);
v___y_1150_ = v_hash_1154_;
goto v___jp_1149_;
}
v___jp_1149_:
{
size_t v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_uint64_to_usize(v___y_1150_);
v___x_1152_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1147_, v___x_1151_, v_x_1148_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1155_, v_x_1156_);
lean_dec(v_x_1156_);
lean_dec_ref(v_x_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_env_1163_; lean_object* v___x_1164_; lean_object* v_asyncMode_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1161_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1162_ = lean_st_ref_get(v_a_1159_);
v_env_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc_ref(v_env_1163_);
lean_dec(v___x_1162_);
v___x_1164_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1165_ = lean_ctor_get(v___x_1164_, 2);
v___x_1166_ = lean_box(0);
v___x_1167_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1161_, v___x_1164_, v_env_1163_, v_asyncMode_1165_, v___x_1166_);
v___x_1168_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1167_, v_thmName_1158_);
lean_dec(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec(v_thmName_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1174_, v_a_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_thmName_1179_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1185_, v_x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1188_, v_x_1189_, v_x_1190_);
lean_dec(v_x_1190_);
lean_dec_ref(v_x_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1192_, lean_object* v_x_1193_, size_t v_x_1194_, lean_object* v_x_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1193_, v_x_1194_, v_x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
size_t v_x_435__boxed_1201_; lean_object* v_res_1202_; 
v_x_435__boxed_1201_ = lean_unbox_usize(v_x_1199_);
lean_dec(v_x_1199_);
v_res_1202_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1197_, v_x_1198_, v_x_435__boxed_1201_, v_x_1200_);
lean_dec(v_x_1200_);
lean_dec_ref(v_x_1198_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1203_, lean_object* v_keys_1204_, lean_object* v_vals_1205_, lean_object* v_heq_1206_, lean_object* v_i_1207_, lean_object* v_k_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1204_, v_vals_1205_, v_i_1207_, v_k_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1210_, lean_object* v_keys_1211_, lean_object* v_vals_1212_, lean_object* v_heq_1213_, lean_object* v_i_1214_, lean_object* v_k_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1210_, v_keys_1211_, v_vals_1212_, v_heq_1213_, v_i_1214_, v_k_1215_);
lean_dec(v_k_1215_);
lean_dec_ref(v_vals_1212_);
lean_dec_ref(v_keys_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1217_, lean_object* v_i_1218_, lean_object* v_k_1219_){
_start:
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_array_get_size(v_keys_1217_);
v___x_1221_ = lean_nat_dec_lt(v_i_1218_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_dec(v_i_1218_);
return v___x_1221_;
}
else
{
lean_object* v_k_x27_1222_; uint8_t v___x_1223_; 
v_k_x27_1222_ = lean_array_fget_borrowed(v_keys_1217_, v_i_1218_);
v___x_1223_ = lean_name_eq(v_k_1219_, v_k_x27_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_add(v_i_1218_, v___x_1224_);
lean_dec(v_i_1218_);
v_i_1218_ = v___x_1225_;
goto _start;
}
else
{
lean_dec(v_i_1218_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1227_, lean_object* v_i_1228_, lean_object* v_k_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1227_, v_i_1228_, v_k_1229_);
lean_dec(v_k_1229_);
lean_dec_ref(v_keys_1227_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1232_, size_t v_x_1233_, lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_object* v_es_1235_; lean_object* v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; lean_object* v_j_1239_; lean_object* v___x_1240_; 
v_es_1235_ = lean_ctor_get(v_x_1232_, 0);
v___x_1236_ = lean_box(2);
v___x_1237_ = ((size_t)31ULL);
v___x_1238_ = lean_usize_land(v_x_1233_, v___x_1237_);
v_j_1239_ = lean_usize_to_nat(v___x_1238_);
v___x_1240_ = lean_array_get_borrowed(v___x_1236_, v_es_1235_, v_j_1239_);
lean_dec(v_j_1239_);
switch(lean_obj_tag(v___x_1240_))
{
case 0:
{
lean_object* v_key_1241_; uint8_t v___x_1242_; 
v_key_1241_ = lean_ctor_get(v___x_1240_, 0);
v___x_1242_ = lean_name_eq(v_x_1234_, v_key_1241_);
return v___x_1242_;
}
case 1:
{
lean_object* v_node_1243_; size_t v___x_1244_; size_t v___x_1245_; 
v_node_1243_ = lean_ctor_get(v___x_1240_, 0);
v___x_1244_ = ((size_t)5ULL);
v___x_1245_ = lean_usize_shift_right(v_x_1233_, v___x_1244_);
v_x_1232_ = v_node_1243_;
v_x_1233_ = v___x_1245_;
goto _start;
}
default: 
{
uint8_t v___x_1247_; 
v___x_1247_ = 0;
return v___x_1247_;
}
}
}
else
{
lean_object* v_ks_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_ks_1248_ = lean_ctor_get(v_x_1232_, 0);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1248_, v___x_1249_, v_x_1234_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
size_t v_x_326__boxed_1254_; uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_x_326__boxed_1254_ = lean_unbox_usize(v_x_1252_);
lean_dec(v_x_1252_);
v_res_1255_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1251_, v_x_326__boxed_1254_, v_x_1253_);
lean_dec(v_x_1253_);
lean_dec_ref(v_x_1251_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
uint64_t v___y_1260_; 
if (lean_obj_tag(v_x_1258_) == 0)
{
uint64_t v___x_1263_; 
v___x_1263_ = 1723ULL;
v___y_1260_ = v___x_1263_;
goto v___jp_1259_;
}
else
{
uint64_t v_hash_1264_; 
v_hash_1264_ = lean_ctor_get_uint64(v_x_1258_, sizeof(void*)*2);
v___y_1260_ = v_hash_1264_;
goto v___jp_1259_;
}
v___jp_1259_:
{
size_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = lean_uint64_to_usize(v___y_1260_);
v___x_1262_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1257_, v___x_1261_, v_x_1258_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_res_1267_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1265_, v_x_1266_);
lean_dec(v_x_1266_);
lean_dec_ref(v_x_1265_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_env_1274_; lean_object* v___x_1275_; lean_object* v_asyncMode_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1272_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1273_ = lean_st_ref_get(v_a_1270_);
v_env_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc_ref(v_env_1274_);
lean_dec(v___x_1273_);
v___x_1275_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1276_ = lean_ctor_get(v___x_1275_, 2);
v___x_1277_ = lean_box(0);
v___x_1278_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1272_, v___x_1275_, v_env_1274_, v_asyncMode_1276_, v___x_1277_);
v___x_1279_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1278_, v_thmName_1269_);
lean_dec(v___x_1278_);
v___x_1280_ = lean_box(v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec(v_thmName_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1286_, v_a_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_isEqnThm(v_thmName_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_thmName_1291_);
return v_res_1295_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1297_, v_x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1300_, v_x_1301_, v_x_1302_);
lean_dec(v_x_1302_);
lean_dec_ref(v_x_1301_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1305_, lean_object* v_x_1306_, size_t v_x_1307_, lean_object* v_x_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1306_, v_x_1307_, v_x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
size_t v_x_415__boxed_1314_; uint8_t v_res_1315_; lean_object* v_r_1316_; 
v_x_415__boxed_1314_ = lean_unbox_usize(v_x_1312_);
lean_dec(v_x_1312_);
v_res_1315_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1310_, v_x_1311_, v_x_415__boxed_1314_, v_x_1313_);
lean_dec(v_x_1313_);
lean_dec_ref(v_x_1311_);
v_r_1316_ = lean_box(v_res_1315_);
return v_r_1316_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1317_, lean_object* v_keys_1318_, lean_object* v_vals_1319_, lean_object* v_heq_1320_, lean_object* v_i_1321_, lean_object* v_k_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1318_, v_i_1321_, v_k_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1324_, lean_object* v_keys_1325_, lean_object* v_vals_1326_, lean_object* v_heq_1327_, lean_object* v_i_1328_, lean_object* v_k_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1324_, v_keys_1325_, v_vals_1326_, v_heq_1327_, v_i_1328_, v_k_1329_);
lean_dec(v_k_1329_);
lean_dec_ref(v_vals_1326_);
lean_dec_ref(v_keys_1325_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v_ks_1336_; lean_object* v_vs_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1361_; 
v_ks_1336_ = lean_ctor_get(v_x_1332_, 0);
v_vs_1337_ = lean_ctor_get(v_x_1332_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1332_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1339_ = v_x_1332_;
v_isShared_1340_ = v_isSharedCheck_1361_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_vs_1337_);
lean_inc(v_ks_1336_);
lean_dec(v_x_1332_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1361_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_array_get_size(v_ks_1336_);
v___x_1342_ = lean_nat_dec_lt(v_x_1333_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_dec(v_x_1333_);
v___x_1343_ = lean_array_push(v_ks_1336_, v_x_1334_);
v___x_1344_ = lean_array_push(v_vs_1337_, v_x_1335_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1344_);
lean_ctor_set(v___x_1339_, 0, v___x_1343_);
v___x_1346_ = v___x_1339_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
else
{
lean_object* v_k_x27_1348_; uint8_t v___x_1349_; 
v_k_x27_1348_ = lean_array_fget_borrowed(v_ks_1336_, v_x_1333_);
v___x_1349_ = lean_name_eq(v_x_1334_, v_k_x27_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1351_; 
if (v_isShared_1340_ == 0)
{
v___x_1351_ = v___x_1339_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_ks_1336_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_vs_1337_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_unsigned_to_nat(1u);
v___x_1353_ = lean_nat_add(v_x_1333_, v___x_1352_);
lean_dec(v_x_1333_);
v_x_1332_ = v___x_1351_;
v_x_1333_ = v___x_1353_;
goto _start;
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1356_ = lean_array_fset(v_ks_1336_, v_x_1333_, v_x_1334_);
v___x_1357_ = lean_array_fset(v_vs_1337_, v_x_1333_, v_x_1335_);
lean_dec(v_x_1333_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1357_);
lean_ctor_set(v___x_1339_, 0, v___x_1356_);
v___x_1359_ = v___x_1339_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1362_, lean_object* v_k_1363_, lean_object* v_v_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1362_, v___x_1365_, v_k_1363_, v_v_1364_);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1368_, size_t v_x_1369_, size_t v_x_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_){
_start:
{
if (lean_obj_tag(v_x_1368_) == 0)
{
lean_object* v_es_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v_j_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_es_1373_ = lean_ctor_get(v_x_1368_, 0);
v___x_1374_ = ((size_t)31ULL);
v___x_1375_ = lean_usize_land(v_x_1369_, v___x_1374_);
v_j_1376_ = lean_usize_to_nat(v___x_1375_);
v___x_1377_ = lean_array_get_size(v_es_1373_);
v___x_1378_ = lean_nat_dec_lt(v_j_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_dec(v_j_1376_);
lean_dec(v_x_1372_);
lean_dec(v_x_1371_);
return v_x_1368_;
}
else
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1417_; 
lean_inc_ref(v_es_1373_);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_x_1368_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_x_1368_, 0);
lean_dec(v_unused_1418_);
v___x_1380_ = v_x_1368_;
v_isShared_1381_ = v_isSharedCheck_1417_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v_x_1368_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1417_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_v_1382_; lean_object* v___x_1383_; lean_object* v_xs_x27_1384_; lean_object* v___y_1386_; 
v_v_1382_ = lean_array_fget(v_es_1373_, v_j_1376_);
v___x_1383_ = lean_box(0);
v_xs_x27_1384_ = lean_array_fset(v_es_1373_, v_j_1376_, v___x_1383_);
switch(lean_obj_tag(v_v_1382_))
{
case 0:
{
lean_object* v_key_1391_; lean_object* v_val_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1402_; 
v_key_1391_ = lean_ctor_get(v_v_1382_, 0);
v_val_1392_ = lean_ctor_get(v_v_1382_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_v_1382_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1394_ = v_v_1382_;
v_isShared_1395_ = v_isSharedCheck_1402_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_val_1392_);
lean_inc(v_key_1391_);
lean_dec(v_v_1382_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1402_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_name_eq(v_x_1371_, v_key_1391_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_del_object(v___x_1394_);
v___x_1397_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1391_, v_val_1392_, v_x_1371_, v_x_1372_);
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
v___y_1386_ = v___x_1398_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1400_; 
lean_dec(v_val_1392_);
lean_dec(v_key_1391_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v_x_1372_);
lean_ctor_set(v___x_1394_, 0, v_x_1371_);
v___x_1400_ = v___x_1394_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_x_1371_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_x_1372_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
v___y_1386_ = v___x_1400_;
goto v___jp_1385_;
}
}
}
}
case 1:
{
lean_object* v_node_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1415_; 
v_node_1403_ = lean_ctor_get(v_v_1382_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_v_1382_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1405_ = v_v_1382_;
v_isShared_1406_ = v_isSharedCheck_1415_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_node_1403_);
lean_dec(v_v_1382_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1415_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
size_t v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1407_ = ((size_t)5ULL);
v___x_1408_ = lean_usize_shift_right(v_x_1369_, v___x_1407_);
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_x_1370_, v___x_1409_);
v___x_1411_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1403_, v___x_1408_, v___x_1410_, v_x_1371_, v_x_1372_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1411_);
v___x_1413_ = v___x_1405_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
v___y_1386_ = v___x_1413_;
goto v___jp_1385_;
}
}
}
default: 
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_x_1371_);
lean_ctor_set(v___x_1416_, 1, v_x_1372_);
v___y_1386_ = v___x_1416_;
goto v___jp_1385_;
}
}
v___jp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_array_fset(v_xs_x27_1384_, v_j_1376_, v___y_1386_);
lean_dec(v_j_1376_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1387_);
v___x_1389_ = v___x_1380_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
else
{
lean_object* v_ks_1419_; lean_object* v_vs_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1438_; 
v_ks_1419_ = lean_ctor_get(v_x_1368_, 0);
v_vs_1420_ = lean_ctor_get(v_x_1368_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1368_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1422_ = v_x_1368_;
v_isShared_1423_ = v_isSharedCheck_1438_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_vs_1420_);
lean_inc(v_ks_1419_);
lean_dec(v_x_1368_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1438_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_ks_1419_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_vs_1420_);
v___x_1425_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v_newNode_1426_; size_t v___x_1427_; uint8_t v___x_1428_; 
v_newNode_1426_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1425_, v_x_1371_, v_x_1372_);
v___x_1427_ = ((size_t)7ULL);
v___x_1428_ = lean_usize_dec_le(v___x_1427_, v_x_1370_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1426_);
v___x_1430_ = lean_unsigned_to_nat(4u);
v___x_1431_ = lean_nat_dec_lt(v___x_1429_, v___x_1430_);
lean_dec(v___x_1429_);
if (v___x_1431_ == 0)
{
lean_object* v_ks_1432_; lean_object* v_vs_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v_ks_1432_ = lean_ctor_get(v_newNode_1426_, 0);
lean_inc_ref(v_ks_1432_);
v_vs_1433_ = lean_ctor_get(v_newNode_1426_, 1);
lean_inc_ref(v_vs_1433_);
lean_dec_ref(v_newNode_1426_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1436_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1370_, v_ks_1432_, v_vs_1433_, v___x_1434_, v___x_1435_);
lean_dec_ref(v_vs_1433_);
lean_dec_ref(v_ks_1432_);
return v___x_1436_;
}
else
{
return v_newNode_1426_;
}
}
else
{
return v_newNode_1426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1439_, lean_object* v_keys_1440_, lean_object* v_vals_1441_, lean_object* v_i_1442_, lean_object* v_entries_1443_){
_start:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_array_get_size(v_keys_1440_);
v___x_1445_ = lean_nat_dec_lt(v_i_1442_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec(v_i_1442_);
return v_entries_1443_;
}
else
{
lean_object* v_k_1446_; lean_object* v_v_1447_; uint64_t v___y_1449_; 
v_k_1446_ = lean_array_fget_borrowed(v_keys_1440_, v_i_1442_);
v_v_1447_ = lean_array_fget_borrowed(v_vals_1441_, v_i_1442_);
if (lean_obj_tag(v_k_1446_) == 0)
{
uint64_t v___x_1460_; 
v___x_1460_ = 1723ULL;
v___y_1449_ = v___x_1460_;
goto v___jp_1448_;
}
else
{
uint64_t v_hash_1461_; 
v_hash_1461_ = lean_ctor_get_uint64(v_k_1446_, sizeof(void*)*2);
v___y_1449_ = v_hash_1461_;
goto v___jp_1448_;
}
v___jp_1448_:
{
size_t v_h_1450_; size_t v___x_1451_; lean_object* v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; size_t v_h_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_h_1450_ = lean_uint64_to_usize(v___y_1449_);
v___x_1451_ = ((size_t)5ULL);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_sub(v_depth_1439_, v___x_1453_);
v___x_1455_ = lean_usize_mul(v___x_1451_, v___x_1454_);
v_h_1456_ = lean_usize_shift_right(v_h_1450_, v___x_1455_);
v___x_1457_ = lean_nat_add(v_i_1442_, v___x_1452_);
lean_dec(v_i_1442_);
lean_inc(v_v_1447_);
lean_inc(v_k_1446_);
v___x_1458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1443_, v_h_1456_, v_depth_1439_, v_k_1446_, v_v_1447_);
v_i_1442_ = v___x_1457_;
v_entries_1443_ = v___x_1458_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1462_, lean_object* v_keys_1463_, lean_object* v_vals_1464_, lean_object* v_i_1465_, lean_object* v_entries_1466_){
_start:
{
size_t v_depth_boxed_1467_; lean_object* v_res_1468_; 
v_depth_boxed_1467_ = lean_unbox_usize(v_depth_1462_);
lean_dec(v_depth_1462_);
v_res_1468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1467_, v_keys_1463_, v_vals_1464_, v_i_1465_, v_entries_1466_);
lean_dec_ref(v_vals_1464_);
lean_dec_ref(v_keys_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
size_t v_x_632__boxed_1474_; size_t v_x_633__boxed_1475_; lean_object* v_res_1476_; 
v_x_632__boxed_1474_ = lean_unbox_usize(v_x_1470_);
lean_dec(v_x_1470_);
v_x_633__boxed_1475_ = lean_unbox_usize(v_x_1471_);
lean_dec(v_x_1471_);
v_res_1476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1469_, v_x_632__boxed_1474_, v_x_633__boxed_1475_, v_x_1472_, v_x_1473_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
uint64_t v___y_1481_; 
if (lean_obj_tag(v_x_1478_) == 0)
{
uint64_t v___x_1485_; 
v___x_1485_ = 1723ULL;
v___y_1481_ = v___x_1485_;
goto v___jp_1480_;
}
else
{
uint64_t v_hash_1486_; 
v_hash_1486_ = lean_ctor_get_uint64(v_x_1478_, sizeof(void*)*2);
v___y_1481_ = v_hash_1486_;
goto v___jp_1480_;
}
v___jp_1480_:
{
size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_uint64_to_usize(v___y_1481_);
v___x_1483_ = ((size_t)1ULL);
v___x_1484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1477_, v___x_1482_, v___x_1483_, v_x_1478_, v_x_1479_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1487_, lean_object* v_as_1488_, size_t v_i_1489_, size_t v_stop_1490_, lean_object* v_b_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_eq(v_i_1489_, v_stop_1490_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; 
v___x_1493_ = lean_array_uget_borrowed(v_as_1488_, v_i_1489_);
lean_inc(v_declName_1487_);
lean_inc(v___x_1493_);
v___x_1494_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1491_, v___x_1493_, v_declName_1487_);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_add(v_i_1489_, v___x_1495_);
v_i_1489_ = v___x_1496_;
v_b_1491_ = v___x_1494_;
goto _start;
}
else
{
lean_dec(v_declName_1487_);
return v_b_1491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1498_, lean_object* v_as_1499_, lean_object* v_i_1500_, lean_object* v_stop_1501_, lean_object* v_b_1502_){
_start:
{
size_t v_i_boxed_1503_; size_t v_stop_boxed_1504_; lean_object* v_res_1505_; 
v_i_boxed_1503_ = lean_unbox_usize(v_i_1500_);
lean_dec(v_i_1500_);
v_stop_boxed_1504_ = lean_unbox_usize(v_stop_1501_);
lean_dec(v_stop_1501_);
v_res_1505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1498_, v_as_1499_, v_i_boxed_1503_, v_stop_boxed_1504_, v_b_1502_);
lean_dec_ref(v_as_1499_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1506_, lean_object* v_declName_1507_, lean_object* v_s_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_get_size(v_eqThms_1506_);
v___x_1511_ = lean_nat_dec_lt(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_dec(v_declName_1507_);
return v_s_1508_;
}
else
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_le(v___x_1510_, v___x_1510_);
if (v___x_1512_ == 0)
{
if (v___x_1511_ == 0)
{
lean_dec(v_declName_1507_);
return v_s_1508_;
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_of_nat(v___x_1510_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1507_, v_eqThms_1506_, v___x_1513_, v___x_1514_, v_s_1508_);
return v___x_1515_;
}
}
else
{
size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_of_nat(v___x_1510_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1507_, v_eqThms_1506_, v___x_1516_, v___x_1517_, v_s_1508_);
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1519_, lean_object* v_declName_1520_, lean_object* v_s_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1519_, v_declName_1520_, v_s_1521_);
lean_dec_ref(v_eqThms_1519_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1523_, lean_object* v_eqThms_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v_env_1529_; lean_object* v_nextMacroScope_1530_; lean_object* v_ngen_1531_; lean_object* v_auxDeclNGen_1532_; lean_object* v_traceState_1533_; lean_object* v_recordedDeps_1534_; lean_object* v_messages_1535_; lean_object* v_infoState_1536_; lean_object* v_snapshotTasks_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1552_; 
v___f_1527_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1527_, 0, v_eqThms_1524_);
lean_closure_set(v___f_1527_, 1, v_declName_1523_);
v___x_1528_ = lean_st_ref_take(v_a_1525_);
v_env_1529_ = lean_ctor_get(v___x_1528_, 0);
v_nextMacroScope_1530_ = lean_ctor_get(v___x_1528_, 1);
v_ngen_1531_ = lean_ctor_get(v___x_1528_, 2);
v_auxDeclNGen_1532_ = lean_ctor_get(v___x_1528_, 3);
v_traceState_1533_ = lean_ctor_get(v___x_1528_, 4);
v_recordedDeps_1534_ = lean_ctor_get(v___x_1528_, 6);
v_messages_1535_ = lean_ctor_get(v___x_1528_, 7);
v_infoState_1536_ = lean_ctor_get(v___x_1528_, 8);
v_snapshotTasks_1537_ = lean_ctor_get(v___x_1528_, 9);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; 
v_unused_1553_ = lean_ctor_get(v___x_1528_, 5);
lean_dec(v_unused_1553_);
v___x_1539_ = v___x_1528_;
v_isShared_1540_ = v_isSharedCheck_1552_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_snapshotTasks_1537_);
lean_inc(v_infoState_1536_);
lean_inc(v_messages_1535_);
lean_inc(v_recordedDeps_1534_);
lean_inc(v_traceState_1533_);
lean_inc(v_auxDeclNGen_1532_);
lean_inc(v_ngen_1531_);
lean_inc(v_nextMacroScope_1530_);
lean_inc(v_env_1529_);
lean_dec(v___x_1528_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1552_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v_asyncMode_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1541_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1542_ = lean_ctor_get(v___x_1541_, 2);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_box(0);
v___x_1545_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1541_, v_env_1529_, v___f_1527_, v_asyncMode_1542_, v___x_1544_);
v___x_1546_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 5, v___x_1546_);
lean_ctor_set(v___x_1539_, 0, v___x_1545_);
v___x_1548_ = v___x_1539_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_nextMacroScope_1530_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_ngen_1531_);
lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_auxDeclNGen_1532_);
lean_ctor_set(v_reuseFailAlloc_1551_, 4, v_traceState_1533_);
lean_ctor_set(v_reuseFailAlloc_1551_, 5, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1551_, 6, v_recordedDeps_1534_);
lean_ctor_set(v_reuseFailAlloc_1551_, 7, v_messages_1535_);
lean_ctor_set(v_reuseFailAlloc_1551_, 8, v_infoState_1536_);
lean_ctor_set(v_reuseFailAlloc_1551_, 9, v_snapshotTasks_1537_);
v___x_1548_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_st_ref_put(v_a_1525_, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1543_);
return v___x_1550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1554_, lean_object* v_eqThms_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1554_, v_eqThms_1555_, v_a_1556_);
lean_dec(v_a_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1559_, lean_object* v_eqThms_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1559_, v_eqThms_1560_, v_a_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1565_, lean_object* v_eqThms_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1565_, v_eqThms_1566_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1572_, v_x_1573_, v_x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1576_, lean_object* v_x_1577_, size_t v_x_1578_, size_t v_x_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1577_, v_x_1578_, v_x_1579_, v_x_1580_, v_x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
size_t v_x_894__boxed_1589_; size_t v_x_895__boxed_1590_; lean_object* v_res_1591_; 
v_x_894__boxed_1589_ = lean_unbox_usize(v_x_1585_);
lean_dec(v_x_1585_);
v_x_895__boxed_1590_ = lean_unbox_usize(v_x_1586_);
lean_dec(v_x_1586_);
v_res_1591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1583_, v_x_1584_, v_x_894__boxed_1589_, v_x_895__boxed_1590_, v_x_1587_, v_x_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1592_, lean_object* v_n_1593_, lean_object* v_k_1594_, lean_object* v_v_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1593_, v_k_1594_, v_v_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1597_, size_t v_depth_1598_, lean_object* v_keys_1599_, lean_object* v_vals_1600_, lean_object* v_heq_1601_, lean_object* v_i_1602_, lean_object* v_entries_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1598_, v_keys_1599_, v_vals_1600_, v_i_1602_, v_entries_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1605_, lean_object* v_depth_1606_, lean_object* v_keys_1607_, lean_object* v_vals_1608_, lean_object* v_heq_1609_, lean_object* v_i_1610_, lean_object* v_entries_1611_){
_start:
{
size_t v_depth_boxed_1612_; lean_object* v_res_1613_; 
v_depth_boxed_1612_ = lean_unbox_usize(v_depth_1606_);
lean_dec(v_depth_1606_);
v_res_1613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1605_, v_depth_boxed_1612_, v_keys_1607_, v_vals_1608_, v_heq_1609_, v_i_1610_, v_entries_1611_);
lean_dec_ref(v_vals_1608_);
lean_dec_ref(v_keys_1607_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1615_, v_x_1616_, v_x_1617_, v_x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1620_, lean_object* v_env_1621_, lean_object* v_idx_1622_, lean_object* v_eqs_1623_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v_nextEq_1630_; uint8_t v___x_1631_; 
v___x_1625_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = lean_nat_add(v_idx_1622_, v___x_1626_);
lean_dec(v_idx_1622_);
lean_inc(v___x_1627_);
v___x_1628_ = l_Nat_reprFast(v___x_1627_);
v___x_1629_ = lean_string_append(v___x_1625_, v___x_1628_);
lean_dec_ref(v___x_1628_);
lean_inc(v_declName_1620_);
lean_inc_ref(v_env_1621_);
v_nextEq_1630_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1621_, v_declName_1620_, v___x_1629_);
v___x_1631_ = l_Lean_Environment_containsOnBranch(v_env_1621_, v_nextEq_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_dec(v_nextEq_1630_);
lean_dec(v___x_1627_);
lean_dec_ref(v_env_1621_);
lean_dec(v_declName_1620_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_eqs_1623_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_array_push(v_eqs_1623_, v_nextEq_1630_);
v_idx_1622_ = v___x_1627_;
v_eqs_1623_ = v___x_1633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1635_, lean_object* v_env_1636_, lean_object* v_idx_1637_, lean_object* v_eqs_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1635_, v_env_1636_, v_idx_1637_, v_eqs_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1641_, lean_object* v_env_1642_, lean_object* v_idx_1643_, lean_object* v_eqs_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1641_, v_env_1642_, v_idx_1643_, v_eqs_1644_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1651_, lean_object* v_env_1652_, lean_object* v_idx_1653_, lean_object* v_eqs_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1651_, v_env_1652_, v_idx_1653_, v_eqs_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v_env_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1664_ = lean_st_ref_get(v_a_1662_);
v_env_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_ref_n(v_env_1665_, 3);
lean_dec(v___x_1664_);
v___x_1666_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1661_);
v___x_1667_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1665_, v_declName_1661_, v___x_1666_);
v___x_1668_ = 1;
lean_inc(v___x_1667_);
v___x_1669_ = l_Lean_Environment_contains(v_env_1665_, v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v___x_1667_);
lean_dec_ref(v_env_1665_);
lean_dec(v_declName_1661_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1672_ = lean_unsigned_to_nat(1u);
v___x_1673_ = lean_mk_empty_array_with_capacity(v___x_1672_);
v___x_1674_ = lean_array_push(v___x_1673_, v___x_1667_);
lean_inc(v_declName_1661_);
v___x_1675_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1661_, v_env_1665_, v___x_1672_, v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1685_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_n(v_a_1676_, 2);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1661_, v_a_1676_, v_a_1662_);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v___x_1677_, 0);
lean_dec(v_unused_1686_);
v___x_1679_ = v___x_1677_;
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
else
{
lean_dec(v___x_1677_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_a_1676_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_declName_1661_);
v_a_1687_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1675_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1675_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1695_, v_a_1696_);
lean_dec(v_a_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1699_, v_a_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1713_, lean_object* v_localInsts_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1713_, v_localInsts_1714_, v_x_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1721_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1721_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1738_, lean_object* v_localInsts_1739_, lean_object* v_x_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1738_, v_localInsts_1739_, v_x_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1747_, lean_object* v_lctx_1748_, lean_object* v_localInsts_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1748_, v_localInsts_1749_, v_x_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_lctx_1758_, lean_object* v_localInsts_1759_, lean_object* v_x_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1757_, v_lctx_1758_, v_localInsts_1759_, v_x_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1770_, lean_object* v_as_x27_1771_, lean_object* v_b_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
if (lean_obj_tag(v_as_x27_1771_) == 0)
{
lean_object* v___x_1778_; 
lean_dec(v_declName_1770_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_b_1772_);
return v___x_1778_;
}
else
{
lean_object* v_head_1779_; lean_object* v_tail_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v_b_1772_);
v_head_1779_ = lean_ctor_get(v_as_x27_1771_, 0);
v_tail_1780_ = lean_ctor_get(v_as_x27_1771_, 1);
v___x_1781_ = lean_box(0);
v___x_1782_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1779_);
lean_inc(v___y_1776_);
lean_inc_ref(v___y_1775_);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1773_);
lean_inc(v_declName_1770_);
v___x_1783_ = lean_apply_6(v_head_1779_, v_declName_1770_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, lean_box(0));
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
if (lean_obj_tag(v_a_1784_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1795_; 
v_val_1785_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_val_1785_);
v___x_1786_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1770_, v_val_1785_, v___y_1776_);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v___x_1786_, 0);
lean_dec(v_unused_1796_);
v___x_1788_ = v___x_1786_;
v_isShared_1789_ = v_isSharedCheck_1795_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v___x_1786_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1795_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1784_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1781_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1791_);
v___x_1793_ = v___x_1788_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_dec(v_a_1784_);
v_as_x27_1771_ = v_tail_1780_;
v_b_1772_ = v___x_1782_;
goto _start;
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_declName_1770_);
v_a_1798_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1783_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1783_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1806_, lean_object* v_as_x27_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1806_, v_as_x27_1807_, v_b_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_as_x27_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
lean_inc(v_declName_1815_);
v___x_1821_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1859_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1859_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1859_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_unbox(v_a_1822_);
lean_dec(v_a_1822_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_dec(v_declName_1815_);
v___x_1827_ = lean_box(0);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
else
{
lean_object* v___x_1831_; 
lean_del_object(v___x_1824_);
lean_inc(v_declName_1815_);
v___x_1831_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1815_, v___y_1819_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
if (lean_obj_tag(v_a_1832_) == 1)
{
lean_dec(v_declName_1815_);
return v___x_1831_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1834_ = lean_st_ref_get(v___x_1833_);
v___x_1835_ = lean_box(0);
v___x_1836_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1837_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1815_, v___x_1834_, v___x_1836_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___x_1834_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1850_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1850_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1850_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_fst_1842_; 
v_fst_1842_ = lean_ctor_get(v_a_1838_, 0);
lean_inc(v_fst_1842_);
lean_dec(v_a_1838_);
if (lean_obj_tag(v_fst_1842_) == 0)
{
lean_object* v___x_1844_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1835_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1835_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
lean_object* v_val_1846_; lean_object* v___x_1848_; 
v_val_1846_ = lean_ctor_get(v_fst_1842_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_fst_1842_, 1);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_val_1846_);
v___x_1848_ = v___x_1840_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_val_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1837_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1837_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
else
{
lean_dec(v_declName_1815_);
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_declName_1815_);
v_a_1860_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1821_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1821_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = lean_box(1);
v___x_1878_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1879_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___x_1878_);
lean_ctor_set(v___x_1880_, 2, v___x_1877_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___f_1889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1889_, 0, v_declName_1883_);
v___x_1890_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1891_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1892_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1890_, v___x_1891_, v___f_1889_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1900_, lean_object* v_as_1901_, lean_object* v_as_x27_1902_, lean_object* v_b_1903_, lean_object* v_a_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1900_, v_as_x27_1902_, v_b_1903_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1911_, lean_object* v_as_1912_, lean_object* v_as_x27_1913_, lean_object* v_b_1914_, lean_object* v_a_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1911_, v_as_1912_, v_as_x27_1913_, v_b_1914_, v_a_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v_as_x27_1913_);
lean_dec(v_as_1912_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1928_ = lean_unsigned_to_nat(32u);
v___x_1929_ = lean_mk_empty_array_with_capacity(v___x_1928_);
lean_dec_ref(v___x_1929_);
v___x_1930_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1931_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1922_);
v___x_1932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1932_, 0, v_declName_1922_);
v___x_1933_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1933_, 0, lean_box(0));
lean_closure_set(v___x_1933_, 1, v_declName_1922_);
lean_closure_set(v___x_1933_, 2, v___x_1932_);
v___x_1934_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1930_, v___x_1931_, v___x_1933_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_1942_, lean_object* v_opt_1943_){
_start:
{
lean_object* v_name_1944_; lean_object* v_defValue_1945_; lean_object* v_map_1946_; lean_object* v___x_1947_; 
v_name_1944_ = lean_ctor_get(v_opt_1943_, 0);
v_defValue_1945_ = lean_ctor_get(v_opt_1943_, 1);
v_map_1946_ = lean_ctor_get(v_opts_1942_, 0);
v___x_1947_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1946_, v_name_1944_);
if (lean_obj_tag(v___x_1947_) == 0)
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_unbox(v_defValue_1945_);
return v___x_1948_;
}
else
{
lean_object* v_val_1949_; 
v_val_1949_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_val_1949_);
lean_dec_ref_known(v___x_1947_, 1);
if (lean_obj_tag(v_val_1949_) == 1)
{
uint8_t v_v_1950_; 
v_v_1950_ = lean_ctor_get_uint8(v_val_1949_, 0);
lean_dec_ref_known(v_val_1949_, 0);
return v_v_1950_;
}
else
{
uint8_t v___x_1951_; 
lean_dec(v_val_1949_);
v___x_1951_ = lean_unbox(v_defValue_1945_);
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_1952_, lean_object* v_opt_1953_){
_start:
{
uint8_t v_res_1954_; lean_object* v_r_1955_; 
v_res_1954_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_1952_, v_opt_1953_);
lean_dec_ref(v_opt_1953_);
lean_dec_ref(v_opts_1952_);
v_r_1955_ = lean_box(v_res_1954_);
return v_r_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_1956_, lean_object* v_as_1957_, size_t v_sz_1958_, size_t v_i_1959_, lean_object* v_b_1960_){
_start:
{
lean_object* v_a_1963_; uint8_t v___x_1967_; 
v___x_1967_ = lean_usize_dec_lt(v_i_1959_, v_sz_1958_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_b_1960_);
return v___x_1968_;
}
else
{
lean_object* v_a_1969_; lean_object* v_defValue_1970_; uint8_t v___x_1971_; uint8_t v___y_1985_; uint8_t v___x_1986_; 
v_a_1969_ = lean_array_uget(v_as_1957_, v_i_1959_);
v_defValue_1970_ = lean_ctor_get(v_a_1969_, 1);
v___x_1971_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_1956_, v_a_1969_);
v___x_1986_ = lean_unbox(v_defValue_1970_);
if (v___x_1986_ == 0)
{
if (v___x_1971_ == 0)
{
v___y_1985_ = v___x_1967_;
goto v___jp_1984_;
}
else
{
goto v___jp_1972_;
}
}
else
{
v___y_1985_ = v___x_1971_;
goto v___jp_1984_;
}
v___jp_1972_:
{
lean_object* v_name_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1982_; 
v_name_1973_ = lean_ctor_get(v_a_1969_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_a_1969_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_a_1969_, 1);
lean_dec(v_unused_1983_);
v___x_1975_ = v_a_1969_;
v_isShared_1976_ = v_isSharedCheck_1982_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_name_1973_);
lean_dec(v_a_1969_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1982_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1977_, 0, v___x_1971_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v___x_1977_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_name_1973_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_array_push(v_b_1960_, v___x_1979_);
v_a_1963_ = v___x_1980_;
goto v___jp_1962_;
}
}
}
v___jp_1984_:
{
if (v___y_1985_ == 0)
{
goto v___jp_1972_;
}
else
{
lean_dec(v_a_1969_);
v_a_1963_ = v_b_1960_;
goto v___jp_1962_;
}
}
}
v___jp_1962_:
{
size_t v___x_1964_; size_t v___x_1965_; 
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1959_, v___x_1964_);
v_i_1959_ = v___x_1965_;
v_b_1960_ = v_a_1963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_1987_, lean_object* v_as_1988_, lean_object* v_sz_1989_, lean_object* v_i_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_sz_boxed_1993_; size_t v_i_boxed_1994_; lean_object* v_res_1995_; 
v_sz_boxed_1993_ = lean_unbox_usize(v_sz_1989_);
lean_dec(v_sz_1989_);
v_i_boxed_1994_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_1987_, v_as_1988_, v_sz_boxed_1993_, v_i_boxed_1994_, v_b_1991_);
lean_dec_ref(v_as_1988_);
lean_dec_ref(v___x_1987_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; lean_object* v_env_2003_; lean_object* v___x_2004_; lean_object* v_toCold_2005_; lean_object* v_mctx_2006_; lean_object* v_lctx_2007_; lean_object* v_options_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2002_ = lean_st_ref_get(v___y_2000_);
v_env_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_ref(v_env_2003_);
lean_dec(v___x_2002_);
v___x_2004_ = lean_st_ref_get(v___y_1998_);
v_toCold_2005_ = lean_ctor_get(v___y_1999_, 0);
v_mctx_2006_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref(v_mctx_2006_);
lean_dec(v___x_2004_);
v_lctx_2007_ = lean_ctor_get(v___y_1997_, 2);
v_options_2008_ = lean_ctor_get(v_toCold_2005_, 2);
lean_inc_ref(v_options_2008_);
lean_inc_ref(v_lctx_2007_);
v___x_2009_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2009_, 0, v_env_2003_);
lean_ctor_set(v___x_2009_, 1, v_mctx_2006_);
lean_ctor_set(v___x_2009_, 2, v_lctx_2007_);
lean_ctor_set(v___x_2009_, 3, v_options_2008_);
v___x_2010_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v_msgData_1996_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2018_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2019_; double v___x_2020_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = lean_float_of_nat(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2024_, lean_object* v_msg_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_ref_2031_; lean_object* v___x_2032_; lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2078_; 
v_ref_2031_ = lean_ctor_get(v___y_2028_, 2);
v___x_2032_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2078_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2078_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v_traceState_2038_; lean_object* v_env_2039_; lean_object* v_nextMacroScope_2040_; lean_object* v_ngen_2041_; lean_object* v_auxDeclNGen_2042_; lean_object* v_cache_2043_; lean_object* v_recordedDeps_2044_; lean_object* v_messages_2045_; lean_object* v_infoState_2046_; lean_object* v_snapshotTasks_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2077_; 
v___x_2037_ = lean_st_ref_take(v___y_2029_);
v_traceState_2038_ = lean_ctor_get(v___x_2037_, 4);
v_env_2039_ = lean_ctor_get(v___x_2037_, 0);
v_nextMacroScope_2040_ = lean_ctor_get(v___x_2037_, 1);
v_ngen_2041_ = lean_ctor_get(v___x_2037_, 2);
v_auxDeclNGen_2042_ = lean_ctor_get(v___x_2037_, 3);
v_cache_2043_ = lean_ctor_get(v___x_2037_, 5);
v_recordedDeps_2044_ = lean_ctor_get(v___x_2037_, 6);
v_messages_2045_ = lean_ctor_get(v___x_2037_, 7);
v_infoState_2046_ = lean_ctor_get(v___x_2037_, 8);
v_snapshotTasks_2047_ = lean_ctor_get(v___x_2037_, 9);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2049_ = v___x_2037_;
v_isShared_2050_ = v_isSharedCheck_2077_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_snapshotTasks_2047_);
lean_inc(v_infoState_2046_);
lean_inc(v_messages_2045_);
lean_inc(v_recordedDeps_2044_);
lean_inc(v_cache_2043_);
lean_inc(v_traceState_2038_);
lean_inc(v_auxDeclNGen_2042_);
lean_inc(v_ngen_2041_);
lean_inc(v_nextMacroScope_2040_);
lean_inc(v_env_2039_);
lean_dec(v___x_2037_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2077_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
uint64_t v_tid_2051_; lean_object* v_traces_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2076_; 
v_tid_2051_ = lean_ctor_get_uint64(v_traceState_2038_, sizeof(void*)*1);
v_traces_2052_ = lean_ctor_get(v_traceState_2038_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_traceState_2038_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2054_ = v_traceState_2038_;
v_isShared_2055_ = v_isSharedCheck_2076_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_traces_2052_);
lean_dec(v_traceState_2038_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2076_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; double v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2059_ = 0;
v___x_2060_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2061_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2061_, 0, v_cls_2024_);
lean_ctor_set(v___x_2061_, 1, v___x_2057_);
lean_ctor_set(v___x_2061_, 2, v___x_2060_);
lean_ctor_set_float(v___x_2061_, sizeof(void*)*3, v___x_2058_);
lean_ctor_set_float(v___x_2061_, sizeof(void*)*3 + 8, v___x_2058_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*3 + 16, v___x_2059_);
v___x_2062_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2063_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
lean_ctor_set(v___x_2063_, 1, v_a_2033_);
lean_ctor_set(v___x_2063_, 2, v___x_2062_);
lean_inc(v_ref_2031_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_ref_2031_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = l_Lean_PersistentArray_push___redArg(v_traces_2052_, v___x_2064_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2065_);
v___x_2067_ = v___x_2054_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2065_);
lean_ctor_set_uint64(v_reuseFailAlloc_2075_, sizeof(void*)*1, v_tid_2051_);
v___x_2067_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 4, v___x_2067_);
v___x_2069_ = v___x_2049_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_env_2039_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_nextMacroScope_2040_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_ngen_2041_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_auxDeclNGen_2042_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v_cache_2043_);
lean_ctor_set(v_reuseFailAlloc_2074_, 6, v_recordedDeps_2044_);
lean_ctor_set(v_reuseFailAlloc_2074_, 7, v_messages_2045_);
lean_ctor_set(v_reuseFailAlloc_2074_, 8, v_infoState_2046_);
lean_ctor_set(v_reuseFailAlloc_2074_, 9, v_snapshotTasks_2047_);
v___x_2069_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_st_ref_put(v___y_2029_, v___x_2069_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2056_);
v___x_2072_ = v___x_2035_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2056_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2079_, lean_object* v_msg_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2079_, v_msg_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2086_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2089_; size_t v_sz_2090_; 
v___x_2089_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2090_ = lean_array_size(v___x_2089_);
return v_sz_2090_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2092_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
lean_ctor_set(v___x_2092_, 3, v___x_2091_);
lean_ctor_set(v___x_2092_, 4, v___x_2091_);
lean_ctor_set(v___x_2092_, 5, v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2101_ = l_Lean_Name_append(v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; size_t v_sz_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2111_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2108_);
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2114_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2115_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2111_, v___x_2114_, v_sz_2115_, v___x_2116_, v___x_2113_);
lean_dec_ref(v___x_2111_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2181_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2181_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2181_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v_a_2118_);
v___x_2167_ = lean_nat_dec_eq(v___x_2166_, v___x_2112_);
if (v___x_2167_ == 0)
{
lean_object* v_toCold_2168_; lean_object* v_options_2169_; uint8_t v_hasTrace_2170_; 
v_toCold_2168_ = lean_ctor_get(v_a_2108_, 0);
v_options_2169_ = lean_ctor_get(v_toCold_2168_, 2);
v_hasTrace_2170_ = lean_ctor_get_uint8(v_options_2169_, sizeof(void*)*1);
if (v_hasTrace_2170_ == 0)
{
v___y_2123_ = v_a_2107_;
v___y_2124_ = v_a_2109_;
goto v___jp_2122_;
}
else
{
lean_object* v_inheritedTraceOptions_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v_inheritedTraceOptions_2171_ = lean_ctor_get(v_toCold_2168_, 11);
v___x_2172_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2173_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2171_, v_options_2169_, v___x_2173_);
if (v___x_2174_ == 0)
{
v___y_2123_ = v_a_2107_;
v___y_2124_ = v_a_2109_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2105_);
v___x_2176_ = l_Lean_MessageData_ofName(v_declName_2105_);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2172_, v___x_2177_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_dec_ref_known(v___x_2178_, 1);
v___y_2123_ = v_a_2107_;
v___y_2124_ = v_a_2109_;
goto v___jp_2122_;
}
else
{
lean_del_object(v___x_2120_);
lean_dec(v_a_2118_);
lean_dec(v_declName_2105_);
return v___x_2178_;
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_del_object(v___x_2120_);
lean_dec(v_a_2118_);
lean_dec(v_declName_2105_);
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
return v___x_2180_;
}
v___jp_2122_:
{
lean_object* v___x_2125_; lean_object* v_env_2126_; lean_object* v_nextMacroScope_2127_; lean_object* v_ngen_2128_; lean_object* v_auxDeclNGen_2129_; lean_object* v_traceState_2130_; lean_object* v_recordedDeps_2131_; lean_object* v_messages_2132_; lean_object* v_infoState_2133_; lean_object* v_snapshotTasks_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2164_; 
v___x_2125_ = lean_st_ref_take(v___y_2124_);
v_env_2126_ = lean_ctor_get(v___x_2125_, 0);
v_nextMacroScope_2127_ = lean_ctor_get(v___x_2125_, 1);
v_ngen_2128_ = lean_ctor_get(v___x_2125_, 2);
v_auxDeclNGen_2129_ = lean_ctor_get(v___x_2125_, 3);
v_traceState_2130_ = lean_ctor_get(v___x_2125_, 4);
v_recordedDeps_2131_ = lean_ctor_get(v___x_2125_, 6);
v_messages_2132_ = lean_ctor_get(v___x_2125_, 7);
v_infoState_2133_ = lean_ctor_get(v___x_2125_, 8);
v_snapshotTasks_2134_ = lean_ctor_get(v___x_2125_, 9);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v___x_2125_, 5);
lean_dec(v_unused_2165_);
v___x_2136_ = v___x_2125_;
v_isShared_2137_ = v_isSharedCheck_2164_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snapshotTasks_2134_);
lean_inc(v_infoState_2133_);
lean_inc(v_messages_2132_);
lean_inc(v_recordedDeps_2131_);
lean_inc(v_traceState_2130_);
lean_inc(v_auxDeclNGen_2129_);
lean_inc(v_ngen_2128_);
lean_inc(v_nextMacroScope_2127_);
lean_inc(v_env_2126_);
lean_dec(v___x_2125_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2164_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2138_ = l_Lean_Meta_eqnOptionsExt;
v___x_2139_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2138_, v_env_2126_, v_declName_2105_, v_a_2118_);
v___x_2140_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 5, v___x_2140_);
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2142_ = v___x_2136_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_nextMacroScope_2127_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_ngen_2128_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_auxDeclNGen_2129_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_traceState_2130_);
lean_ctor_set(v_reuseFailAlloc_2163_, 5, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2163_, 6, v_recordedDeps_2131_);
lean_ctor_set(v_reuseFailAlloc_2163_, 7, v_messages_2132_);
lean_ctor_set(v_reuseFailAlloc_2163_, 8, v_infoState_2133_);
lean_ctor_set(v_reuseFailAlloc_2163_, 9, v_snapshotTasks_2134_);
v___x_2142_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_mctx_2145_; lean_object* v_zetaDeltaFVarIds_2146_; lean_object* v_postponed_2147_; lean_object* v_diag_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2161_; 
v___x_2143_ = lean_st_ref_put(v___y_2124_, v___x_2142_);
v___x_2144_ = lean_st_ref_take(v___y_2123_);
v_mctx_2145_ = lean_ctor_get(v___x_2144_, 0);
v_zetaDeltaFVarIds_2146_ = lean_ctor_get(v___x_2144_, 2);
v_postponed_2147_ = lean_ctor_get(v___x_2144_, 3);
v_diag_2148_ = lean_ctor_get(v___x_2144_, 4);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v___x_2144_, 1);
lean_dec(v_unused_2162_);
v___x_2150_ = v___x_2144_;
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_diag_2148_);
lean_inc(v_postponed_2147_);
lean_inc(v_zetaDeltaFVarIds_2146_);
lean_inc(v_mctx_2145_);
lean_dec(v___x_2144_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v___x_2153_);
v___x_2155_ = v___x_2150_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_mctx_2145_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_zetaDeltaFVarIds_2146_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_postponed_2147_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_diag_2148_);
v___x_2155_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_st_ref_put(v___y_2123_, v___x_2155_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2152_);
v___x_2158_ = v___x_2120_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2152_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
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
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_declName_2105_);
v_a_2182_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2117_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2117_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2197_, lean_object* v_as_2198_, size_t v_sz_2199_, size_t v_i_2200_, lean_object* v_b_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2197_, v_as_2198_, v_sz_2199_, v_i_2200_, v_b_2201_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2208_, lean_object* v_as_2209_, lean_object* v_sz_2210_, lean_object* v_i_2211_, lean_object* v_b_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2210_);
lean_dec(v_sz_2210_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2211_);
lean_dec(v_i_2211_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2208_, v_as_2209_, v_sz_boxed_2218_, v_i_boxed_2219_, v_b_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec_ref(v_as_2209_);
lean_dec_ref(v___x_2208_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_st_mk_ref(v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2227_){
_start:
{
uint8_t v___x_2229_; 
v___x_2229_ = l_Lean_initializing();
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec_ref(v_f_2227_);
v___x_2230_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2233_ = lean_st_ref_take(v___x_2232_);
v___x_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_f_2227_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = lean_st_ref_put(v___x_2232_, v___x_2234_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2243_, lean_object* v_as_x27_2244_, lean_object* v_b_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
if (lean_obj_tag(v_as_x27_2244_) == 0)
{
lean_object* v___x_2251_; 
lean_dec(v_declName_2243_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_b_2245_);
return v___x_2251_;
}
else
{
lean_object* v_head_2252_; lean_object* v_tail_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v_b_2245_);
v_head_2252_ = lean_ctor_get(v_as_x27_2244_, 0);
v_tail_2253_ = lean_ctor_get(v_as_x27_2244_, 1);
v___x_2254_ = lean_box(0);
v___x_2255_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2252_);
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v_declName_2243_);
v___x_2256_ = lean_apply_6(v_head_2252_, v_declName_2243_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, lean_box(0));
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2267_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2267_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2267_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
if (lean_obj_tag(v_a_2257_) == 1)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec(v_declName_2243_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v_a_2257_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v___x_2254_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2262_);
v___x_2264_ = v___x_2259_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_del_object(v___x_2259_);
lean_dec(v_a_2257_);
v_as_x27_2244_ = v_tail_2253_;
v_b_2245_ = v___x_2255_;
goto _start;
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_declName_2243_);
v_a_2268_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2256_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2256_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2276_, lean_object* v_as_x27_2277_, lean_object* v_b_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2276_, v_as_x27_2277_, v_b_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v_as_x27_2277_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2285_, lean_object* v_declName_2286_, uint8_t v_nonRec_2287_, lean_object* v___x_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2297_; lean_object* v_env_2298_; uint8_t v___x_2299_; uint8_t v___x_2300_; 
v___x_2297_ = lean_st_ref_get(v___y_2292_);
v_env_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc_ref(v_env_2298_);
lean_dec(v___x_2297_);
v___x_2299_ = 1;
lean_inc(v___x_2285_);
v___x_2300_ = l_Lean_Environment_contains(v_env_2298_, v___x_2285_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; 
lean_dec(v___x_2285_);
lean_inc(v_declName_2286_);
v___x_2301_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2286_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; uint8_t v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = lean_unbox(v_a_2302_);
lean_dec(v_a_2302_);
if (v___x_2303_ == 0)
{
lean_dec_ref(v___x_2288_);
lean_dec(v_declName_2286_);
goto v___jp_2294_;
}
else
{
lean_object* v___x_2304_; 
lean_inc(v_declName_2286_);
v___x_2304_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2286_, v___y_2292_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; uint8_t v___x_2306_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = lean_unbox(v_a_2305_);
lean_dec(v_a_2305_);
if (v___x_2306_ == 0)
{
if (v_nonRec_2287_ == 0)
{
lean_dec_ref(v___x_2288_);
lean_dec(v_declName_2286_);
goto v___jp_2294_;
}
else
{
lean_object* v___x_2307_; lean_object* v_env_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2307_ = lean_st_ref_get(v___y_2292_);
v_env_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc_ref(v_env_2308_);
lean_dec(v___x_2307_);
lean_inc(v_declName_2286_);
v___x_2309_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2308_, v_declName_2286_, v___x_2288_);
v___x_2310_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2286_, v___x_2309_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2310_;
}
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_dec_ref(v___x_2288_);
v___x_2311_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2312_ = lean_st_ref_get(v___x_2311_);
v___x_2313_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2314_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2286_, v___x_2312_, v___x_2313_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___x_2312_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2324_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2324_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2324_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v_fst_2319_; 
v_fst_2319_ = lean_ctor_get(v_a_2315_, 0);
lean_inc(v_fst_2319_);
lean_dec(v_a_2315_);
if (lean_obj_tag(v_fst_2319_) == 0)
{
lean_del_object(v___x_2317_);
goto v___jp_2294_;
}
else
{
lean_object* v_val_2320_; lean_object* v___x_2322_; 
v_val_2320_ = lean_ctor_get(v_fst_2319_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_fst_2319_, 1);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v_val_2320_);
v___x_2322_ = v___x_2317_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_val_2320_);
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
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
v_a_2325_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2314_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2314_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v___x_2288_);
lean_dec(v_declName_2286_);
v_a_2333_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2304_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2304_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v___x_2288_);
lean_dec(v_declName_2286_);
v_a_2341_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2301_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2301_);
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
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec_ref(v___x_2288_);
lean_dec(v_declName_2286_);
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2285_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
v___jp_2294_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2351_, lean_object* v_declName_2352_, lean_object* v_nonRec_2353_, lean_object* v___x_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v_nonRec_boxed_2360_; lean_object* v_res_2361_; 
v_nonRec_boxed_2360_ = lean_unbox(v_nonRec_2353_);
v_res_2361_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2351_, v_declName_2352_, v_nonRec_boxed_2360_, v___x_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_ref_2368_; lean_object* v___x_2369_; lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2378_; 
v_ref_2368_ = lean_ctor_get(v___y_2365_, 2);
v___x_2369_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
lean_inc(v_ref_2368_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_ref_2368_);
lean_ctor_set(v___x_2374_, 1, v_a_2370_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set_tag(v___x_2372_, 1);
lean_ctor_set(v___x_2372_, 0, v___x_2374_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2386_, uint8_t v_isExporting_2387_, lean_object* v___x_2388_, lean_object* v___y_2389_, lean_object* v___x_2390_, lean_object* v_a_x3f_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v_env_2394_; lean_object* v_nextMacroScope_2395_; lean_object* v_ngen_2396_; lean_object* v_auxDeclNGen_2397_; lean_object* v_traceState_2398_; lean_object* v_recordedDeps_2399_; lean_object* v_messages_2400_; lean_object* v_infoState_2401_; lean_object* v_snapshotTasks_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2427_; 
v___x_2393_ = lean_st_ref_take(v___y_2386_);
v_env_2394_ = lean_ctor_get(v___x_2393_, 0);
v_nextMacroScope_2395_ = lean_ctor_get(v___x_2393_, 1);
v_ngen_2396_ = lean_ctor_get(v___x_2393_, 2);
v_auxDeclNGen_2397_ = lean_ctor_get(v___x_2393_, 3);
v_traceState_2398_ = lean_ctor_get(v___x_2393_, 4);
v_recordedDeps_2399_ = lean_ctor_get(v___x_2393_, 6);
v_messages_2400_ = lean_ctor_get(v___x_2393_, 7);
v_infoState_2401_ = lean_ctor_get(v___x_2393_, 8);
v_snapshotTasks_2402_ = lean_ctor_get(v___x_2393_, 9);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v___x_2393_, 5);
lean_dec(v_unused_2428_);
v___x_2404_ = v___x_2393_;
v_isShared_2405_ = v_isSharedCheck_2427_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snapshotTasks_2402_);
lean_inc(v_infoState_2401_);
lean_inc(v_messages_2400_);
lean_inc(v_recordedDeps_2399_);
lean_inc(v_traceState_2398_);
lean_inc(v_auxDeclNGen_2397_);
lean_inc(v_ngen_2396_);
lean_inc(v_nextMacroScope_2395_);
lean_inc(v_env_2394_);
lean_dec(v___x_2393_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2427_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = l_Lean_Environment_setExporting(v_env_2394_, v_isExporting_2387_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 5, v___x_2388_);
lean_ctor_set(v___x_2404_, 0, v___x_2406_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_nextMacroScope_2395_);
lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_ngen_2396_);
lean_ctor_set(v_reuseFailAlloc_2426_, 3, v_auxDeclNGen_2397_);
lean_ctor_set(v_reuseFailAlloc_2426_, 4, v_traceState_2398_);
lean_ctor_set(v_reuseFailAlloc_2426_, 5, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2426_, 6, v_recordedDeps_2399_);
lean_ctor_set(v_reuseFailAlloc_2426_, 7, v_messages_2400_);
lean_ctor_set(v_reuseFailAlloc_2426_, 8, v_infoState_2401_);
lean_ctor_set(v_reuseFailAlloc_2426_, 9, v_snapshotTasks_2402_);
v___x_2408_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v_mctx_2411_; lean_object* v_zetaDeltaFVarIds_2412_; lean_object* v_postponed_2413_; lean_object* v_diag_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2424_; 
v___x_2409_ = lean_st_ref_put(v___y_2386_, v___x_2408_);
v___x_2410_ = lean_st_ref_take(v___y_2389_);
v_mctx_2411_ = lean_ctor_get(v___x_2410_, 0);
v_zetaDeltaFVarIds_2412_ = lean_ctor_get(v___x_2410_, 2);
v_postponed_2413_ = lean_ctor_get(v___x_2410_, 3);
v_diag_2414_ = lean_ctor_get(v___x_2410_, 4);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v___x_2410_, 1);
lean_dec(v_unused_2425_);
v___x_2416_ = v___x_2410_;
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_diag_2414_);
lean_inc(v_postponed_2413_);
lean_inc(v_zetaDeltaFVarIds_2412_);
lean_inc(v_mctx_2411_);
lean_dec(v___x_2410_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = lean_box(0);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2390_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_mctx_2411_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_zetaDeltaFVarIds_2412_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_postponed_2413_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_diag_2414_);
v___x_2420_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_st_ref_put(v___y_2389_, v___x_2420_);
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2418_);
return v___x_2422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2429_, lean_object* v_isExporting_2430_, lean_object* v___x_2431_, lean_object* v___y_2432_, lean_object* v___x_2433_, lean_object* v_a_x3f_2434_, lean_object* v___y_2435_){
_start:
{
uint8_t v_isExporting_boxed_2436_; lean_object* v_res_2437_; 
v_isExporting_boxed_2436_ = lean_unbox(v_isExporting_2430_);
v_res_2437_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2429_, v_isExporting_boxed_2436_, v___x_2431_, v___y_2432_, v___x_2433_, v_a_x3f_2434_);
lean_dec(v_a_x3f_2434_);
lean_dec(v___y_2432_);
lean_dec(v___y_2429_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2438_, uint8_t v_isExporting_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v_env_2446_; lean_object* v___x_2447_; uint8_t v_isModule_2448_; 
v___x_2445_ = lean_st_ref_get(v___y_2443_);
v_env_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc_ref(v_env_2446_);
lean_dec(v___x_2445_);
v___x_2447_ = l_Lean_Environment_header(v_env_2446_);
v_isModule_2448_ = lean_ctor_get_uint8(v___x_2447_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2447_);
if (v_isModule_2448_ == 0)
{
lean_object* v___x_2449_; 
lean_dec_ref(v_env_2446_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
lean_inc(v___y_2441_);
lean_inc_ref(v___y_2440_);
v___x_2449_ = lean_apply_5(v_x_2438_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, lean_box(0));
return v___x_2449_;
}
else
{
uint8_t v_isExporting_2450_; 
v_isExporting_2450_ = lean_ctor_get_uint8(v_env_2446_, sizeof(void*)*8);
lean_dec_ref(v_env_2446_);
if (v_isExporting_2439_ == 0)
{
if (v_isExporting_2450_ == 0)
{
lean_object* v___x_2517_; 
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
lean_inc(v___y_2441_);
lean_inc_ref(v___y_2440_);
v___x_2517_ = lean_apply_5(v_x_2438_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, lean_box(0));
return v___x_2517_;
}
else
{
goto v___jp_2451_;
}
}
else
{
if (v_isExporting_2450_ == 0)
{
goto v___jp_2451_;
}
else
{
lean_object* v___x_2518_; 
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
lean_inc(v___y_2441_);
lean_inc_ref(v___y_2440_);
v___x_2518_ = lean_apply_5(v_x_2438_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, lean_box(0));
return v___x_2518_;
}
}
v___jp_2451_:
{
lean_object* v___x_2452_; lean_object* v_env_2453_; lean_object* v_nextMacroScope_2454_; lean_object* v_ngen_2455_; lean_object* v_auxDeclNGen_2456_; lean_object* v_traceState_2457_; lean_object* v_recordedDeps_2458_; lean_object* v_messages_2459_; lean_object* v_infoState_2460_; lean_object* v_snapshotTasks_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2515_; 
v___x_2452_ = lean_st_ref_take(v___y_2443_);
v_env_2453_ = lean_ctor_get(v___x_2452_, 0);
v_nextMacroScope_2454_ = lean_ctor_get(v___x_2452_, 1);
v_ngen_2455_ = lean_ctor_get(v___x_2452_, 2);
v_auxDeclNGen_2456_ = lean_ctor_get(v___x_2452_, 3);
v_traceState_2457_ = lean_ctor_get(v___x_2452_, 4);
v_recordedDeps_2458_ = lean_ctor_get(v___x_2452_, 6);
v_messages_2459_ = lean_ctor_get(v___x_2452_, 7);
v_infoState_2460_ = lean_ctor_get(v___x_2452_, 8);
v_snapshotTasks_2461_ = lean_ctor_get(v___x_2452_, 9);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; 
v_unused_2516_ = lean_ctor_get(v___x_2452_, 5);
lean_dec(v_unused_2516_);
v___x_2463_ = v___x_2452_;
v_isShared_2464_ = v_isSharedCheck_2515_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_snapshotTasks_2461_);
lean_inc(v_infoState_2460_);
lean_inc(v_messages_2459_);
lean_inc(v_recordedDeps_2458_);
lean_inc(v_traceState_2457_);
lean_inc(v_auxDeclNGen_2456_);
lean_inc(v_ngen_2455_);
lean_inc(v_nextMacroScope_2454_);
lean_inc(v_env_2453_);
lean_dec(v___x_2452_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2515_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2465_ = l_Lean_Environment_setExporting(v_env_2453_, v_isExporting_2439_);
v___x_2466_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 5, v___x_2466_);
lean_ctor_set(v___x_2463_, 0, v___x_2465_);
v___x_2468_ = v___x_2463_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_nextMacroScope_2454_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_ngen_2455_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_auxDeclNGen_2456_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_traceState_2457_);
lean_ctor_set(v_reuseFailAlloc_2514_, 5, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2514_, 6, v_recordedDeps_2458_);
lean_ctor_set(v_reuseFailAlloc_2514_, 7, v_messages_2459_);
lean_ctor_set(v_reuseFailAlloc_2514_, 8, v_infoState_2460_);
lean_ctor_set(v_reuseFailAlloc_2514_, 9, v_snapshotTasks_2461_);
v___x_2468_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_mctx_2471_; lean_object* v_zetaDeltaFVarIds_2472_; lean_object* v_postponed_2473_; lean_object* v_diag_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2512_; 
v___x_2469_ = lean_st_ref_put(v___y_2443_, v___x_2468_);
v___x_2470_ = lean_st_ref_take(v___y_2441_);
v_mctx_2471_ = lean_ctor_get(v___x_2470_, 0);
v_zetaDeltaFVarIds_2472_ = lean_ctor_get(v___x_2470_, 2);
v_postponed_2473_ = lean_ctor_get(v___x_2470_, 3);
v_diag_2474_ = lean_ctor_get(v___x_2470_, 4);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2470_, 1);
lean_dec(v_unused_2513_);
v___x_2476_ = v___x_2470_;
v_isShared_2477_ = v_isSharedCheck_2512_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_diag_2474_);
lean_inc(v_postponed_2473_);
lean_inc(v_zetaDeltaFVarIds_2472_);
lean_inc(v_mctx_2471_);
lean_dec(v___x_2470_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2512_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2478_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2478_);
v___x_2480_ = v___x_2476_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_mctx_2471_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_zetaDeltaFVarIds_2472_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_postponed_2473_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_diag_2474_);
v___x_2480_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v_r_2482_; 
v___x_2481_ = lean_st_ref_put(v___y_2441_, v___x_2480_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
lean_inc(v___y_2441_);
lean_inc_ref(v___y_2440_);
v_r_2482_ = lean_apply_5(v_x_2438_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, lean_box(0));
if (lean_obj_tag(v_r_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2499_; 
v_a_2483_ = lean_ctor_get(v_r_2482_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_r_2482_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2485_ = v_r_2482_;
v_isShared_2486_ = v_isSharedCheck_2499_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v_r_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2499_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
lean_inc(v_a_2483_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set_tag(v___x_2485_, 1);
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v___x_2489_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2443_, v_isExporting_2450_, v___x_2466_, v___y_2441_, v___x_2478_, v___x_2488_);
lean_dec_ref(v___x_2488_);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v___x_2489_, 0);
lean_dec(v_unused_2497_);
v___x_2491_ = v___x_2489_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v___x_2489_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v_a_2483_);
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2483_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_a_2500_ = lean_ctor_get(v_r_2482_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v_r_2482_, 1);
v___x_2501_ = lean_box(0);
v___x_2502_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2443_, v_isExporting_2450_, v___x_2466_, v___y_2441_, v___x_2478_, v___x_2501_);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2509_ == 0)
{
lean_object* v_unused_2510_; 
v_unused_2510_ = lean_ctor_get(v___x_2502_, 0);
lean_dec(v_unused_2510_);
v___x_2504_ = v___x_2502_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_dec(v___x_2502_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 1);
lean_ctor_set(v___x_2504_, 0, v_a_2500_);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2500_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2519_, lean_object* v_isExporting_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v_isExporting_boxed_2526_; lean_object* v_res_2527_; 
v_isExporting_boxed_2526_ = lean_unbox(v_isExporting_2520_);
v_res_2527_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2519_, v_isExporting_boxed_2526_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2528_, uint8_t v_when_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
if (v_when_2529_ == 0)
{
lean_object* v___x_2535_; 
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
v___x_2535_ = lean_apply_5(v_x_2528_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
return v___x_2535_;
}
else
{
uint8_t v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = 0;
v___x_2537_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2528_, v___x_2536_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2538_, lean_object* v_when_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v_when_boxed_2545_; lean_object* v_res_2546_; 
v_when_boxed_2545_ = lean_unbox(v_when_2539_);
v_res_2546_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2538_, v_when_boxed_2545_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
return v_res_2546_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2556_, uint8_t v_nonRec_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v_env_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; 
v___x_2563_ = lean_st_ref_get(v___y_2561_);
v_env_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc_ref(v_env_2564_);
lean_dec(v___x_2563_);
v___x_2565_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2556_);
v___x_2566_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2564_, v_declName_2556_, v___x_2565_);
v___x_2567_ = lean_box(v_nonRec_2557_);
lean_inc(v___x_2566_);
v___f_2568_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2568_, 0, v___x_2566_);
lean_closure_set(v___f_2568_, 1, v_declName_2556_);
lean_closure_set(v___f_2568_, 2, v___x_2567_);
lean_closure_set(v___f_2568_, 3, v___x_2565_);
v___x_2569_ = 1;
v___x_2570_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2568_, v___x_2569_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
if (lean_obj_tag(v_a_2571_) == 1)
{
lean_object* v_val_2572_; uint8_t v___x_2573_; 
v_val_2572_ = lean_ctor_get(v_a_2571_, 0);
v___x_2573_ = lean_name_eq(v_val_2572_, v___x_2566_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_inc(v_val_2572_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2574_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2575_ = l_Lean_MessageData_ofName(v_val_2572_);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = l_Lean_MessageData_ofName(v___x_2566_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2582_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_dec(v___x_2566_);
return v___x_2570_;
}
}
else
{
lean_dec(v___x_2566_);
return v___x_2570_;
}
}
else
{
lean_dec(v___x_2566_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2592_, lean_object* v_nonRec_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v_nonRec_boxed_2599_; lean_object* v_res_2600_; 
v_nonRec_boxed_2599_ = lean_unbox(v_nonRec_2593_);
v_res_2600_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2592_, v_nonRec_boxed_2599_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2601_, uint8_t v_nonRec_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v___x_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2608_ = lean_box(v_nonRec_2602_);
v___f_2609_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2609_, 0, v_declName_2601_);
lean_closure_set(v___f_2609_, 1, v___x_2608_);
v___x_2610_ = lean_unsigned_to_nat(32u);
v___x_2611_ = lean_mk_empty_array_with_capacity(v___x_2610_);
lean_dec_ref(v___x_2611_);
v___x_2612_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2614_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2612_, v___x_2613_, v___f_2609_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2615_, lean_object* v_nonRec_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
uint8_t v_nonRec_boxed_2622_; lean_object* v_res_2623_; 
v_nonRec_boxed_2622_ = lean_unbox(v_nonRec_2616_);
v_res_2623_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2615_, v_nonRec_boxed_2622_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2624_, lean_object* v_as_2625_, lean_object* v_as_x27_2626_, lean_object* v_b_2627_, lean_object* v_a_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2624_, v_as_x27_2626_, v_b_2627_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2635_, lean_object* v_as_2636_, lean_object* v_as_x27_2637_, lean_object* v_b_2638_, lean_object* v_a_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2635_, v_as_2636_, v_as_x27_2637_, v_b_2638_, v_a_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v_as_x27_2637_);
lean_dec(v_as_2636_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2646_, lean_object* v_x_2647_, uint8_t v_isExporting_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2647_, v_isExporting_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2655_, lean_object* v_x_2656_, lean_object* v_isExporting_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v_isExporting_boxed_2663_; lean_object* v_res_2664_; 
v_isExporting_boxed_2663_ = lean_unbox(v_isExporting_2657_);
v_res_2664_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2655_, v_x_2656_, v_isExporting_boxed_2663_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2665_, lean_object* v_x_2666_, uint8_t v_when_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2666_, v_when_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2674_, lean_object* v_x_2675_, lean_object* v_when_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v_when_boxed_2682_; lean_object* v_res_2683_; 
v_when_boxed_2682_ = lean_unbox(v_when_2676_);
v_res_2683_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2674_, v_x_2675_, v_when_boxed_2682_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2684_, lean_object* v_msg_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2692_, lean_object* v_msg_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2692_, v_msg_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2699_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = lean_unsigned_to_nat(32u);
v___x_2701_ = lean_mk_empty_array_with_capacity(v___x_2700_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2703_ = ((size_t)5ULL);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_unsigned_to_nat(32u);
v___x_2706_ = lean_mk_empty_array_with_capacity(v___x_2705_);
v___x_2707_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2708_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v___x_2706_);
lean_ctor_set(v___x_2708_, 2, v___x_2704_);
lean_ctor_set(v___x_2708_, 3, v___x_2704_);
lean_ctor_set_usize(v___x_2708_, 4, v___x_2703_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v_traceState_2712_; lean_object* v_traces_2713_; lean_object* v___x_2714_; lean_object* v_traceState_2715_; lean_object* v_env_2716_; lean_object* v_nextMacroScope_2717_; lean_object* v_ngen_2718_; lean_object* v_auxDeclNGen_2719_; lean_object* v_cache_2720_; lean_object* v_recordedDeps_2721_; lean_object* v_messages_2722_; lean_object* v_infoState_2723_; lean_object* v_snapshotTasks_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2743_; 
v___x_2711_ = lean_st_ref_get(v___y_2709_);
v_traceState_2712_ = lean_ctor_get(v___x_2711_, 4);
lean_inc_ref(v_traceState_2712_);
lean_dec(v___x_2711_);
v_traces_2713_ = lean_ctor_get(v_traceState_2712_, 0);
lean_inc_ref(v_traces_2713_);
lean_dec_ref(v_traceState_2712_);
v___x_2714_ = lean_st_ref_take(v___y_2709_);
v_traceState_2715_ = lean_ctor_get(v___x_2714_, 4);
v_env_2716_ = lean_ctor_get(v___x_2714_, 0);
v_nextMacroScope_2717_ = lean_ctor_get(v___x_2714_, 1);
v_ngen_2718_ = lean_ctor_get(v___x_2714_, 2);
v_auxDeclNGen_2719_ = lean_ctor_get(v___x_2714_, 3);
v_cache_2720_ = lean_ctor_get(v___x_2714_, 5);
v_recordedDeps_2721_ = lean_ctor_get(v___x_2714_, 6);
v_messages_2722_ = lean_ctor_get(v___x_2714_, 7);
v_infoState_2723_ = lean_ctor_get(v___x_2714_, 8);
v_snapshotTasks_2724_ = lean_ctor_get(v___x_2714_, 9);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2726_ = v___x_2714_;
v_isShared_2727_ = v_isSharedCheck_2743_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_snapshotTasks_2724_);
lean_inc(v_infoState_2723_);
lean_inc(v_messages_2722_);
lean_inc(v_recordedDeps_2721_);
lean_inc(v_cache_2720_);
lean_inc(v_traceState_2715_);
lean_inc(v_auxDeclNGen_2719_);
lean_inc(v_ngen_2718_);
lean_inc(v_nextMacroScope_2717_);
lean_inc(v_env_2716_);
lean_dec(v___x_2714_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2743_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint64_t v_tid_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2741_; 
v_tid_2728_ = lean_ctor_get_uint64(v_traceState_2715_, sizeof(void*)*1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_traceState_2715_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v_traceState_2715_, 0);
lean_dec(v_unused_2742_);
v___x_2730_ = v_traceState_2715_;
v_isShared_2731_ = v_isSharedCheck_2741_;
goto v_resetjp_2729_;
}
else
{
lean_dec(v_traceState_2715_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2741_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2732_);
lean_ctor_set_uint64(v_reuseFailAlloc_2740_, sizeof(void*)*1, v_tid_2728_);
v___x_2734_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 4, v___x_2734_);
v___x_2736_ = v___x_2726_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_env_2716_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_nextMacroScope_2717_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v_ngen_2718_);
lean_ctor_set(v_reuseFailAlloc_2739_, 3, v_auxDeclNGen_2719_);
lean_ctor_set(v_reuseFailAlloc_2739_, 4, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2739_, 5, v_cache_2720_);
lean_ctor_set(v_reuseFailAlloc_2739_, 6, v_recordedDeps_2721_);
lean_ctor_set(v_reuseFailAlloc_2739_, 7, v_messages_2722_);
lean_ctor_set(v_reuseFailAlloc_2739_, 8, v_infoState_2723_);
lean_ctor_set(v_reuseFailAlloc_2739_, 9, v_snapshotTasks_2724_);
v___x_2736_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_st_ref_put(v___y_2709_, v___x_2736_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_traces_2713_);
return v___x_2738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2744_);
lean_dec(v___y_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = 0;
v___x_2760_ = lean_box(v___x_2759_);
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
return v_res_2766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2775_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2776_ = l_Lean_MessageData_ofName(v_name_2770_);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2779_, lean_object* v_x_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2779_, v_x_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v_x_2780_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2785_){
_start:
{
if (lean_obj_tag(v_x_2785_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_a_2787_ = lean_ctor_get(v_x_2785_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_x_2785_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v_x_2785_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v_x_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 1);
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v_x_2785_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_x_2785_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v_x_2785_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v_x_2785_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 0);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2806_){
_start:
{
if (lean_obj_tag(v_e_2806_) == 0)
{
uint8_t v___x_2807_; 
v___x_2807_ = 2;
return v___x_2807_;
}
else
{
lean_object* v_a_2808_; uint8_t v___x_2809_; 
v_a_2808_ = lean_ctor_get(v_e_2806_, 0);
v___x_2809_ = lean_unbox(v_a_2808_);
if (v___x_2809_ == 0)
{
uint8_t v___x_2810_; 
v___x_2810_ = 1;
return v___x_2810_;
}
else
{
uint8_t v___x_2811_; 
v___x_2811_ = 0;
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2812_){
_start:
{
uint8_t v_res_2813_; lean_object* v_r_2814_; 
v_res_2813_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2812_);
lean_dec_ref(v_e_2812_);
v_r_2814_ = lean_box(v_res_2813_);
return v_r_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2815_, size_t v_i_2816_, lean_object* v_bs_2817_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_usize_dec_lt(v_i_2816_, v_sz_2815_);
if (v___x_2818_ == 0)
{
return v_bs_2817_;
}
else
{
lean_object* v_v_2819_; lean_object* v_msg_2820_; lean_object* v___x_2821_; lean_object* v_bs_x27_2822_; size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v_v_2819_ = lean_array_uget_borrowed(v_bs_2817_, v_i_2816_);
v_msg_2820_ = lean_ctor_get(v_v_2819_, 1);
lean_inc_ref(v_msg_2820_);
v___x_2821_ = lean_unsigned_to_nat(0u);
v_bs_x27_2822_ = lean_array_uset(v_bs_2817_, v_i_2816_, v___x_2821_);
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_add(v_i_2816_, v___x_2823_);
v___x_2825_ = lean_array_uset(v_bs_x27_2822_, v_i_2816_, v_msg_2820_);
v_i_2816_ = v___x_2824_;
v_bs_2817_ = v___x_2825_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2827_, lean_object* v_i_2828_, lean_object* v_bs_2829_){
_start:
{
size_t v_sz_boxed_2830_; size_t v_i_boxed_2831_; lean_object* v_res_2832_; 
v_sz_boxed_2830_ = lean_unbox_usize(v_sz_2827_);
lean_dec(v_sz_2827_);
v_i_boxed_2831_ = lean_unbox_usize(v_i_2828_);
lean_dec(v_i_2828_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2830_, v_i_boxed_2831_, v_bs_2829_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2833_, lean_object* v_data_2834_, lean_object* v_ref_2835_, lean_object* v_msg_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_toCold_2840_; lean_object* v_currRecDepth_2841_; lean_object* v_ref_2842_; uint16_t v_optionFlags_2843_; uint8_t v_suppressElabErrors_2844_; uint8_t v_isRecordingDeps_2845_; lean_object* v_ref_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v_traceState_2849_; lean_object* v_traces_2850_; lean_object* v___x_2851_; size_t v_sz_2852_; size_t v___x_2853_; lean_object* v___x_2854_; lean_object* v_msg_2855_; lean_object* v___x_2856_; lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2895_; 
v_toCold_2840_ = lean_ctor_get(v___y_2837_, 0);
v_currRecDepth_2841_ = lean_ctor_get(v___y_2837_, 1);
v_ref_2842_ = lean_ctor_get(v___y_2837_, 2);
v_optionFlags_2843_ = lean_ctor_get_uint16(v___y_2837_, sizeof(void*)*3);
v_suppressElabErrors_2844_ = lean_ctor_get_uint8(v___y_2837_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2845_ = lean_ctor_get_uint8(v___y_2837_, sizeof(void*)*3 + 3);
v_ref_2846_ = l_Lean_replaceRef(v_ref_2835_, v_ref_2842_);
lean_inc(v_currRecDepth_2841_);
lean_inc_ref(v_toCold_2840_);
v___x_2847_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2847_, 0, v_toCold_2840_);
lean_ctor_set(v___x_2847_, 1, v_currRecDepth_2841_);
lean_ctor_set(v___x_2847_, 2, v_ref_2846_);
lean_ctor_set_uint16(v___x_2847_, sizeof(void*)*3, v_optionFlags_2843_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*3 + 2, v_suppressElabErrors_2844_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*3 + 3, v_isRecordingDeps_2845_);
v___x_2848_ = lean_st_ref_get(v___y_2838_);
v_traceState_2849_ = lean_ctor_get(v___x_2848_, 4);
lean_inc_ref(v_traceState_2849_);
lean_dec(v___x_2848_);
v_traces_2850_ = lean_ctor_get(v_traceState_2849_, 0);
lean_inc_ref(v_traces_2850_);
lean_dec_ref(v_traceState_2849_);
v___x_2851_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2850_);
lean_dec_ref(v_traces_2850_);
v_sz_2852_ = lean_array_size(v___x_2851_);
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2852_, v___x_2853_, v___x_2851_);
v_msg_2855_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2855_, 0, v_data_2834_);
lean_ctor_set(v_msg_2855_, 1, v_msg_2836_);
lean_ctor_set(v_msg_2855_, 2, v___x_2854_);
v___x_2856_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2855_, v___x_2847_, v___y_2838_);
lean_dec_ref_known(v___x_2847_, 3);
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2895_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2895_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v_traceState_2862_; lean_object* v_env_2863_; lean_object* v_nextMacroScope_2864_; lean_object* v_ngen_2865_; lean_object* v_auxDeclNGen_2866_; lean_object* v_cache_2867_; lean_object* v_recordedDeps_2868_; lean_object* v_messages_2869_; lean_object* v_infoState_2870_; lean_object* v_snapshotTasks_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2894_; 
v___x_2861_ = lean_st_ref_take(v___y_2838_);
v_traceState_2862_ = lean_ctor_get(v___x_2861_, 4);
v_env_2863_ = lean_ctor_get(v___x_2861_, 0);
v_nextMacroScope_2864_ = lean_ctor_get(v___x_2861_, 1);
v_ngen_2865_ = lean_ctor_get(v___x_2861_, 2);
v_auxDeclNGen_2866_ = lean_ctor_get(v___x_2861_, 3);
v_cache_2867_ = lean_ctor_get(v___x_2861_, 5);
v_recordedDeps_2868_ = lean_ctor_get(v___x_2861_, 6);
v_messages_2869_ = lean_ctor_get(v___x_2861_, 7);
v_infoState_2870_ = lean_ctor_get(v___x_2861_, 8);
v_snapshotTasks_2871_ = lean_ctor_get(v___x_2861_, 9);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2873_ = v___x_2861_;
v_isShared_2874_ = v_isSharedCheck_2894_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_snapshotTasks_2871_);
lean_inc(v_infoState_2870_);
lean_inc(v_messages_2869_);
lean_inc(v_recordedDeps_2868_);
lean_inc(v_cache_2867_);
lean_inc(v_traceState_2862_);
lean_inc(v_auxDeclNGen_2866_);
lean_inc(v_ngen_2865_);
lean_inc(v_nextMacroScope_2864_);
lean_inc(v_env_2863_);
lean_dec(v___x_2861_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2894_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
uint64_t v_tid_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2892_; 
v_tid_2875_ = lean_ctor_get_uint64(v_traceState_2862_, sizeof(void*)*1);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_traceState_2862_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v_traceState_2862_, 0);
lean_dec(v_unused_2893_);
v___x_2877_ = v_traceState_2862_;
v_isShared_2878_ = v_isSharedCheck_2892_;
goto v_resetjp_2876_;
}
else
{
lean_dec(v_traceState_2862_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2892_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v_ref_2835_);
lean_ctor_set(v___x_2880_, 1, v_a_2857_);
v___x_2881_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2833_, v___x_2880_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2881_);
v___x_2883_ = v___x_2877_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2881_);
lean_ctor_set_uint64(v_reuseFailAlloc_2891_, sizeof(void*)*1, v_tid_2875_);
v___x_2883_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 4, v___x_2883_);
v___x_2885_ = v___x_2873_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_env_2863_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_nextMacroScope_2864_);
lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_ngen_2865_);
lean_ctor_set(v_reuseFailAlloc_2890_, 3, v_auxDeclNGen_2866_);
lean_ctor_set(v_reuseFailAlloc_2890_, 4, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2890_, 5, v_cache_2867_);
lean_ctor_set(v_reuseFailAlloc_2890_, 6, v_recordedDeps_2868_);
lean_ctor_set(v_reuseFailAlloc_2890_, 7, v_messages_2869_);
lean_ctor_set(v_reuseFailAlloc_2890_, 8, v_infoState_2870_);
lean_ctor_set(v_reuseFailAlloc_2890_, 9, v_snapshotTasks_2871_);
v___x_2885_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2886_ = lean_st_ref_put(v___y_2838_, v___x_2885_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2879_);
v___x_2888_ = v___x_2859_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2879_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2896_, lean_object* v_data_2897_, lean_object* v_ref_2898_, lean_object* v_msg_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2896_, v_data_2897_, v_ref_2898_, v_msg_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2903_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2906_ = l_Lean_stringToMessageData(v___x_2905_);
return v___x_2906_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2907_; double v___x_2908_; 
v___x_2907_ = lean_unsigned_to_nat(1000u);
v___x_2908_ = lean_float_of_nat(v___x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2909_, uint8_t v_collapsed_2910_, lean_object* v_tag_2911_, lean_object* v_opts_2912_, uint8_t v_clsEnabled_2913_, lean_object* v_oldTraces_2914_, lean_object* v_msg_2915_, lean_object* v_resStartStop_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_fst_2920_; lean_object* v_snd_2921_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v_data_2925_; lean_object* v_fst_2936_; lean_object* v_snd_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; lean_object* v___y_2941_; lean_object* v_a_2942_; uint8_t v___y_2957_; double v___y_2989_; 
v_fst_2920_ = lean_ctor_get(v_resStartStop_2916_, 0);
lean_inc(v_fst_2920_);
v_snd_2921_ = lean_ctor_get(v_resStartStop_2916_, 1);
lean_inc(v_snd_2921_);
lean_dec_ref(v_resStartStop_2916_);
v_fst_2936_ = lean_ctor_get(v_snd_2921_, 0);
lean_inc(v_fst_2936_);
v_snd_2937_ = lean_ctor_get(v_snd_2921_, 1);
lean_inc(v_snd_2937_);
lean_dec(v_snd_2921_);
v___x_2938_ = l_Lean_trace_profiler;
v___x_2939_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2912_, v___x_2938_);
if (v___x_2939_ == 0)
{
v___y_2957_ = v___x_2939_;
goto v___jp_2956_;
}
else
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2995_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2912_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; lean_object* v___x_2997_; double v___x_2998_; double v___x_2999_; double v___x_3000_; 
v___x_2996_ = l_Lean_trace_profiler_threshold;
v___x_2997_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2912_, v___x_2996_);
v___x_2998_ = lean_float_of_nat(v___x_2997_);
v___x_2999_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3000_ = lean_float_div(v___x_2998_, v___x_2999_);
v___y_2989_ = v___x_3000_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; double v___x_3003_; 
v___x_3001_ = l_Lean_trace_profiler_threshold;
v___x_3002_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2912_, v___x_3001_);
v___x_3003_ = lean_float_of_nat(v___x_3002_);
v___y_2989_ = v___x_3003_;
goto v___jp_2988_;
}
}
v___jp_2922_:
{
lean_object* v___x_2926_; 
lean_inc(v___y_2924_);
v___x_2926_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2914_, v_data_2925_, v___y_2924_, v___y_2923_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v___x_2927_; 
lean_dec_ref_known(v___x_2926_, 1);
v___x_2927_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2920_);
return v___x_2927_;
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_fst_2920_);
v_a_2928_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2926_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2926_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
v___jp_2940_:
{
uint8_t v_result_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; double v___x_2946_; lean_object* v_data_2947_; 
v_result_2943_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2920_);
v___x_2944_ = lean_box(v_result_2943_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
v___x_2946_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_2911_);
lean_inc_ref(v___x_2945_);
lean_inc(v_cls_2909_);
v_data_2947_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2947_, 0, v_cls_2909_);
lean_ctor_set(v_data_2947_, 1, v___x_2945_);
lean_ctor_set(v_data_2947_, 2, v_tag_2911_);
lean_ctor_set_float(v_data_2947_, sizeof(void*)*3, v___x_2946_);
lean_ctor_set_float(v_data_2947_, sizeof(void*)*3 + 8, v___x_2946_);
lean_ctor_set_uint8(v_data_2947_, sizeof(void*)*3 + 16, v_collapsed_2910_);
if (v___x_2939_ == 0)
{
lean_dec_ref_known(v___x_2945_, 1);
lean_dec(v_snd_2937_);
lean_dec(v_fst_2936_);
lean_dec_ref(v_tag_2911_);
lean_dec(v_cls_2909_);
v___y_2923_ = v_a_2942_;
v___y_2924_ = v___y_2941_;
v_data_2925_ = v_data_2947_;
goto v___jp_2922_;
}
else
{
lean_object* v_data_2948_; double v___x_2949_; double v___x_2950_; 
lean_dec_ref_known(v_data_2947_, 3);
v_data_2948_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2948_, 0, v_cls_2909_);
lean_ctor_set(v_data_2948_, 1, v___x_2945_);
lean_ctor_set(v_data_2948_, 2, v_tag_2911_);
v___x_2949_ = lean_unbox_float(v_fst_2936_);
lean_dec(v_fst_2936_);
lean_ctor_set_float(v_data_2948_, sizeof(void*)*3, v___x_2949_);
v___x_2950_ = lean_unbox_float(v_snd_2937_);
lean_dec(v_snd_2937_);
lean_ctor_set_float(v_data_2948_, sizeof(void*)*3 + 8, v___x_2950_);
lean_ctor_set_uint8(v_data_2948_, sizeof(void*)*3 + 16, v_collapsed_2910_);
v___y_2923_ = v_a_2942_;
v___y_2924_ = v___y_2941_;
v_data_2925_ = v_data_2948_;
goto v___jp_2922_;
}
}
v___jp_2951_:
{
lean_object* v_ref_2952_; lean_object* v___x_2953_; 
v_ref_2952_ = lean_ctor_get(v___y_2917_, 2);
lean_inc(v___y_2918_);
lean_inc_ref(v___y_2917_);
lean_inc(v_fst_2920_);
v___x_2953_ = lean_apply_4(v_msg_2915_, v_fst_2920_, v___y_2917_, v___y_2918_, lean_box(0));
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___y_2941_ = v_ref_2952_;
v_a_2942_ = v_a_2954_;
goto v___jp_2940_;
}
else
{
lean_object* v___x_2955_; 
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2941_ = v_ref_2952_;
v_a_2942_ = v___x_2955_;
goto v___jp_2940_;
}
}
v___jp_2956_:
{
if (v_clsEnabled_2913_ == 0)
{
if (v___y_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v_traceState_2959_; lean_object* v_env_2960_; lean_object* v_nextMacroScope_2961_; lean_object* v_ngen_2962_; lean_object* v_auxDeclNGen_2963_; lean_object* v_cache_2964_; lean_object* v_recordedDeps_2965_; lean_object* v_messages_2966_; lean_object* v_infoState_2967_; lean_object* v_snapshotTasks_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v_snd_2937_);
lean_dec(v_fst_2936_);
lean_dec_ref(v_msg_2915_);
lean_dec_ref(v_tag_2911_);
lean_dec(v_cls_2909_);
v___x_2958_ = lean_st_ref_take(v___y_2918_);
v_traceState_2959_ = lean_ctor_get(v___x_2958_, 4);
v_env_2960_ = lean_ctor_get(v___x_2958_, 0);
v_nextMacroScope_2961_ = lean_ctor_get(v___x_2958_, 1);
v_ngen_2962_ = lean_ctor_get(v___x_2958_, 2);
v_auxDeclNGen_2963_ = lean_ctor_get(v___x_2958_, 3);
v_cache_2964_ = lean_ctor_get(v___x_2958_, 5);
v_recordedDeps_2965_ = lean_ctor_get(v___x_2958_, 6);
v_messages_2966_ = lean_ctor_get(v___x_2958_, 7);
v_infoState_2967_ = lean_ctor_get(v___x_2958_, 8);
v_snapshotTasks_2968_ = lean_ctor_get(v___x_2958_, 9);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2970_ = v___x_2958_;
v_isShared_2971_ = v_isSharedCheck_2987_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_snapshotTasks_2968_);
lean_inc(v_infoState_2967_);
lean_inc(v_messages_2966_);
lean_inc(v_recordedDeps_2965_);
lean_inc(v_cache_2964_);
lean_inc(v_traceState_2959_);
lean_inc(v_auxDeclNGen_2963_);
lean_inc(v_ngen_2962_);
lean_inc(v_nextMacroScope_2961_);
lean_inc(v_env_2960_);
lean_dec(v___x_2958_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2987_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint64_t v_tid_2972_; lean_object* v_traces_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2986_; 
v_tid_2972_ = lean_ctor_get_uint64(v_traceState_2959_, sizeof(void*)*1);
v_traces_2973_ = lean_ctor_get(v_traceState_2959_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_traceState_2959_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2975_ = v_traceState_2959_;
v_isShared_2976_ = v_isSharedCheck_2986_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_traces_2973_);
lean_dec(v_traceState_2959_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2986_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2914_, v_traces_2973_);
lean_dec_ref(v_traces_2973_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2977_);
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2977_);
lean_ctor_set_uint64(v_reuseFailAlloc_2985_, sizeof(void*)*1, v_tid_2972_);
v___x_2979_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 4, v___x_2979_);
v___x_2981_ = v___x_2970_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_env_2960_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_nextMacroScope_2961_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_ngen_2962_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_auxDeclNGen_2963_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2984_, 5, v_cache_2964_);
lean_ctor_set(v_reuseFailAlloc_2984_, 6, v_recordedDeps_2965_);
lean_ctor_set(v_reuseFailAlloc_2984_, 7, v_messages_2966_);
lean_ctor_set(v_reuseFailAlloc_2984_, 8, v_infoState_2967_);
lean_ctor_set(v_reuseFailAlloc_2984_, 9, v_snapshotTasks_2968_);
v___x_2981_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_st_ref_put(v___y_2918_, v___x_2981_);
v___x_2983_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2920_);
return v___x_2983_;
}
}
}
}
}
else
{
goto v___jp_2951_;
}
}
else
{
goto v___jp_2951_;
}
}
v___jp_2988_:
{
double v___x_2990_; double v___x_2991_; double v___x_2992_; uint8_t v___x_2993_; 
v___x_2990_ = lean_unbox_float(v_snd_2937_);
v___x_2991_ = lean_unbox_float(v_fst_2936_);
v___x_2992_ = lean_float_sub(v___x_2990_, v___x_2991_);
v___x_2993_ = lean_float_decLt(v___y_2989_, v___x_2992_);
v___y_2957_ = v___x_2993_;
goto v___jp_2956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3004_, lean_object* v_collapsed_3005_, lean_object* v_tag_3006_, lean_object* v_opts_3007_, lean_object* v_clsEnabled_3008_, lean_object* v_oldTraces_3009_, lean_object* v_msg_3010_, lean_object* v_resStartStop_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v_collapsed_boxed_3015_; uint8_t v_clsEnabled_boxed_3016_; lean_object* v_res_3017_; 
v_collapsed_boxed_3015_ = lean_unbox(v_collapsed_3005_);
v_clsEnabled_boxed_3016_ = lean_unbox(v_clsEnabled_3008_);
v_res_3017_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3004_, v_collapsed_boxed_3015_, v_tag_3006_, v_opts_3007_, v_clsEnabled_boxed_3016_, v_oldTraces_3009_, v_msg_3010_, v_resStartStop_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec_ref(v_opts_3007_);
return v_res_3017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
lean_ctor_set(v___x_3022_, 3, v___x_3021_);
lean_ctor_set(v___x_3022_, 4, v___x_3020_);
lean_ctor_set(v___x_3022_, 5, v___x_3020_);
lean_ctor_set(v___x_3022_, 6, v___x_3020_);
lean_ctor_set(v___x_3022_, 7, v___x_3020_);
lean_ctor_set(v___x_3022_, 8, v___x_3020_);
lean_ctor_set(v___x_3022_, 9, v___x_3020_);
lean_ctor_set(v___x_3022_, 10, v___x_3020_);
return v___x_3022_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3024_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
lean_ctor_set(v___x_3024_, 2, v___x_3023_);
lean_ctor_set(v___x_3024_, 3, v___x_3023_);
lean_ctor_set(v___x_3024_, 4, v___x_3023_);
lean_ctor_set(v___x_3024_, 5, v___x_3023_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
lean_ctor_set(v___x_3026_, 2, v___x_3025_);
lean_ctor_set(v___x_3026_, 3, v___x_3025_);
lean_ctor_set(v___x_3026_, 4, v___x_3025_);
return v___x_3026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3032_ = l_Lean_Name_append(v___x_3031_, v___x_3030_);
return v___x_3032_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3033_; double v___x_3034_; 
v___x_3033_ = lean_unsigned_to_nat(1000000000u);
v___x_3034_ = lean_float_of_nat(v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3035_, lean_object* v___f_3036_, lean_object* v_name_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_toCold_3041_; lean_object* v_options_3042_; uint8_t v_hasTrace_3043_; 
v_toCold_3041_ = lean_ctor_get(v___y_3038_, 0);
v_options_3042_ = lean_ctor_get(v_toCold_3041_, 2);
v_hasTrace_3043_ = lean_ctor_get_uint8(v_options_3042_, sizeof(void*)*1);
if (v_hasTrace_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v_env_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v___f_3036_);
v___x_3044_ = lean_st_ref_get(v___y_3039_);
v_env_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc_ref(v_env_3045_);
lean_dec(v___x_3044_);
lean_inc(v_name_3037_);
v___x_3046_ = l_Lean_Meta_declFromEqLikeName(v_env_3045_, v_name_3037_);
if (lean_obj_tag(v___x_3046_) == 1)
{
lean_object* v_val_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3152_; 
v_val_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3152_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_val_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3152_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_fst_3051_; lean_object* v_snd_3052_; lean_object* v___x_3053_; lean_object* v_env_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v_fst_3051_ = lean_ctor_get(v_val_3047_, 0);
lean_inc_n(v_fst_3051_, 2);
v_snd_3052_ = lean_ctor_get(v_val_3047_, 1);
lean_inc_n(v_snd_3052_, 2);
lean_dec(v_val_3047_);
v___x_3053_ = lean_st_ref_get(v___y_3039_);
v_env_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc_ref(v_env_3054_);
lean_dec(v___x_3053_);
v___x_3055_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3054_, v_fst_3051_, v_snd_3052_);
v___x_3056_ = lean_name_eq(v_name_3037_, v___x_3055_);
lean_dec(v___x_3055_);
lean_dec(v_name_3037_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3059_; 
lean_dec(v_snd_3052_);
lean_dec(v_fst_3051_);
lean_dec(v___x_3035_);
v___x_3057_ = lean_box(v_hasTrace_3043_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set_tag(v___x_3049_, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3057_);
v___x_3059_ = v___x_3049_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
else
{
uint8_t v___x_3061_; lean_object* v_a_3063_; 
lean_inc(v_snd_3052_);
v___x_3061_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3052_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3077_; uint8_t v___x_3078_; lean_object* v_a_3080_; 
lean_del_object(v___x_3049_);
v___x_3077_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3078_ = lean_string_dec_eq(v_snd_3052_, v___x_3077_);
lean_dec(v_snd_3052_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec(v_fst_3051_);
lean_dec(v___x_3035_);
v___x_3092_ = lean_box(v_hasTrace_3043_);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
else
{
uint8_t v___x_3094_; uint8_t v___x_3095_; uint8_t v___x_3096_; lean_object* v___x_3097_; uint64_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3094_ = 1;
v___x_3095_ = 0;
v___x_3096_ = 2;
v___x_3097_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3097_, 0, v___x_3061_);
lean_ctor_set_uint8(v___x_3097_, 1, v___x_3061_);
lean_ctor_set_uint8(v___x_3097_, 2, v___x_3061_);
lean_ctor_set_uint8(v___x_3097_, 3, v___x_3061_);
lean_ctor_set_uint8(v___x_3097_, 4, v___x_3061_);
lean_ctor_set_uint8(v___x_3097_, 5, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 6, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 7, v___x_3061_);
lean_ctor_set_uint8(v___x_3097_, 8, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 9, v___x_3094_);
lean_ctor_set_uint8(v___x_3097_, 10, v___x_3095_);
lean_ctor_set_uint8(v___x_3097_, 11, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 12, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 13, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 14, v___x_3096_);
lean_ctor_set_uint8(v___x_3097_, 15, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 16, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 17, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 18, v___x_3078_);
lean_ctor_set_uint8(v___x_3097_, 19, v___x_3061_);
v___x_3098_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3097_);
v___x_3099_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set_uint64(v___x_3099_, sizeof(void*)*1, v___x_3098_);
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3102_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3103_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3104_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3105_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3105_, 0, v___x_3099_);
lean_ctor_set(v___x_3105_, 1, v___x_3035_);
lean_ctor_set(v___x_3105_, 2, v___x_3102_);
lean_ctor_set(v___x_3105_, 3, v___x_3103_);
lean_ctor_set(v___x_3105_, 4, v___x_3104_);
lean_ctor_set(v___x_3105_, 5, v___x_3100_);
lean_ctor_set(v___x_3105_, 6, v___x_3104_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*7, v___x_3061_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*7 + 1, v___x_3061_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*7 + 2, v___x_3061_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*7 + 3, v___x_3056_);
v___x_3106_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3107_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3108_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3106_);
lean_ctor_set(v___x_3109_, 1, v___x_3107_);
lean_ctor_set(v___x_3109_, 2, v___x_3035_);
lean_ctor_set(v___x_3109_, 3, v___x_3101_);
lean_ctor_set(v___x_3109_, 4, v___x_3108_);
v___x_3110_ = lean_st_mk_ref(v___x_3109_);
v___x_3111_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3051_, v___x_3056_, v___x_3105_, v___x_3110_, v___y_3038_, v___y_3039_);
lean_dec_ref_known(v___x_3105_, 7);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3113_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = lean_st_ref_get(v___x_3110_);
lean_dec(v___x_3110_);
lean_dec(v___x_3113_);
v_a_3080_ = v_a_3112_;
goto v___jp_3079_;
}
else
{
lean_dec(v___x_3110_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3114_; 
v_a_3114_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3111_, 1);
v_a_3080_ = v_a_3114_;
goto v___jp_3079_;
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
v_a_3115_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3111_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
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
v___jp_3079_:
{
if (lean_obj_tag(v_a_3080_) == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_box(v___x_3061_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
else
{
lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3090_; 
v_isSharedCheck_3090_ = !lean_is_exclusive(v_a_3080_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v_a_3080_, 0);
lean_dec(v_unused_3091_);
v___x_3084_ = v_a_3080_;
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
else
{
lean_dec(v_a_3080_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = lean_box(v___x_3078_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set_tag(v___x_3084_, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3086_);
v___x_3088_ = v___x_3084_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
else
{
uint8_t v___x_3123_; uint8_t v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; uint64_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec(v_snd_3052_);
v___x_3123_ = 1;
v___x_3124_ = 0;
v___x_3125_ = 2;
v___x_3126_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3126_, 0, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3126_, 1, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3126_, 2, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3126_, 3, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3126_, 4, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3126_, 5, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 6, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 7, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3126_, 8, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 9, v___x_3123_);
lean_ctor_set_uint8(v___x_3126_, 10, v___x_3124_);
lean_ctor_set_uint8(v___x_3126_, 11, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 12, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 13, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 14, v___x_3125_);
lean_ctor_set_uint8(v___x_3126_, 15, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 16, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 17, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 18, v___x_3061_);
lean_ctor_set_uint8(v___x_3126_, 19, v_hasTrace_3043_);
v___x_3127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3126_);
v___x_3128_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3128_, 0, v___x_3126_);
lean_ctor_set_uint64(v___x_3128_, sizeof(void*)*1, v___x_3127_);
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3131_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3132_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3133_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3134_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3134_, 0, v___x_3128_);
lean_ctor_set(v___x_3134_, 1, v___x_3035_);
lean_ctor_set(v___x_3134_, 2, v___x_3131_);
lean_ctor_set(v___x_3134_, 3, v___x_3132_);
lean_ctor_set(v___x_3134_, 4, v___x_3133_);
lean_ctor_set(v___x_3134_, 5, v___x_3129_);
lean_ctor_set(v___x_3134_, 6, v___x_3133_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*7, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*7 + 1, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*7 + 2, v_hasTrace_3043_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*7 + 3, v___x_3056_);
v___x_3135_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3136_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3137_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3135_);
lean_ctor_set(v___x_3138_, 1, v___x_3136_);
lean_ctor_set(v___x_3138_, 2, v___x_3035_);
lean_ctor_set(v___x_3138_, 3, v___x_3130_);
lean_ctor_set(v___x_3138_, 4, v___x_3137_);
v___x_3139_ = lean_st_mk_ref(v___x_3138_);
v___x_3140_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3051_, v___x_3134_, v___x_3139_, v___y_3038_, v___y_3039_);
lean_dec_ref_known(v___x_3134_, 7);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = lean_st_ref_get(v___x_3139_);
lean_dec(v___x_3139_);
lean_dec(v___x_3142_);
v_a_3063_ = v_a_3141_;
goto v___jp_3062_;
}
else
{
lean_dec(v___x_3139_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3143_; 
v_a_3143_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3140_, 1);
v_a_3063_ = v_a_3143_;
goto v___jp_3062_;
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_del_object(v___x_3049_);
v_a_3144_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3140_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3140_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
v___jp_3062_:
{
if (lean_obj_tag(v_a_3063_) == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3066_; 
v___x_3064_ = lean_box(v_hasTrace_3043_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set_tag(v___x_3049_, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3064_);
v___x_3066_ = v___x_3049_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
else
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3075_; 
lean_del_object(v___x_3049_);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_a_3063_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v_a_3063_, 0);
lean_dec(v_unused_3076_);
v___x_3069_ = v_a_3063_;
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v_a_3063_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_box(v___x_3061_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
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
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec(v___x_3046_);
lean_dec(v_name_3037_);
lean_dec(v___x_3035_);
v___x_3153_ = lean_box(v_hasTrace_3043_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3155_; lean_object* v___f_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v_a_3164_; lean_object* v___y_3177_; lean_object* v___y_3178_; uint8_t v_a_3179_; lean_object* v___y_3183_; uint8_t v___y_3184_; lean_object* v___y_3185_; uint8_t v___y_3186_; lean_object* v_a_3187_; lean_object* v___y_3189_; uint8_t v___y_3190_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v_a_3193_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v_a_3197_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v_a_3202_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v_a_3214_; lean_object* v___y_3217_; lean_object* v___y_3218_; uint8_t v_a_3219_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; uint8_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v_a_3233_; uint8_t v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v_a_3240_; 
v_inheritedTraceOptions_3155_ = lean_ctor_get(v_toCold_3041_, 11);
lean_inc(v_name_3037_);
v___f_3156_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3156_, 0, v_name_3037_);
v___x_3157_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3158_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3159_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3160_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3155_, v_options_3042_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3369_ = l_Lean_trace_profiler;
v___x_3370_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3042_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v_env_3372_; lean_object* v___x_3373_; 
lean_dec_ref(v___f_3156_);
lean_dec_ref(v___f_3036_);
v___x_3371_ = lean_st_ref_get(v___y_3039_);
v_env_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc_ref(v_env_3372_);
lean_dec(v___x_3371_);
lean_inc(v_name_3037_);
v___x_3373_ = l_Lean_Meta_declFromEqLikeName(v_env_3372_, v_name_3037_);
if (lean_obj_tag(v___x_3373_) == 1)
{
lean_object* v_val_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3479_; 
v_val_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3479_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_val_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3479_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_fst_3378_; lean_object* v_snd_3379_; lean_object* v___x_3380_; lean_object* v_env_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v_fst_3378_ = lean_ctor_get(v_val_3374_, 0);
lean_inc_n(v_fst_3378_, 2);
v_snd_3379_ = lean_ctor_get(v_val_3374_, 1);
lean_inc_n(v_snd_3379_, 2);
lean_dec(v_val_3374_);
v___x_3380_ = lean_st_ref_get(v___y_3039_);
v_env_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc_ref(v_env_3381_);
lean_dec(v___x_3380_);
v___x_3382_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3381_, v_fst_3378_, v_snd_3379_);
v___x_3383_ = lean_name_eq(v_name_3037_, v___x_3382_);
lean_dec(v___x_3382_);
lean_dec(v_name_3037_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_dec(v_snd_3379_);
lean_dec(v_fst_3378_);
lean_dec(v___x_3035_);
v___x_3384_ = lean_box(v___x_3370_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set_tag(v___x_3376_, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3384_);
v___x_3386_ = v___x_3376_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
else
{
uint8_t v___x_3388_; lean_object* v_a_3390_; 
lean_inc(v_snd_3379_);
v___x_3388_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3379_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3404_; uint8_t v___x_3405_; lean_object* v_a_3407_; 
lean_del_object(v___x_3376_);
v___x_3404_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3405_ = lean_string_dec_eq(v_snd_3379_, v___x_3404_);
lean_dec(v_snd_3379_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
lean_dec(v_fst_3378_);
lean_dec(v___x_3035_);
v___x_3419_ = lean_box(v___x_3370_);
v___x_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
return v___x_3420_;
}
else
{
uint8_t v___x_3421_; uint8_t v___x_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; uint64_t v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3421_ = 1;
v___x_3422_ = 0;
v___x_3423_ = 2;
v___x_3424_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3424_, 0, v___x_3388_);
lean_ctor_set_uint8(v___x_3424_, 1, v___x_3388_);
lean_ctor_set_uint8(v___x_3424_, 2, v___x_3388_);
lean_ctor_set_uint8(v___x_3424_, 3, v___x_3388_);
lean_ctor_set_uint8(v___x_3424_, 4, v___x_3388_);
lean_ctor_set_uint8(v___x_3424_, 5, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 6, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 7, v___x_3388_);
lean_ctor_set_uint8(v___x_3424_, 8, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 9, v___x_3421_);
lean_ctor_set_uint8(v___x_3424_, 10, v___x_3422_);
lean_ctor_set_uint8(v___x_3424_, 11, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 12, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 13, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 14, v___x_3423_);
lean_ctor_set_uint8(v___x_3424_, 15, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 16, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 17, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 18, v___x_3405_);
lean_ctor_set_uint8(v___x_3424_, 19, v___x_3388_);
v___x_3425_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3424_);
v___x_3426_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set_uint64(v___x_3426_, sizeof(void*)*1, v___x_3425_);
v___x_3427_ = lean_unsigned_to_nat(0u);
v___x_3428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3431_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3432_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3432_, 0, v___x_3426_);
lean_ctor_set(v___x_3432_, 1, v___x_3035_);
lean_ctor_set(v___x_3432_, 2, v___x_3429_);
lean_ctor_set(v___x_3432_, 3, v___x_3430_);
lean_ctor_set(v___x_3432_, 4, v___x_3431_);
lean_ctor_set(v___x_3432_, 5, v___x_3427_);
lean_ctor_set(v___x_3432_, 6, v___x_3431_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*7, v___x_3388_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*7 + 1, v___x_3388_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*7 + 2, v___x_3388_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*7 + 3, v_hasTrace_3043_);
v___x_3433_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3434_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3433_);
lean_ctor_set(v___x_3436_, 1, v___x_3434_);
lean_ctor_set(v___x_3436_, 2, v___x_3035_);
lean_ctor_set(v___x_3436_, 3, v___x_3428_);
lean_ctor_set(v___x_3436_, 4, v___x_3435_);
v___x_3437_ = lean_st_mk_ref(v___x_3436_);
v___x_3438_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3378_, v_hasTrace_3043_, v___x_3432_, v___x_3437_, v___y_3038_, v___y_3039_);
lean_dec_ref_known(v___x_3432_, 7);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = lean_st_ref_get(v___x_3437_);
lean_dec(v___x_3437_);
lean_dec(v___x_3440_);
v_a_3407_ = v_a_3439_;
goto v___jp_3406_;
}
else
{
lean_dec(v___x_3437_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3441_; 
v_a_3441_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3438_, 1);
v_a_3407_ = v_a_3441_;
goto v___jp_3406_;
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
v_a_3442_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3438_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3438_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
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
v___jp_3406_:
{
if (lean_obj_tag(v_a_3407_) == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_box(v___x_3388_);
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
return v___x_3409_;
}
else
{
lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3417_; 
v_isSharedCheck_3417_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v_a_3407_, 0);
lean_dec(v_unused_3418_);
v___x_3411_ = v_a_3407_;
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
else
{
lean_dec(v_a_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = lean_box(v___x_3405_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3415_ = v___x_3411_;
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
}
}
}
else
{
uint8_t v___x_3450_; uint8_t v___x_3451_; uint8_t v___x_3452_; lean_object* v___x_3453_; uint64_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec(v_snd_3379_);
v___x_3450_ = 1;
v___x_3451_ = 0;
v___x_3452_ = 2;
v___x_3453_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3453_, 0, v___x_3370_);
lean_ctor_set_uint8(v___x_3453_, 1, v___x_3370_);
lean_ctor_set_uint8(v___x_3453_, 2, v___x_3370_);
lean_ctor_set_uint8(v___x_3453_, 3, v___x_3370_);
lean_ctor_set_uint8(v___x_3453_, 4, v___x_3370_);
lean_ctor_set_uint8(v___x_3453_, 5, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 6, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 7, v___x_3370_);
lean_ctor_set_uint8(v___x_3453_, 8, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 9, v___x_3450_);
lean_ctor_set_uint8(v___x_3453_, 10, v___x_3451_);
lean_ctor_set_uint8(v___x_3453_, 11, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 12, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 13, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 14, v___x_3452_);
lean_ctor_set_uint8(v___x_3453_, 15, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 16, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 17, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 18, v___x_3388_);
lean_ctor_set_uint8(v___x_3453_, 19, v___x_3370_);
v___x_3454_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3453_);
v___x_3455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set_uint64(v___x_3455_, sizeof(void*)*1, v___x_3454_);
v___x_3456_ = lean_unsigned_to_nat(0u);
v___x_3457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3458_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3459_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3460_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3461_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3461_, 0, v___x_3455_);
lean_ctor_set(v___x_3461_, 1, v___x_3035_);
lean_ctor_set(v___x_3461_, 2, v___x_3458_);
lean_ctor_set(v___x_3461_, 3, v___x_3459_);
lean_ctor_set(v___x_3461_, 4, v___x_3460_);
lean_ctor_set(v___x_3461_, 5, v___x_3456_);
lean_ctor_set(v___x_3461_, 6, v___x_3460_);
lean_ctor_set_uint8(v___x_3461_, sizeof(void*)*7, v___x_3370_);
lean_ctor_set_uint8(v___x_3461_, sizeof(void*)*7 + 1, v___x_3370_);
lean_ctor_set_uint8(v___x_3461_, sizeof(void*)*7 + 2, v___x_3370_);
lean_ctor_set_uint8(v___x_3461_, sizeof(void*)*7 + 3, v_hasTrace_3043_);
v___x_3462_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3463_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3464_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3462_);
lean_ctor_set(v___x_3465_, 1, v___x_3463_);
lean_ctor_set(v___x_3465_, 2, v___x_3035_);
lean_ctor_set(v___x_3465_, 3, v___x_3457_);
lean_ctor_set(v___x_3465_, 4, v___x_3464_);
v___x_3466_ = lean_st_mk_ref(v___x_3465_);
v___x_3467_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3378_, v___x_3461_, v___x_3466_, v___y_3038_, v___y_3039_);
lean_dec_ref_known(v___x_3461_, 7);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = lean_st_ref_get(v___x_3466_);
lean_dec(v___x_3466_);
lean_dec(v___x_3469_);
v_a_3390_ = v_a_3468_;
goto v___jp_3389_;
}
else
{
lean_dec(v___x_3466_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3470_; 
v_a_3470_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3467_, 1);
v_a_3390_ = v_a_3470_;
goto v___jp_3389_;
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_del_object(v___x_3376_);
v_a_3471_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3467_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3467_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
v___jp_3389_:
{
if (lean_obj_tag(v_a_3390_) == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3391_ = lean_box(v___x_3370_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set_tag(v___x_3376_, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3391_);
v___x_3393_ = v___x_3376_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
else
{
lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3402_; 
lean_del_object(v___x_3376_);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v_a_3390_, 0);
lean_dec(v_unused_3403_);
v___x_3396_ = v_a_3390_;
v_isShared_3397_ = v_isSharedCheck_3402_;
goto v_resetjp_3395_;
}
else
{
lean_dec(v_a_3390_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3402_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3398_ = lean_box(v___x_3388_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3398_);
v___x_3400_ = v___x_3396_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_dec(v___x_3373_);
lean_dec(v_name_3037_);
lean_dec(v___x_3035_);
v___x_3480_ = lean_box(v___x_3370_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
else
{
goto v___jp_3241_;
}
}
else
{
goto v___jp_3241_;
}
v___jp_3161_:
{
lean_object* v___x_3165_; double v___x_3166_; double v___x_3167_; double v___x_3168_; double v___x_3169_; double v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3165_ = lean_io_mono_nanos_now();
v___x_3166_ = lean_float_of_nat(v___y_3162_);
v___x_3167_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3168_ = lean_float_div(v___x_3166_, v___x_3167_);
v___x_3169_ = lean_float_of_nat(v___x_3165_);
v___x_3170_ = lean_float_div(v___x_3169_, v___x_3167_);
v___x_3171_ = lean_box_float(v___x_3168_);
v___x_3172_ = lean_box_float(v___x_3170_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3171_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v_a_3164_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3157_, v_hasTrace_3043_, v___x_3158_, v_options_3042_, v___x_3160_, v___y_3163_, v___f_3156_, v___x_3174_, v___y_3038_, v___y_3039_);
return v___x_3175_;
}
v___jp_3176_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_box(v_a_3179_);
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
v___y_3162_ = v___y_3177_;
v___y_3163_ = v___y_3178_;
v_a_3164_ = v___x_3181_;
goto v___jp_3161_;
}
v___jp_3182_:
{
if (lean_obj_tag(v_a_3187_) == 0)
{
v___y_3177_ = v___y_3183_;
v___y_3178_ = v___y_3185_;
v_a_3179_ = v___y_3184_;
goto v___jp_3176_;
}
else
{
lean_dec_ref_known(v_a_3187_, 1);
v___y_3177_ = v___y_3183_;
v___y_3178_ = v___y_3185_;
v_a_3179_ = v___y_3186_;
goto v___jp_3176_;
}
}
v___jp_3188_:
{
if (lean_obj_tag(v_a_3193_) == 0)
{
v___y_3177_ = v___y_3189_;
v___y_3178_ = v___y_3192_;
v_a_3179_ = v___y_3190_;
goto v___jp_3176_;
}
else
{
lean_dec_ref_known(v_a_3193_, 1);
v___y_3177_ = v___y_3189_;
v___y_3178_ = v___y_3192_;
v_a_3179_ = v___y_3191_;
goto v___jp_3176_;
}
}
v___jp_3194_:
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v_a_3197_);
v___y_3162_ = v___y_3195_;
v___y_3163_ = v___y_3196_;
v_a_3164_ = v___x_3198_;
goto v___jp_3161_;
}
v___jp_3199_:
{
lean_object* v___x_3203_; double v___x_3204_; double v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3203_ = lean_io_get_num_heartbeats();
v___x_3204_ = lean_float_of_nat(v___y_3201_);
v___x_3205_ = lean_float_of_nat(v___x_3203_);
v___x_3206_ = lean_box_float(v___x_3204_);
v___x_3207_ = lean_box_float(v___x_3205_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v_a_3202_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3157_, v_hasTrace_3043_, v___x_3158_, v_options_3042_, v___x_3160_, v___y_3200_, v___f_3156_, v___x_3209_, v___y_3038_, v___y_3039_);
return v___x_3210_;
}
v___jp_3211_:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_a_3214_);
v___y_3200_ = v___y_3212_;
v___y_3201_ = v___y_3213_;
v_a_3202_ = v___x_3215_;
goto v___jp_3199_;
}
v___jp_3216_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_box(v_a_3219_);
v___x_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v_a_3202_ = v___x_3221_;
goto v___jp_3199_;
}
v___jp_3222_:
{
if (lean_obj_tag(v___y_3225_) == 0)
{
lean_object* v_a_3226_; uint8_t v___x_3227_; 
v_a_3226_ = lean_ctor_get(v___y_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___y_3225_, 1);
v___x_3227_ = lean_unbox(v_a_3226_);
lean_dec(v_a_3226_);
v___y_3217_ = v___y_3223_;
v___y_3218_ = v___y_3224_;
v_a_3219_ = v___x_3227_;
goto v___jp_3216_;
}
else
{
lean_object* v_a_3228_; 
v_a_3228_ = lean_ctor_get(v___y_3225_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___y_3225_, 1);
v___y_3212_ = v___y_3223_;
v___y_3213_ = v___y_3224_;
v_a_3214_ = v_a_3228_;
goto v___jp_3211_;
}
}
v___jp_3229_:
{
if (lean_obj_tag(v_a_3233_) == 0)
{
uint8_t v___x_3234_; 
v___x_3234_ = 0;
v___y_3217_ = v___y_3231_;
v___y_3218_ = v___y_3232_;
v_a_3219_ = v___x_3234_;
goto v___jp_3216_;
}
else
{
lean_dec_ref_known(v_a_3233_, 1);
v___y_3217_ = v___y_3231_;
v___y_3218_ = v___y_3232_;
v_a_3219_ = v___y_3230_;
goto v___jp_3216_;
}
}
v___jp_3235_:
{
if (lean_obj_tag(v_a_3240_) == 0)
{
v___y_3217_ = v___y_3238_;
v___y_3218_ = v___y_3239_;
v_a_3219_ = v___y_3236_;
goto v___jp_3216_;
}
else
{
lean_dec_ref_known(v_a_3240_, 1);
v___y_3217_ = v___y_3238_;
v___y_3218_ = v___y_3239_;
v_a_3219_ = v___y_3237_;
goto v___jp_3216_;
}
}
v___jp_3241_:
{
lean_object* v___x_3242_; lean_object* v_a_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3242_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3039_);
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref(v___x_3242_);
v___x_3244_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3245_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3042_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_env_3248_; lean_object* v___x_3249_; 
lean_dec_ref(v___f_3036_);
v___x_3246_ = lean_io_mono_nanos_now();
v___x_3247_ = lean_st_ref_get(v___y_3039_);
v_env_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_env_3248_);
lean_dec(v___x_3247_);
lean_inc(v_name_3037_);
v___x_3249_ = l_Lean_Meta_declFromEqLikeName(v_env_3248_, v_name_3037_);
if (lean_obj_tag(v___x_3249_) == 1)
{
lean_object* v_val_3250_; lean_object* v_fst_3251_; lean_object* v_snd_3252_; lean_object* v___x_3253_; lean_object* v_env_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_val_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_val_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v_fst_3251_ = lean_ctor_get(v_val_3250_, 0);
lean_inc_n(v_fst_3251_, 2);
v_snd_3252_ = lean_ctor_get(v_val_3250_, 1);
lean_inc_n(v_snd_3252_, 2);
lean_dec(v_val_3250_);
v___x_3253_ = lean_st_ref_get(v___y_3039_);
v_env_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc_ref(v_env_3254_);
lean_dec(v___x_3253_);
v___x_3255_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3254_, v_fst_3251_, v_snd_3252_);
v___x_3256_ = lean_name_eq(v_name_3037_, v___x_3255_);
lean_dec(v___x_3255_);
lean_dec(v_name_3037_);
if (v___x_3256_ == 0)
{
lean_dec(v_snd_3252_);
lean_dec(v_fst_3251_);
lean_dec(v___x_3035_);
v___y_3177_ = v___x_3246_;
v___y_3178_ = v_a_3243_;
v_a_3179_ = v___x_3245_;
goto v___jp_3176_;
}
else
{
uint8_t v___x_3257_; 
lean_inc(v_snd_3252_);
v___x_3257_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3252_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3259_ = lean_string_dec_eq(v_snd_3252_, v___x_3258_);
lean_dec(v_snd_3252_);
if (v___x_3259_ == 0)
{
lean_dec(v_fst_3251_);
lean_dec(v___x_3035_);
v___y_3177_ = v___x_3246_;
v___y_3178_ = v_a_3243_;
v_a_3179_ = v___x_3245_;
goto v___jp_3176_;
}
else
{
uint8_t v___x_3260_; uint8_t v___x_3261_; uint8_t v___x_3262_; lean_object* v___x_3263_; uint64_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3260_ = 1;
v___x_3261_ = 0;
v___x_3262_ = 2;
v___x_3263_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3263_, 0, v___x_3257_);
lean_ctor_set_uint8(v___x_3263_, 1, v___x_3257_);
lean_ctor_set_uint8(v___x_3263_, 2, v___x_3257_);
lean_ctor_set_uint8(v___x_3263_, 3, v___x_3257_);
lean_ctor_set_uint8(v___x_3263_, 4, v___x_3257_);
lean_ctor_set_uint8(v___x_3263_, 5, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 6, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 7, v___x_3257_);
lean_ctor_set_uint8(v___x_3263_, 8, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 9, v___x_3260_);
lean_ctor_set_uint8(v___x_3263_, 10, v___x_3261_);
lean_ctor_set_uint8(v___x_3263_, 11, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 12, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 13, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 14, v___x_3262_);
lean_ctor_set_uint8(v___x_3263_, 15, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 16, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 17, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 18, v___x_3259_);
lean_ctor_set_uint8(v___x_3263_, 19, v___x_3257_);
v___x_3264_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3263_);
v___x_3265_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set_uint64(v___x_3265_, sizeof(void*)*1, v___x_3264_);
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3268_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3269_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3270_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3271_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3271_, 0, v___x_3265_);
lean_ctor_set(v___x_3271_, 1, v___x_3035_);
lean_ctor_set(v___x_3271_, 2, v___x_3268_);
lean_ctor_set(v___x_3271_, 3, v___x_3269_);
lean_ctor_set(v___x_3271_, 4, v___x_3270_);
lean_ctor_set(v___x_3271_, 5, v___x_3266_);
lean_ctor_set(v___x_3271_, 6, v___x_3270_);
lean_ctor_set_uint8(v___x_3271_, sizeof(void*)*7, v___x_3257_);
lean_ctor_set_uint8(v___x_3271_, sizeof(void*)*7 + 1, v___x_3257_);
lean_ctor_set_uint8(v___x_3271_, sizeof(void*)*7 + 2, v___x_3257_);
lean_ctor_set_uint8(v___x_3271_, sizeof(void*)*7 + 3, v_hasTrace_3043_);
v___x_3272_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3273_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3274_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3272_);
lean_ctor_set(v___x_3275_, 1, v___x_3273_);
lean_ctor_set(v___x_3275_, 2, v___x_3035_);
lean_ctor_set(v___x_3275_, 3, v___x_3267_);
lean_ctor_set(v___x_3275_, 4, v___x_3274_);
v___x_3276_ = lean_st_mk_ref(v___x_3275_);
v___x_3277_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3251_, v_hasTrace_3043_, v___x_3271_, v___x_3276_, v___y_3038_, v___y_3039_);
lean_dec_ref_known(v___x_3271_, 7);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = lean_st_ref_get(v___x_3276_);
lean_dec(v___x_3276_);
lean_dec(v___x_3279_);
v___y_3183_ = v___x_3246_;
v___y_3184_ = v___x_3257_;
v___y_3185_ = v_a_3243_;
v___y_3186_ = v___x_3259_;
v_a_3187_ = v_a_3278_;
goto v___jp_3182_;
}
else
{
lean_dec(v___x_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3280_; 
v_a_3280_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3277_, 1);
v___y_3183_ = v___x_3246_;
v___y_3184_ = v___x_3257_;
v___y_3185_ = v_a_3243_;
v___y_3186_ = v___x_3259_;
v_a_3187_ = v_a_3280_;
goto v___jp_3182_;
}
else
{
lean_object* v_a_3281_; 
v_a_3281_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3277_, 1);
v___y_3195_ = v___x_3246_;
v___y_3196_ = v_a_3243_;
v_a_3197_ = v_a_3281_;
goto v___jp_3194_;
}
}
}
}
else
{
uint8_t v___x_3282_; uint8_t v___x_3283_; uint8_t v___x_3284_; lean_object* v___x_3285_; uint64_t v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_snd_3252_);
v___x_3282_ = 1;
v___x_3283_ = 0;
v___x_3284_ = 2;
v___x_3285_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3285_, 0, v___x_3245_);
lean_ctor_set_uint8(v___x_3285_, 1, v___x_3245_);
lean_ctor_set_uint8(v___x_3285_, 2, v___x_3245_);
lean_ctor_set_uint8(v___x_3285_, 3, v___x_3245_);
lean_ctor_set_uint8(v___x_3285_, 4, v___x_3245_);
lean_ctor_set_uint8(v___x_3285_, 5, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 6, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 7, v___x_3245_);
lean_ctor_set_uint8(v___x_3285_, 8, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 9, v___x_3282_);
lean_ctor_set_uint8(v___x_3285_, 10, v___x_3283_);
lean_ctor_set_uint8(v___x_3285_, 11, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 12, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 13, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 14, v___x_3284_);
lean_ctor_set_uint8(v___x_3285_, 15, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 16, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 17, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 18, v___x_3257_);
lean_ctor_set_uint8(v___x_3285_, 19, v___x_3245_);
v___x_3286_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set_uint64(v___x_3287_, sizeof(void*)*1, v___x_3286_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3290_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3291_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3292_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3293_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3293_, 0, v___x_3287_);
lean_ctor_set(v___x_3293_, 1, v___x_3035_);
lean_ctor_set(v___x_3293_, 2, v___x_3290_);
lean_ctor_set(v___x_3293_, 3, v___x_3291_);
lean_ctor_set(v___x_3293_, 4, v___x_3292_);
lean_ctor_set(v___x_3293_, 5, v___x_3288_);
lean_ctor_set(v___x_3293_, 6, v___x_3292_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7, v___x_3245_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 1, v___x_3245_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 2, v___x_3245_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*7 + 3, v_hasTrace_3043_);
v___x_3294_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3294_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
lean_ctor_set(v___x_3297_, 2, v___x_3035_);
lean_ctor_set(v___x_3297_, 3, v___x_3289_);
lean_ctor_set(v___x_3297_, 4, v___x_3296_);
v___x_3298_ = lean_st_mk_ref(v___x_3297_);
v___x_3299_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3251_, v___x_3293_, v___x_3298_, v___y_3038_, v___y_3039_);
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
v___y_3189_ = v___x_3246_;
v___y_3190_ = v___x_3245_;
v___y_3191_ = v___x_3257_;
v___y_3192_ = v_a_3243_;
v_a_3193_ = v_a_3300_;
goto v___jp_3188_;
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
v___y_3189_ = v___x_3246_;
v___y_3190_ = v___x_3245_;
v___y_3191_ = v___x_3257_;
v___y_3192_ = v_a_3243_;
v_a_3193_ = v_a_3302_;
goto v___jp_3188_;
}
else
{
lean_object* v_a_3303_; 
v_a_3303_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3299_, 1);
v___y_3195_ = v___x_3246_;
v___y_3196_ = v_a_3243_;
v_a_3197_ = v_a_3303_;
goto v___jp_3194_;
}
}
}
}
}
else
{
lean_dec(v___x_3249_);
lean_dec(v_name_3037_);
lean_dec(v___x_3035_);
v___y_3177_ = v___x_3246_;
v___y_3178_ = v_a_3243_;
v_a_3179_ = v___x_3245_;
goto v___jp_3176_;
}
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v_env_3306_; lean_object* v___x_3307_; 
v___x_3304_ = lean_io_get_num_heartbeats();
v___x_3305_ = lean_st_ref_get(v___y_3039_);
v_env_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc_ref(v_env_3306_);
lean_dec(v___x_3305_);
lean_inc(v_name_3037_);
v___x_3307_ = l_Lean_Meta_declFromEqLikeName(v_env_3306_, v_name_3037_);
if (lean_obj_tag(v___x_3307_) == 1)
{
lean_object* v_val_3308_; lean_object* v_fst_3309_; lean_object* v_snd_3310_; lean_object* v___x_3311_; lean_object* v_env_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_val_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_val_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v_fst_3309_ = lean_ctor_get(v_val_3308_, 0);
lean_inc_n(v_fst_3309_, 2);
v_snd_3310_ = lean_ctor_get(v_val_3308_, 1);
lean_inc_n(v_snd_3310_, 2);
lean_dec(v_val_3308_);
v___x_3311_ = lean_st_ref_get(v___y_3039_);
v_env_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc_ref(v_env_3312_);
lean_dec(v___x_3311_);
v___x_3313_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3312_, v_fst_3309_, v_snd_3310_);
v___x_3314_ = lean_name_eq(v_name_3037_, v___x_3313_);
lean_dec(v___x_3313_);
lean_dec(v_name_3037_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec(v_snd_3310_);
lean_dec(v_fst_3309_);
lean_dec(v___x_3035_);
v___x_3315_ = lean_box(0);
lean_inc(v___y_3039_);
lean_inc_ref(v___y_3038_);
v___x_3316_ = lean_apply_4(v___f_3036_, v___x_3315_, v___y_3038_, v___y_3039_, lean_box(0));
v___y_3223_ = v_a_3243_;
v___y_3224_ = v___x_3304_;
v___y_3225_ = v___x_3316_;
goto v___jp_3222_;
}
else
{
uint8_t v___x_3317_; 
lean_inc(v_snd_3310_);
v___x_3317_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3310_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3319_ = lean_string_dec_eq(v_snd_3310_, v___x_3318_);
lean_dec(v_snd_3310_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
lean_dec(v_fst_3309_);
lean_dec(v___x_3035_);
v___x_3320_ = lean_box(0);
lean_inc(v___y_3039_);
lean_inc_ref(v___y_3038_);
v___x_3321_ = lean_apply_4(v___f_3036_, v___x_3320_, v___y_3038_, v___y_3039_, lean_box(0));
v___y_3223_ = v_a_3243_;
v___y_3224_ = v___x_3304_;
v___y_3225_ = v___x_3321_;
goto v___jp_3222_;
}
else
{
uint8_t v___x_3322_; uint8_t v___x_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; uint64_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec_ref(v___f_3036_);
v___x_3322_ = 1;
v___x_3323_ = 0;
v___x_3324_ = 2;
v___x_3325_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3325_, 0, v___x_3317_);
lean_ctor_set_uint8(v___x_3325_, 1, v___x_3317_);
lean_ctor_set_uint8(v___x_3325_, 2, v___x_3317_);
lean_ctor_set_uint8(v___x_3325_, 3, v___x_3317_);
lean_ctor_set_uint8(v___x_3325_, 4, v___x_3317_);
lean_ctor_set_uint8(v___x_3325_, 5, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 6, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 7, v___x_3317_);
lean_ctor_set_uint8(v___x_3325_, 8, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 9, v___x_3322_);
lean_ctor_set_uint8(v___x_3325_, 10, v___x_3323_);
lean_ctor_set_uint8(v___x_3325_, 11, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 12, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 13, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 14, v___x_3324_);
lean_ctor_set_uint8(v___x_3325_, 15, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 16, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 17, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 18, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, 19, v___x_3317_);
v___x_3326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3325_);
v___x_3327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set_uint64(v___x_3327_, sizeof(void*)*1, v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3330_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3332_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3333_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3333_, 0, v___x_3327_);
lean_ctor_set(v___x_3333_, 1, v___x_3035_);
lean_ctor_set(v___x_3333_, 2, v___x_3330_);
lean_ctor_set(v___x_3333_, 3, v___x_3331_);
lean_ctor_set(v___x_3333_, 4, v___x_3332_);
lean_ctor_set(v___x_3333_, 5, v___x_3328_);
lean_ctor_set(v___x_3333_, 6, v___x_3332_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7, v___x_3317_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 1, v___x_3317_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 2, v___x_3317_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 3, v___x_3245_);
v___x_3334_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3335_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3336_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v___x_3335_);
lean_ctor_set(v___x_3337_, 2, v___x_3035_);
lean_ctor_set(v___x_3337_, 3, v___x_3329_);
lean_ctor_set(v___x_3337_, 4, v___x_3336_);
v___x_3338_ = lean_st_mk_ref(v___x_3337_);
v___x_3339_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3309_, v___x_3245_, v___x_3333_, v___x_3338_, v___y_3038_, v___y_3039_);
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
v___y_3236_ = v___x_3317_;
v___y_3237_ = v___x_3319_;
v___y_3238_ = v_a_3243_;
v___y_3239_ = v___x_3304_;
v_a_3240_ = v_a_3340_;
goto v___jp_3235_;
}
else
{
lean_dec(v___x_3338_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3342_; 
v_a_3342_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3339_, 1);
v___y_3236_ = v___x_3317_;
v___y_3237_ = v___x_3319_;
v___y_3238_ = v_a_3243_;
v___y_3239_ = v___x_3304_;
v_a_3240_ = v_a_3342_;
goto v___jp_3235_;
}
else
{
lean_object* v_a_3343_; 
v_a_3343_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3339_, 1);
v___y_3212_ = v_a_3243_;
v___y_3213_ = v___x_3304_;
v_a_3214_ = v_a_3343_;
goto v___jp_3211_;
}
}
}
}
else
{
uint8_t v___x_3344_; uint8_t v___x_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; uint64_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_dec(v_snd_3310_);
lean_dec_ref(v___f_3036_);
v___x_3344_ = 0;
v___x_3345_ = 1;
v___x_3346_ = 0;
v___x_3347_ = 2;
v___x_3348_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3348_, 0, v___x_3344_);
lean_ctor_set_uint8(v___x_3348_, 1, v___x_3344_);
lean_ctor_set_uint8(v___x_3348_, 2, v___x_3344_);
lean_ctor_set_uint8(v___x_3348_, 3, v___x_3344_);
lean_ctor_set_uint8(v___x_3348_, 4, v___x_3344_);
lean_ctor_set_uint8(v___x_3348_, 5, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 6, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 7, v___x_3344_);
lean_ctor_set_uint8(v___x_3348_, 8, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 9, v___x_3345_);
lean_ctor_set_uint8(v___x_3348_, 10, v___x_3346_);
lean_ctor_set_uint8(v___x_3348_, 11, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 12, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 13, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 14, v___x_3347_);
lean_ctor_set_uint8(v___x_3348_, 15, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 16, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 17, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 18, v___x_3317_);
lean_ctor_set_uint8(v___x_3348_, 19, v___x_3344_);
v___x_3349_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3348_);
v___x_3350_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set_uint64(v___x_3350_, sizeof(void*)*1, v___x_3349_);
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3353_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3355_ = lean_box(0);
lean_inc(v___x_3035_);
v___x_3356_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3356_, 0, v___x_3350_);
lean_ctor_set(v___x_3356_, 1, v___x_3035_);
lean_ctor_set(v___x_3356_, 2, v___x_3353_);
lean_ctor_set(v___x_3356_, 3, v___x_3354_);
lean_ctor_set(v___x_3356_, 4, v___x_3355_);
lean_ctor_set(v___x_3356_, 5, v___x_3351_);
lean_ctor_set(v___x_3356_, 6, v___x_3355_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7, v___x_3344_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 1, v___x_3344_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 2, v___x_3344_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 3, v___x_3245_);
v___x_3357_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3358_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3359_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3357_);
lean_ctor_set(v___x_3360_, 1, v___x_3358_);
lean_ctor_set(v___x_3360_, 2, v___x_3035_);
lean_ctor_set(v___x_3360_, 3, v___x_3352_);
lean_ctor_set(v___x_3360_, 4, v___x_3359_);
v___x_3361_ = lean_st_mk_ref(v___x_3360_);
v___x_3362_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3309_, v___x_3356_, v___x_3361_, v___y_3038_, v___y_3039_);
lean_dec_ref_known(v___x_3356_, 7);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = lean_st_ref_get(v___x_3361_);
lean_dec(v___x_3361_);
lean_dec(v___x_3364_);
v___y_3230_ = v___x_3317_;
v___y_3231_ = v_a_3243_;
v___y_3232_ = v___x_3304_;
v_a_3233_ = v_a_3363_;
goto v___jp_3229_;
}
else
{
lean_dec(v___x_3361_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3365_; 
v_a_3365_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3362_, 1);
v___y_3230_ = v___x_3317_;
v___y_3231_ = v_a_3243_;
v___y_3232_ = v___x_3304_;
v_a_3233_ = v_a_3365_;
goto v___jp_3229_;
}
else
{
lean_object* v_a_3366_; 
v_a_3366_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3362_, 1);
v___y_3212_ = v_a_3243_;
v___y_3213_ = v___x_3304_;
v_a_3214_ = v_a_3366_;
goto v___jp_3211_;
}
}
}
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec(v___x_3307_);
lean_dec(v_name_3037_);
lean_dec(v___x_3035_);
v___x_3367_ = lean_box(0);
lean_inc(v___y_3039_);
lean_inc_ref(v___y_3038_);
v___x_3368_ = lean_apply_4(v___f_3036_, v___x_3367_, v___y_3038_, v___y_3039_, lean_box(0));
v___y_3223_ = v_a_3243_;
v___y_3224_ = v___x_3304_;
v___y_3225_ = v___x_3368_;
goto v___jp_3222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3482_, lean_object* v___f_3483_, lean_object* v_name_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3482_, v___f_3483_, v_name_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
return v_res_3488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = lean_unsigned_to_nat(3137104340u);
v___x_3534_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3535_ = l_Lean_Name_num___override(v___x_3534_, v___x_3533_);
return v___x_3535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3538_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3539_ = l_Lean_Name_str___override(v___x_3538_, v___x_3537_);
return v___x_3539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3542_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3543_ = l_Lean_Name_str___override(v___x_3542_, v___x_3541_);
return v___x_3543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = lean_unsigned_to_nat(2u);
v___x_3545_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3546_ = l_Lean_Name_num___override(v___x_3545_, v___x_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3548_; lean_object* v___x_3549_; 
v___f_3548_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3549_ = l_Lean_registerReservedNameAction(v___f_3548_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v___x_3550_; uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec_ref_known(v___x_3549_, 1);
v___x_3550_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3551_ = 0;
v___x_3552_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3553_ = l_Lean_registerTraceClass(v___x_3550_, v___x_3551_, v___x_3552_);
return v___x_3553_;
}
else
{
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3556_, lean_object* v_x_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3557_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3562_, lean_object* v_x_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3562_, v_x_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
return v_res_3567_;
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
