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
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_backward_defeqAttrib_useBackward;
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
static lean_once_cell_t l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isEqnReservedNameSuffix___closed__0;
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
static lean_object* _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_191_ = lean_string_utf8_byte_size(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_193_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_194_ = lean_string_utf8_byte_size(v_s_192_);
v___x_195_ = lean_obj_once(&l_Lean_Meta_isEqnReservedNameSuffix___closed__0, &l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0);
v___x_196_ = lean_nat_dec_le(v___x_195_, v___x_194_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_s_192_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_string_memcmp(v_s_192_, v___x_193_, v___x_197_, v___x_197_, v___x_195_);
if (v___x_198_ == 0)
{
lean_dec_ref(v_s_192_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_199_ = lean_unsigned_to_nat(3u);
lean_inc_ref(v_s_192_);
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v_s_192_);
lean_ctor_set(v___x_200_, 1, v___x_197_);
lean_ctor_set(v___x_200_, 2, v___x_194_);
v___x_201_ = l_String_Slice_Pos_nextn(v___x_200_, v___x_197_, v___x_199_);
lean_dec_ref_known(v___x_200_, 3);
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_s_192_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_ctor_set(v___x_202_, 2, v___x_194_);
v___x_203_ = l_String_Slice_isNat(v___x_202_);
lean_dec_ref_known(v___x_202_, 3);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_213_ = lean_string_dec_eq(v_s_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_215_ = lean_string_dec_eq(v_s_211_, v___x_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_211_);
return v___x_216_;
}
else
{
lean_dec_ref(v_s_211_);
return v___x_215_;
}
}
else
{
lean_dec_ref(v_s_211_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Meta_isEqnLikeSuffix(v_s_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_223_, lean_object* v_env_224_, uint8_t v___x_225_, lean_object* v_as_x27_226_, lean_object* v_b_227_){
_start:
{
if (lean_obj_tag(v_as_x27_226_) == 0)
{
lean_dec_ref(v_env_224_);
lean_dec_ref(v_str_223_);
lean_inc_ref(v_b_227_);
return v_b_227_;
}
else
{
lean_object* v_head_228_; lean_object* v_tail_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___y_233_; uint8_t v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_head_228_ = lean_ctor_get(v_as_x27_226_, 0);
v_tail_229_ = lean_ctor_get(v_as_x27_226_, 1);
v___x_230_ = lean_box(0);
v___x_231_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_239_ = 0;
lean_inc_ref(v_env_224_);
v___x_240_ = l_Lean_Environment_setExporting(v_env_224_, v___x_239_);
lean_inc(v_head_228_);
v___x_241_ = l_Lean_Environment_isSafeDefinition(v___x_240_, v_head_228_);
if (v___x_241_ == 0)
{
v___y_233_ = v___x_241_;
goto v___jp_232_;
}
else
{
uint8_t v___x_242_; 
lean_inc(v_head_228_);
lean_inc_ref(v_env_224_);
v___x_242_ = l_Lean_Meta_isMatcherCore(v_env_224_, v_head_228_);
if (v___x_242_ == 0)
{
v___y_233_ = v___x_225_;
goto v___jp_232_;
}
else
{
v_as_x27_226_ = v_tail_229_;
v_b_227_ = v___x_231_;
goto _start;
}
}
v___jp_232_:
{
if (v___y_233_ == 0)
{
v_as_x27_226_ = v_tail_229_;
v_b_227_ = v___x_231_;
goto _start;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v_env_224_);
lean_inc(v_head_228_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_head_228_);
lean_ctor_set(v___x_235_, 1, v_str_223_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_230_);
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_244_, lean_object* v_env_245_, lean_object* v___x_246_, lean_object* v_as_x27_247_, lean_object* v_b_248_){
_start:
{
uint8_t v___x_616__boxed_249_; lean_object* v_res_250_; 
v___x_616__boxed_249_ = lean_unbox(v___x_246_);
v_res_250_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_244_, v_env_245_, v___x_616__boxed_249_, v_as_x27_247_, v_b_248_);
lean_dec_ref(v_b_248_);
lean_dec(v_as_x27_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_251_, lean_object* v_name_252_){
_start:
{
if (lean_obj_tag(v_name_252_) == 1)
{
lean_object* v_pre_253_; lean_object* v_str_254_; uint8_t v___x_255_; 
v_pre_253_ = lean_ctor_get(v_name_252_, 0);
lean_inc(v_pre_253_);
v_str_254_ = lean_ctor_get(v_name_252_, 1);
lean_inc_ref_n(v_str_254_, 2);
lean_dec_ref_known(v_name_252_, 2);
v___x_255_ = l_Lean_Meta_isEqnLikeSuffix(v_str_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec_ref(v_str_254_);
lean_dec(v_pre_253_);
lean_dec_ref(v_env_251_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_fst_264_; 
lean_inc(v_pre_253_);
v___x_257_ = l_Lean_privateToUserName(v_pre_253_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v_pre_253_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_box(0);
v___x_262_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_263_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_254_, v_env_251_, v___x_255_, v___x_260_, v___x_262_);
lean_dec_ref_known(v___x_260_, 2);
v_fst_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_fst_264_);
lean_dec_ref(v___x_263_);
if (lean_obj_tag(v_fst_264_) == 0)
{
return v___x_261_;
}
else
{
lean_object* v_val_265_; 
v_val_265_ = lean_ctor_get(v_fst_264_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v_fst_264_, 1);
return v_val_265_;
}
}
}
else
{
lean_object* v___x_266_; 
lean_dec(v_name_252_);
lean_dec_ref(v_env_251_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_267_, lean_object* v_env_268_, uint8_t v___x_269_, lean_object* v_as_270_, lean_object* v_as_x27_271_, lean_object* v_b_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_267_, v_env_268_, v___x_269_, v_as_x27_271_, v_b_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_275_, lean_object* v_env_276_, lean_object* v___x_277_, lean_object* v_as_278_, lean_object* v_as_x27_279_, lean_object* v_b_280_, lean_object* v_a_281_){
_start:
{
uint8_t v___x_687__boxed_282_; lean_object* v_res_283_; 
v___x_687__boxed_282_ = lean_unbox(v___x_277_);
v_res_283_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_275_, v_env_276_, v___x_687__boxed_282_, v_as_278_, v_as_x27_279_, v_b_280_, v_a_281_);
lean_dec_ref(v_b_280_);
lean_dec(v_as_x27_279_);
lean_dec(v_as_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_284_, lean_object* v_declName_285_, lean_object* v_suffix_286_){
_start:
{
uint8_t v_isExposed_287_; lean_object* v_name_288_; 
lean_inc(v_declName_285_);
lean_inc_ref(v_env_284_);
v_isExposed_287_ = l_Lean_Environment_hasExposedBody(v_env_284_, v_declName_285_);
v_name_288_ = l_Lean_Name_str___override(v_declName_285_, v_suffix_286_);
if (v_isExposed_287_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_mkPrivateName(v_env_284_, v_name_288_);
lean_dec_ref(v_env_284_);
return v___x_289_;
}
else
{
lean_dec_ref(v_env_284_);
return v_name_288_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_290_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
lean_ctor_set(v___x_295_, 3, v___x_294_);
lean_ctor_set(v___x_295_, 4, v___x_293_);
lean_ctor_set(v___x_295_, 5, v___x_293_);
lean_ctor_set(v___x_295_, 6, v___x_293_);
lean_ctor_set(v___x_295_, 7, v___x_293_);
lean_ctor_set(v___x_295_, 8, v___x_293_);
lean_ctor_set(v___x_295_, 9, v___x_293_);
lean_ctor_set(v___x_295_, 10, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(32u);
v___x_297_ = lean_mk_empty_array_with_capacity(v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((size_t)5ULL);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_unsigned_to_nat(32u);
v___x_302_ = lean_mk_empty_array_with_capacity(v___x_301_);
v___x_303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_304_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_300_);
lean_ctor_set(v___x_304_, 3, v___x_300_);
lean_ctor_set_usize(v___x_304_, 4, v___x_299_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = lean_box(1);
v___x_306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_307_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
lean_ctor_set(v___x_308_, 2, v___x_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v_toCold_314_; lean_object* v_env_315_; lean_object* v_options_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_313_ = lean_st_ref_get(v___y_311_);
v_toCold_314_ = lean_ctor_get(v___y_310_, 0);
v_env_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_env_315_);
lean_dec(v___x_313_);
v_options_316_ = lean_ctor_get(v_toCold_314_, 2);
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_316_);
v___x_319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_319_, 0, v_env_315_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v_options_316_);
v___x_320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_msgData_309_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_526_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_529_; lean_object* v___f_530_; 
v___x_529_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___f_530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_530_, 0, v___x_529_);
return v___f_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___f_532_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_box(1);
v___x_535_ = l_Lean_registerEnvExtension___redArg(v___f_532_, v___x_533_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_538_, lean_object* v_opt_539_){
_start:
{
lean_object* v_name_540_; lean_object* v_defValue_541_; lean_object* v_map_542_; lean_object* v___x_543_; 
v_name_540_ = lean_ctor_get(v_opt_539_, 0);
v_defValue_541_ = lean_ctor_get(v_opt_539_, 1);
v_map_542_ = lean_ctor_get(v_opts_538_, 0);
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_542_, v_name_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_inc(v_defValue_541_);
return v_defValue_541_;
}
else
{
lean_object* v_val_544_; 
v_val_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v___x_543_, 1);
if (lean_obj_tag(v_val_544_) == 3)
{
lean_object* v_v_545_; 
v_v_545_ = lean_ctor_get(v_val_544_, 0);
lean_inc(v_v_545_);
lean_dec_ref_known(v_val_544_, 1);
return v_v_545_;
}
else
{
lean_dec(v_val_544_);
lean_inc(v_defValue_541_);
return v_defValue_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_546_, lean_object* v_opt_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_546_, v_opt_547_);
lean_dec_ref(v_opt_547_);
lean_dec_ref(v_opts_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_as_552_, size_t v_sz_553_, size_t v_i_554_, lean_object* v_b_555_){
_start:
{
lean_object* v_a_557_; uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_lt(v_i_554_, v_sz_553_);
if (v___x_561_ == 0)
{
return v_b_555_;
}
else
{
lean_object* v_a_562_; lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v_map_565_; uint8_t v_hasTrace_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_579_; 
v_a_562_ = lean_array_uget_borrowed(v_as_552_, v_i_554_);
v_fst_563_ = lean_ctor_get(v_a_562_, 0);
v_snd_564_ = lean_ctor_get(v_a_562_, 1);
v_map_565_ = lean_ctor_get(v_b_555_, 0);
v_hasTrace_566_ = lean_ctor_get_uint8(v_b_555_, sizeof(void*)*1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_b_555_);
if (v_isSharedCheck_579_ == 0)
{
v___x_568_ = v_b_555_;
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_map_565_);
lean_dec(v_b_555_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; 
lean_inc(v_snd_564_);
lean_inc(v_fst_563_);
v___x_570_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_563_, v_snd_564_, v_map_565_);
if (v_hasTrace_566_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_574_; 
v___x_571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_572_ = l_Lean_Name_isPrefixOf(v___x_571_, v_fst_563_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_574_ = v___x_568_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_570_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*1, v___x_572_);
v_a_557_ = v___x_574_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_577_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_577_ = v___x_568_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_570_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*1, v_hasTrace_566_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v_a_557_ = v___x_577_;
goto v___jp_556_;
}
}
}
}
v___jp_556_:
{
size_t v___x_558_; size_t v___x_559_; 
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_554_, v___x_558_);
v_i_554_ = v___x_559_;
v_b_555_ = v_a_557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_as_580_, lean_object* v_sz_581_, lean_object* v_i_582_, lean_object* v_b_583_){
_start:
{
size_t v_sz_boxed_584_; size_t v_i_boxed_585_; lean_object* v_res_586_; 
v_sz_boxed_584_ = lean_unbox_usize(v_sz_581_);
lean_dec(v_sz_581_);
v_i_boxed_585_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_as_580_, v_sz_boxed_584_, v_i_boxed_585_, v_b_583_);
lean_dec_ref(v_as_580_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_587_, lean_object* v_k_588_, uint8_t v_v_589_){
_start:
{
lean_object* v_map_590_; uint8_t v_hasTrace_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_605_; 
v_map_590_ = lean_ctor_get(v_o_587_, 0);
v_hasTrace_591_ = lean_ctor_get_uint8(v_o_587_, sizeof(void*)*1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_o_587_);
if (v_isSharedCheck_605_ == 0)
{
v___x_593_ = v_o_587_;
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_map_590_);
lean_dec(v_o_587_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_595_, 0, v_v_589_);
lean_inc(v_k_588_);
v___x_596_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_588_, v___x_595_, v_map_590_);
if (v_hasTrace_591_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_600_; 
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_598_ = l_Lean_Name_isPrefixOf(v___x_597_, v_k_588_);
lean_dec(v_k_588_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_600_ = v___x_593_;
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
return v___x_600_;
}
}
else
{
lean_object* v___x_603_; 
lean_dec(v_k_588_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_603_ = v___x_593_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_596_);
lean_ctor_set_uint8(v_reuseFailAlloc_604_, sizeof(void*)*1, v_hasTrace_591_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_606_, lean_object* v_k_607_, lean_object* v_v_608_){
_start:
{
uint8_t v_v_boxed_609_; lean_object* v_res_610_; 
v_v_boxed_609_ = lean_unbox(v_v_608_);
v_res_610_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_606_, v_k_607_, v_v_boxed_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_611_, lean_object* v_opt_612_, uint8_t v_val_613_){
_start:
{
lean_object* v_name_614_; lean_object* v___x_615_; 
v_name_614_ = lean_ctor_get(v_opt_612_, 0);
lean_inc(v_name_614_);
lean_dec_ref(v_opt_612_);
v___x_615_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_611_, v_name_614_, v_val_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_616_, lean_object* v_opt_617_, lean_object* v_val_618_){
_start:
{
uint8_t v_val_boxed_619_; lean_object* v_res_620_; 
v_val_boxed_619_ = lean_unbox(v_val_618_);
v_res_620_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_616_, v_opt_617_, v_val_boxed_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_621_, size_t v_i_622_, size_t v_stop_623_, lean_object* v_b_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_eq(v_i_622_, v_stop_623_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v_defValue_627_; uint8_t v___x_628_; lean_object* v___x_629_; size_t v___x_630_; size_t v___x_631_; 
v___x_626_ = lean_array_uget_borrowed(v_as_621_, v_i_622_);
v_defValue_627_ = lean_ctor_get(v___x_626_, 1);
v___x_628_ = lean_unbox(v_defValue_627_);
lean_inc(v___x_626_);
v___x_629_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_624_, v___x_626_, v___x_628_);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_622_, v___x_630_);
v_i_622_ = v___x_631_;
v_b_624_ = v___x_629_;
goto _start;
}
else
{
return v_b_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_633_, lean_object* v_i_634_, lean_object* v_stop_635_, lean_object* v_b_636_){
_start:
{
size_t v_i_boxed_637_; size_t v_stop_boxed_638_; lean_object* v_res_639_; 
v_i_boxed_637_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_stop_boxed_638_ = lean_unbox_usize(v_stop_635_);
lean_dec(v_stop_635_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v_as_633_, v_i_boxed_637_, v_stop_boxed_638_, v_b_636_);
lean_dec_ref(v_as_633_);
return v_res_639_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Array_instInhabited___redArg();
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = l_Lean_Meta_eqnAffectingOptions;
v___x_646_ = lean_array_get_size(v___x_645_);
return v___x_646_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_nat_dec_lt(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_651_ = lean_nat_dec_le(v___x_650_, v___x_650_);
return v___x_651_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_652_; size_t v___x_653_; 
v___x_652_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_653_ = lean_usize_of_nat(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_654_, lean_object* v_act_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___y_662_; uint16_t v___y_663_; lean_object* v_fileName_664_; lean_object* v_fileMap_665_; lean_object* v_currNamespace_666_; lean_object* v_openDecls_667_; lean_object* v_initHeartbeats_668_; lean_object* v_maxHeartbeats_669_; lean_object* v_quotContext_670_; lean_object* v_currMacroScope_671_; lean_object* v_cancelTk_x3f_672_; lean_object* v_inheritedTraceOptions_673_; lean_object* v_currRecDepth_674_; lean_object* v_ref_675_; uint8_t v_suppressElabErrors_676_; uint8_t v_isRecordingDeps_677_; lean_object* v___y_678_; lean_object* v___y_685_; uint8_t v___y_686_; uint16_t v___y_687_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_env_726_; lean_object* v___x_727_; lean_object* v_toEnvExtension_728_; lean_object* v_toCold_729_; lean_object* v_asyncMode_730_; lean_object* v_currRecDepth_731_; lean_object* v_ref_732_; uint8_t v_suppressElabErrors_733_; uint8_t v_isRecordingDeps_734_; lean_object* v_fileName_735_; lean_object* v_fileMap_736_; lean_object* v_options_737_; lean_object* v_currNamespace_738_; lean_object* v_openDecls_739_; lean_object* v_initHeartbeats_740_; lean_object* v_maxHeartbeats_741_; lean_object* v_quotContext_742_; lean_object* v_currMacroScope_743_; lean_object* v_cancelTk_x3f_744_; lean_object* v_inheritedTraceOptions_745_; lean_object* v___y_747_; uint8_t v___x_758_; lean_object* v___x_759_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
v___x_725_ = lean_st_ref_get(v_a_659_);
v_env_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_ref(v_env_726_);
lean_dec(v___x_725_);
v___x_727_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_728_ = lean_ctor_get(v___x_727_, 0);
v_toCold_729_ = lean_ctor_get(v_a_658_, 0);
v_asyncMode_730_ = lean_ctor_get(v_toEnvExtension_728_, 2);
v_currRecDepth_731_ = lean_ctor_get(v_a_658_, 1);
v_ref_732_ = lean_ctor_get(v_a_658_, 2);
v_suppressElabErrors_733_ = lean_ctor_get_uint8(v_a_658_, sizeof(void*)*3 + 2);
v_isRecordingDeps_734_ = lean_ctor_get_uint8(v_a_658_, sizeof(void*)*3 + 3);
v_fileName_735_ = lean_ctor_get(v_toCold_729_, 0);
v_fileMap_736_ = lean_ctor_get(v_toCold_729_, 1);
v_options_737_ = lean_ctor_get(v_toCold_729_, 2);
v_currNamespace_738_ = lean_ctor_get(v_toCold_729_, 4);
v_openDecls_739_ = lean_ctor_get(v_toCold_729_, 5);
v_initHeartbeats_740_ = lean_ctor_get(v_toCold_729_, 6);
v_maxHeartbeats_741_ = lean_ctor_get(v_toCold_729_, 7);
v_quotContext_742_ = lean_ctor_get(v_toCold_729_, 8);
v_currMacroScope_743_ = lean_ctor_get(v_toCold_729_, 9);
v_cancelTk_x3f_744_ = lean_ctor_get(v_toCold_729_, 10);
v_inheritedTraceOptions_745_ = lean_ctor_get(v_toCold_729_, 11);
v___x_758_ = 0;
v___x_759_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_724_, v___x_727_, v_env_726_, v_declName_654_, v_asyncMode_730_, v___x_758_);
if (lean_obj_tag(v___x_759_) == 1)
{
lean_object* v_val_760_; lean_object* v___y_762_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_val_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_766_ = l_Lean_Meta_eqnAffectingOptions;
v___x_767_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_767_ == 0)
{
lean_inc_ref(v_options_737_);
v___y_762_ = v_options_737_;
goto v___jp_761_;
}
else
{
uint8_t v___x_768_; 
v___x_768_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_768_ == 0)
{
if (v___x_767_ == 0)
{
lean_inc_ref(v_options_737_);
v___y_762_ = v_options_737_;
goto v___jp_761_;
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_737_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_766_, v___x_769_, v___x_770_, v_options_737_);
v___y_762_ = v___x_771_;
goto v___jp_761_;
}
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_737_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_766_, v___x_772_, v___x_773_, v_options_737_);
v___y_762_ = v___x_774_;
goto v___jp_761_;
}
}
v___jp_761_:
{
size_t v_sz_763_; size_t v___x_764_; lean_object* v___x_765_; 
v_sz_763_ = lean_array_size(v_val_760_);
v___x_764_ = ((size_t)0ULL);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2(v_val_760_, v_sz_763_, v___x_764_, v___y_762_);
lean_dec(v_val_760_);
v___y_747_ = v___x_765_;
goto v___jp_746_;
}
}
else
{
lean_object* v___x_775_; uint8_t v___x_776_; 
lean_dec(v___x_759_);
v___x_775_ = l_Lean_Meta_eqnAffectingOptions;
v___x_776_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
if (v___x_776_ == 0)
{
lean_inc_ref(v_options_737_);
v___y_747_ = v_options_737_;
goto v___jp_746_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_777_ == 0)
{
if (v___x_776_ == 0)
{
lean_inc_ref(v_options_737_);
v___y_747_ = v_options_737_;
goto v___jp_746_;
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_737_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_775_, v___x_778_, v___x_779_, v_options_737_);
v___y_747_ = v___x_780_;
goto v___jp_746_;
}
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
lean_inc_ref(v_options_737_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__3(v___x_775_, v___x_781_, v___x_782_, v_options_737_);
v___y_747_ = v___x_783_;
goto v___jp_746_;
}
}
}
v___jp_661_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_679_ = l_Lean_maxRecDepth;
v___x_680_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_662_, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_681_, 0, v_fileName_664_);
lean_ctor_set(v___x_681_, 1, v_fileMap_665_);
lean_ctor_set(v___x_681_, 2, v___y_662_);
lean_ctor_set(v___x_681_, 3, v___x_680_);
lean_ctor_set(v___x_681_, 4, v_currNamespace_666_);
lean_ctor_set(v___x_681_, 5, v_openDecls_667_);
lean_ctor_set(v___x_681_, 6, v_initHeartbeats_668_);
lean_ctor_set(v___x_681_, 7, v_maxHeartbeats_669_);
lean_ctor_set(v___x_681_, 8, v_quotContext_670_);
lean_ctor_set(v___x_681_, 9, v_currMacroScope_671_);
lean_ctor_set(v___x_681_, 10, v_cancelTk_x3f_672_);
lean_ctor_set(v___x_681_, 11, v_inheritedTraceOptions_673_);
lean_inc(v_ref_675_);
lean_inc(v_currRecDepth_674_);
v___x_682_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_currRecDepth_674_);
lean_ctor_set(v___x_682_, 2, v_ref_675_);
lean_ctor_set_uint16(v___x_682_, sizeof(void*)*3, v___y_663_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*3 + 2, v_suppressElabErrors_676_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*3 + 3, v_isRecordingDeps_677_);
lean_inc(v___y_678_);
lean_inc(v_a_657_);
lean_inc_ref(v_a_656_);
v___x_683_ = lean_apply_5(v_act_655_, v_a_656_, v_a_657_, v___x_682_, v___y_678_, lean_box(0));
return v___x_683_;
}
v___jp_684_:
{
lean_object* v___x_688_; lean_object* v_env_689_; lean_object* v_nextMacroScope_690_; lean_object* v_ngen_691_; lean_object* v_auxDeclNGen_692_; lean_object* v_traceState_693_; lean_object* v_recordedDeps_694_; lean_object* v_messages_695_; lean_object* v_infoState_696_; lean_object* v_snapshotTasks_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_722_; 
v___x_688_ = lean_st_ref_take(v_a_659_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
v_nextMacroScope_690_ = lean_ctor_get(v___x_688_, 1);
v_ngen_691_ = lean_ctor_get(v___x_688_, 2);
v_auxDeclNGen_692_ = lean_ctor_get(v___x_688_, 3);
v_traceState_693_ = lean_ctor_get(v___x_688_, 4);
v_recordedDeps_694_ = lean_ctor_get(v___x_688_, 6);
v_messages_695_ = lean_ctor_get(v___x_688_, 7);
v_infoState_696_ = lean_ctor_get(v___x_688_, 8);
v_snapshotTasks_697_ = lean_ctor_get(v___x_688_, 9);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_688_, 5);
lean_dec(v_unused_723_);
v___x_699_ = v___x_688_;
v_isShared_700_ = v_isSharedCheck_722_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snapshotTasks_697_);
lean_inc(v_infoState_696_);
lean_inc(v_messages_695_);
lean_inc(v_recordedDeps_694_);
lean_inc(v_traceState_693_);
lean_inc(v_auxDeclNGen_692_);
lean_inc(v_ngen_691_);
lean_inc(v_nextMacroScope_690_);
lean_inc(v_env_689_);
lean_dec(v___x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_722_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_701_ = l_Lean_Kernel_enableDiag(v_env_689_, v___y_686_);
v___x_702_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 5, v___x_702_);
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_704_ = v___x_699_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_nextMacroScope_690_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_ngen_691_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_auxDeclNGen_692_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_traceState_693_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_recordedDeps_694_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v_messages_695_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v_infoState_696_);
lean_ctor_set(v_reuseFailAlloc_721_, 9, v_snapshotTasks_697_);
v___x_704_ = v_reuseFailAlloc_721_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v_toCold_706_; lean_object* v_currRecDepth_707_; lean_object* v_ref_708_; uint8_t v_suppressElabErrors_709_; uint8_t v_isRecordingDeps_710_; lean_object* v_fileName_711_; lean_object* v_fileMap_712_; lean_object* v_currNamespace_713_; lean_object* v_openDecls_714_; lean_object* v_initHeartbeats_715_; lean_object* v_maxHeartbeats_716_; lean_object* v_quotContext_717_; lean_object* v_currMacroScope_718_; lean_object* v_cancelTk_x3f_719_; lean_object* v_inheritedTraceOptions_720_; 
v___x_705_ = lean_st_ref_put(v_a_659_, v___x_704_);
v_toCold_706_ = lean_ctor_get(v_a_658_, 0);
v_currRecDepth_707_ = lean_ctor_get(v_a_658_, 1);
v_ref_708_ = lean_ctor_get(v_a_658_, 2);
v_suppressElabErrors_709_ = lean_ctor_get_uint8(v_a_658_, sizeof(void*)*3 + 2);
v_isRecordingDeps_710_ = lean_ctor_get_uint8(v_a_658_, sizeof(void*)*3 + 3);
v_fileName_711_ = lean_ctor_get(v_toCold_706_, 0);
v_fileMap_712_ = lean_ctor_get(v_toCold_706_, 1);
v_currNamespace_713_ = lean_ctor_get(v_toCold_706_, 4);
v_openDecls_714_ = lean_ctor_get(v_toCold_706_, 5);
v_initHeartbeats_715_ = lean_ctor_get(v_toCold_706_, 6);
v_maxHeartbeats_716_ = lean_ctor_get(v_toCold_706_, 7);
v_quotContext_717_ = lean_ctor_get(v_toCold_706_, 8);
v_currMacroScope_718_ = lean_ctor_get(v_toCold_706_, 9);
v_cancelTk_x3f_719_ = lean_ctor_get(v_toCold_706_, 10);
v_inheritedTraceOptions_720_ = lean_ctor_get(v_toCold_706_, 11);
lean_inc_ref(v_inheritedTraceOptions_720_);
lean_inc(v_cancelTk_x3f_719_);
lean_inc(v_currMacroScope_718_);
lean_inc(v_quotContext_717_);
lean_inc(v_maxHeartbeats_716_);
lean_inc(v_initHeartbeats_715_);
lean_inc(v_openDecls_714_);
lean_inc(v_currNamespace_713_);
lean_inc_ref(v_fileMap_712_);
lean_inc_ref(v_fileName_711_);
v___y_662_ = v___y_685_;
v___y_663_ = v___y_687_;
v_fileName_664_ = v_fileName_711_;
v_fileMap_665_ = v_fileMap_712_;
v_currNamespace_666_ = v_currNamespace_713_;
v_openDecls_667_ = v_openDecls_714_;
v_initHeartbeats_668_ = v_initHeartbeats_715_;
v_maxHeartbeats_669_ = v_maxHeartbeats_716_;
v_quotContext_670_ = v_quotContext_717_;
v_currMacroScope_671_ = v_currMacroScope_718_;
v_cancelTk_x3f_672_ = v_cancelTk_x3f_719_;
v_inheritedTraceOptions_673_ = v_inheritedTraceOptions_720_;
v_currRecDepth_674_ = v_currRecDepth_707_;
v_ref_675_ = v_ref_708_;
v_suppressElabErrors_676_ = v_suppressElabErrors_709_;
v_isRecordingDeps_677_ = v_isRecordingDeps_710_;
v___y_678_ = v_a_659_;
goto v___jp_661_;
}
}
}
v___jp_746_:
{
uint16_t v___x_748_; lean_object* v___x_749_; lean_object* v_env_750_; uint8_t v___x_751_; uint16_t v___x_752_; uint16_t v___x_753_; uint16_t v___x_754_; uint8_t v___x_755_; 
v___x_748_ = l_Lean_OptionFlags_ofOptions(v___y_747_);
v___x_749_ = lean_st_ref_get(v_a_659_);
v_env_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_env_750_);
lean_dec(v___x_749_);
v___x_751_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_750_);
lean_dec_ref(v_env_750_);
v___x_752_ = 512;
v___x_753_ = lean_uint16_land(v___x_748_, v___x_752_);
v___x_754_ = 0;
v___x_755_ = lean_uint16_dec_eq(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
if (v___x_751_ == 0)
{
uint8_t v___x_756_; 
v___x_756_ = 1;
v___y_685_ = v___y_747_;
v___y_686_ = v___x_756_;
v___y_687_ = v___x_748_;
goto v___jp_684_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_745_);
lean_inc(v_cancelTk_x3f_744_);
lean_inc(v_currMacroScope_743_);
lean_inc(v_quotContext_742_);
lean_inc(v_maxHeartbeats_741_);
lean_inc(v_initHeartbeats_740_);
lean_inc(v_openDecls_739_);
lean_inc(v_currNamespace_738_);
lean_inc_ref(v_fileMap_736_);
lean_inc_ref(v_fileName_735_);
v___y_662_ = v___y_747_;
v___y_663_ = v___x_748_;
v_fileName_664_ = v_fileName_735_;
v_fileMap_665_ = v_fileMap_736_;
v_currNamespace_666_ = v_currNamespace_738_;
v_openDecls_667_ = v_openDecls_739_;
v_initHeartbeats_668_ = v_initHeartbeats_740_;
v_maxHeartbeats_669_ = v_maxHeartbeats_741_;
v_quotContext_670_ = v_quotContext_742_;
v_currMacroScope_671_ = v_currMacroScope_743_;
v_cancelTk_x3f_672_ = v_cancelTk_x3f_744_;
v_inheritedTraceOptions_673_ = v_inheritedTraceOptions_745_;
v_currRecDepth_674_ = v_currRecDepth_731_;
v_ref_675_ = v_ref_732_;
v_suppressElabErrors_676_ = v_suppressElabErrors_733_;
v_isRecordingDeps_677_ = v_isRecordingDeps_734_;
v___y_678_ = v_a_659_;
goto v___jp_661_;
}
}
else
{
if (v___x_751_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_745_);
lean_inc(v_cancelTk_x3f_744_);
lean_inc(v_currMacroScope_743_);
lean_inc(v_quotContext_742_);
lean_inc(v_maxHeartbeats_741_);
lean_inc(v_initHeartbeats_740_);
lean_inc(v_openDecls_739_);
lean_inc(v_currNamespace_738_);
lean_inc_ref(v_fileMap_736_);
lean_inc_ref(v_fileName_735_);
v___y_662_ = v___y_747_;
v___y_663_ = v___x_748_;
v_fileName_664_ = v_fileName_735_;
v_fileMap_665_ = v_fileMap_736_;
v_currNamespace_666_ = v_currNamespace_738_;
v_openDecls_667_ = v_openDecls_739_;
v_initHeartbeats_668_ = v_initHeartbeats_740_;
v_maxHeartbeats_669_ = v_maxHeartbeats_741_;
v_quotContext_670_ = v_quotContext_742_;
v_currMacroScope_671_ = v_currMacroScope_743_;
v_cancelTk_x3f_672_ = v_cancelTk_x3f_744_;
v_inheritedTraceOptions_673_ = v_inheritedTraceOptions_745_;
v_currRecDepth_674_ = v_currRecDepth_731_;
v_ref_675_ = v_ref_732_;
v_suppressElabErrors_676_ = v_suppressElabErrors_733_;
v_isRecordingDeps_677_ = v_isRecordingDeps_734_;
v___y_678_ = v_a_659_;
goto v___jp_661_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
v___y_685_ = v___y_747_;
v___y_686_ = v___x_757_;
v___y_687_ = v___x_748_;
goto v___jp_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_784_, lean_object* v_act_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_784_, v_act_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_792_, lean_object* v_declName_793_, lean_object* v_act_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_793_, v_act_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_801_, lean_object* v_declName_802_, lean_object* v_act_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_801_, v_declName_802_, v_act_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v_env_814_; lean_object* v_toConstantVal_815_; lean_object* v_value_816_; lean_object* v_all_817_; uint8_t v___y_819_; lean_object* v_type_827_; uint8_t v___x_828_; 
v___x_813_ = lean_st_ref_get(v___y_811_);
v_env_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc_ref_n(v_env_814_, 2);
lean_dec(v___x_813_);
v_toConstantVal_815_ = lean_ctor_get(v_thm_810_, 0);
v_value_816_ = lean_ctor_get(v_thm_810_, 1);
v_all_817_ = lean_ctor_get(v_thm_810_, 2);
v_type_827_ = lean_ctor_get(v_toConstantVal_815_, 2);
v___x_828_ = l_Lean_Environment_hasUnsafe(v_env_814_, v_type_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_Environment_hasUnsafe(v_env_814_, v_value_816_);
v___y_819_ = v___x_829_;
goto v___jp_818_;
}
else
{
lean_dec_ref(v_env_814_);
v___y_819_ = v___x_828_;
goto v___jp_818_;
}
v___jp_818_:
{
if (v___y_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_820_, 0, v_thm_810_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_inc(v_all_817_);
lean_inc_ref(v_value_816_);
lean_inc_ref(v_toConstantVal_815_);
lean_dec_ref(v_thm_810_);
v___x_822_ = lean_box(0);
v___x_823_ = 0;
v___x_824_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_824_, 0, v_toConstantVal_815_);
lean_ctor_set(v___x_824_, 1, v_value_816_);
lean_ctor_set(v___x_824_, 2, v___x_822_);
lean_ctor_set(v___x_824_, 3, v_all_817_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*4, v___x_823_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_830_, v___y_831_);
lean_dec(v___y_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_834_, v___y_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_848_, lean_object* v_b_849_, lean_object* v_c_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
v___x_856_ = lean_apply_7(v_k_848_, v_b_849_, v_c_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, lean_box(0));
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_857_, lean_object* v_b_858_, lean_object* v_c_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_857_, v_b_858_, v_c_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_866_, lean_object* v_k_867_, uint8_t v_cleanupAnnotations_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___f_874_; uint8_t v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_874_, 0, v_k_867_);
v___x_875_ = 1;
v___x_876_ = 0;
v___x_877_ = lean_box(0);
v___x_878_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_866_, v___x_875_, v___x_876_, v___x_875_, v___x_876_, v___x_877_, v___f_874_, v_cleanupAnnotations_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_878_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_878_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_895_, lean_object* v_k_896_, lean_object* v_cleanupAnnotations_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_903_; lean_object* v_res_904_; 
v_cleanupAnnotations_boxed_903_ = lean_unbox(v_cleanupAnnotations_897_);
v_res_904_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_895_, v_k_896_, v_cleanupAnnotations_boxed_903_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_905_, lean_object* v_e_906_, lean_object* v_k_907_, uint8_t v_cleanupAnnotations_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_906_, v_k_907_, v_cleanupAnnotations_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_915_, lean_object* v_e_916_, lean_object* v_k_917_, lean_object* v_cleanupAnnotations_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_924_; lean_object* v_res_925_; 
v_cleanupAnnotations_boxed_924_ = lean_unbox(v_cleanupAnnotations_918_);
v_res_925_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_915_, v_e_916_, v_k_917_, v_cleanupAnnotations_boxed_924_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
if (lean_obj_tag(v_a_926_) == 0)
{
lean_object* v___x_928_; 
v___x_928_ = l_List_reverse___redArg(v_a_927_);
return v___x_928_;
}
else
{
lean_object* v_head_929_; lean_object* v_tail_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_939_; 
v_head_929_ = lean_ctor_get(v_a_926_, 0);
v_tail_930_ = lean_ctor_get(v_a_926_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_939_ == 0)
{
v___x_932_ = v_a_926_;
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_tail_930_);
lean_inc(v_head_929_);
lean_dec(v_a_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = l_Lean_mkLevelParam(v_head_929_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_a_927_);
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_a_927_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v_a_926_ = v_tail_930_;
v_a_927_ = v___x_936_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_940_, lean_object* v_name_941_, lean_object* v_xs_942_, lean_object* v_body_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_name_949_; lean_object* v_levelParams_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1020_; 
v_name_949_ = lean_ctor_get(v_toConstantVal_940_, 0);
v_levelParams_950_ = lean_ctor_get(v_toConstantVal_940_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_toConstantVal_940_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_toConstantVal_940_, 2);
lean_dec(v_unused_1021_);
v___x_952_ = v_toConstantVal_940_;
v_isShared_953_ = v_isSharedCheck_1020_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_levelParams_950_);
lean_inc(v_name_949_);
lean_dec(v_toConstantVal_940_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1020_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_lhs_957_; lean_object* v___x_958_; 
v___x_954_ = lean_box(0);
lean_inc(v_levelParams_950_);
v___x_955_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_950_, v___x_954_);
v___x_956_ = l_Lean_mkConst(v_name_949_, v___x_955_);
v_lhs_957_ = l_Lean_mkAppN(v___x_956_, v_xs_942_);
lean_inc_ref(v_lhs_957_);
v___x_958_ = l_Lean_Meta_mkEq(v_lhs_957_, v_body_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; uint8_t v___x_960_; uint8_t v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = 0;
v___x_961_ = 1;
v___x_962_ = 1;
v___x_963_ = l_Lean_Meta_mkForallFVars(v_xs_942_, v_a_959_, v___x_960_, v___x_961_, v___x_961_, v___x_962_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = l_Lean_Meta_letToHave(v_a_964_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Meta_mkEqRefl(v_lhs_957_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = l_Lean_Meta_mkLambdaFVars(v_xs_942_, v_a_968_, v___x_960_, v___x_961_, v___x_960_, v___x_961_, v___x_962_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
lean_inc(v_name_941_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 2, v_a_966_);
lean_ctor_set(v___x_952_, 0, v_name_941_);
v___x_972_ = v___x_952_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_name_941_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_levelParams_950_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_a_966_);
v___x_972_ = v_reuseFailAlloc_979_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_977_; 
lean_inc(v_name_941_);
v___x_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_973_, 0, v_name_941_);
lean_ctor_set(v___x_973_, 1, v___x_954_);
v___x_974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v_a_970_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
v___x_975_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_974_, v___y_947_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_Lean_addDecl(v_a_976_, v___x_960_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; 
lean_dec_ref_known(v___x_977_, 1);
v___x_978_ = l_Lean_inferDefEqAttr(v_name_941_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_978_;
}
else
{
lean_dec(v_name_941_);
return v___x_977_;
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_a_966_);
lean_del_object(v___x_952_);
lean_dec(v_levelParams_950_);
lean_dec(v_name_941_);
v_a_980_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_969_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_969_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_a_966_);
lean_del_object(v___x_952_);
lean_dec(v_levelParams_950_);
lean_dec(v_name_941_);
v_a_988_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_967_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_967_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_lhs_957_);
lean_del_object(v___x_952_);
lean_dec(v_levelParams_950_);
lean_dec(v_name_941_);
v_a_996_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_965_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_965_);
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
lean_dec_ref(v_lhs_957_);
lean_del_object(v___x_952_);
lean_dec(v_levelParams_950_);
lean_dec(v_name_941_);
v_a_1004_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_963_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_963_);
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
lean_dec_ref(v_lhs_957_);
lean_del_object(v___x_952_);
lean_dec(v_levelParams_950_);
lean_dec(v_name_941_);
v_a_1012_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_958_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_958_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1022_, lean_object* v_name_1023_, lean_object* v_xs_1024_, lean_object* v_body_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1022_, v_name_1023_, v_xs_1024_, v_body_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v_xs_1024_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1032_, lean_object* v_info_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_toConstantVal_1039_; lean_object* v_value_1040_; lean_object* v___f_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; 
v_toConstantVal_1039_ = lean_ctor_get(v_info_1033_, 0);
lean_inc_ref(v_toConstantVal_1039_);
v_value_1040_ = lean_ctor_get(v_info_1033_, 1);
lean_inc_ref(v_value_1040_);
lean_dec_ref(v_info_1033_);
v___f_1041_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1041_, 0, v_toConstantVal_1039_);
lean_closure_set(v___f_1041_, 1, v_name_1032_);
v___x_1042_ = 1;
v___x_1043_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1040_, v___f_1041_, v___x_1042_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1044_, lean_object* v_info_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1044_, v_info_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1052_, lean_object* v_name_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1062_; lean_object* v_env_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_st_ref_get(v_a_1057_);
v_env_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_ref(v_env_1063_);
lean_dec(v___x_1062_);
v___x_1064_ = 0;
lean_inc(v_declName_1052_);
v___x_1065_ = l_Lean_Environment_find_x3f(v_env_1063_, v_declName_1052_, v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 1)
{
lean_object* v_val_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1093_; 
v_val_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1093_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_val_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1093_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
if (lean_obj_tag(v_val_1066_) == 1)
{
lean_object* v_val_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_val_1070_ = lean_ctor_get(v_val_1066_, 0);
lean_inc_ref(v_val_1070_);
lean_dec_ref_known(v_val_1066_, 1);
lean_inc_n(v_name_1053_, 2);
v___x_1071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1071_, 0, v_name_1053_);
lean_closure_set(v___x_1071_, 1, v_val_1070_);
lean_inc(v_declName_1052_);
v___x_1072_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1072_, 0, lean_box(0));
lean_closure_set(v___x_1072_, 1, v_declName_1052_);
lean_closure_set(v___x_1072_, 2, v___x_1071_);
v___x_1073_ = l_Lean_Meta_realizeConst(v_declName_1052_, v_name_1053_, v___x_1072_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1083_; 
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1084_);
v___x_1075_ = v___x_1073_;
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v___x_1073_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v_name_1053_);
v___x_1078_ = v___x_1068_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_name_1053_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
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
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_del_object(v___x_1068_);
lean_dec(v_name_1053_);
v_a_1085_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1073_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1073_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
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
lean_del_object(v___x_1068_);
lean_dec(v_val_1066_);
lean_dec(v_name_1053_);
lean_dec(v_declName_1052_);
goto v___jp_1059_;
}
}
}
else
{
lean_dec(v___x_1065_);
lean_dec(v_name_1053_);
lean_dec(v_declName_1052_);
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1094_, lean_object* v_name_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1094_, v_name_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1102_, lean_object* v_vals_1103_, lean_object* v_i_1104_, lean_object* v_k_1105_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_array_get_size(v_keys_1102_);
v___x_1107_ = lean_nat_dec_lt(v_i_1104_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_i_1104_);
v___x_1108_ = lean_box(0);
return v___x_1108_;
}
else
{
lean_object* v_k_x27_1109_; uint8_t v___x_1110_; 
v_k_x27_1109_ = lean_array_fget_borrowed(v_keys_1102_, v_i_1104_);
v___x_1110_ = lean_name_eq(v_k_1105_, v_k_x27_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_i_1104_, v___x_1111_);
lean_dec(v_i_1104_);
v_i_1104_ = v___x_1112_;
goto _start;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_array_fget_borrowed(v_vals_1103_, v_i_1104_);
lean_dec(v_i_1104_);
lean_inc(v___x_1114_);
v___x_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_i_1118_, lean_object* v_k_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1116_, v_vals_1117_, v_i_1118_, v_k_1119_);
lean_dec(v_k_1119_);
lean_dec_ref(v_vals_1117_);
lean_dec_ref(v_keys_1116_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1121_, size_t v_x_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
lean_object* v_es_1124_; lean_object* v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; lean_object* v_j_1128_; lean_object* v___x_1129_; 
v_es_1124_ = lean_ctor_get(v_x_1121_, 0);
v___x_1125_ = lean_box(2);
v___x_1126_ = ((size_t)31ULL);
v___x_1127_ = lean_usize_land(v_x_1122_, v___x_1126_);
v_j_1128_ = lean_usize_to_nat(v___x_1127_);
v___x_1129_ = lean_array_get_borrowed(v___x_1125_, v_es_1124_, v_j_1128_);
lean_dec(v_j_1128_);
switch(lean_obj_tag(v___x_1129_))
{
case 0:
{
lean_object* v_key_1130_; lean_object* v_val_1131_; uint8_t v___x_1132_; 
v_key_1130_ = lean_ctor_get(v___x_1129_, 0);
v_val_1131_ = lean_ctor_get(v___x_1129_, 1);
v___x_1132_ = lean_name_eq(v_x_1123_, v_key_1130_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_box(0);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
lean_inc(v_val_1131_);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_val_1131_);
return v___x_1134_;
}
}
case 1:
{
lean_object* v_node_1135_; size_t v___x_1136_; size_t v___x_1137_; 
v_node_1135_ = lean_ctor_get(v___x_1129_, 0);
v___x_1136_ = ((size_t)5ULL);
v___x_1137_ = lean_usize_shift_right(v_x_1122_, v___x_1136_);
v_x_1121_ = v_node_1135_;
v_x_1122_ = v___x_1137_;
goto _start;
}
default: 
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_box(0);
return v___x_1139_;
}
}
}
else
{
lean_object* v_ks_1140_; lean_object* v_vs_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_ks_1140_ = lean_ctor_get(v_x_1121_, 0);
v_vs_1141_ = lean_ctor_get(v_x_1121_, 1);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1140_, v_vs_1141_, v___x_1142_, v_x_1123_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
size_t v_x_342__boxed_1147_; lean_object* v_res_1148_; 
v_x_342__boxed_1147_ = lean_unbox_usize(v_x_1145_);
lean_dec(v_x_1145_);
v_res_1148_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1144_, v_x_342__boxed_1147_, v_x_1146_);
lean_dec(v_x_1146_);
lean_dec_ref(v_x_1144_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
uint64_t v___y_1152_; 
if (lean_obj_tag(v_x_1150_) == 0)
{
uint64_t v___x_1155_; 
v___x_1155_ = 1723ULL;
v___y_1152_ = v___x_1155_;
goto v___jp_1151_;
}
else
{
uint64_t v_hash_1156_; 
v_hash_1156_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*2);
v___y_1152_ = v_hash_1156_;
goto v___jp_1151_;
}
v___jp_1151_:
{
size_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_uint64_to_usize(v___y_1152_);
v___x_1154_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1149_, v___x_1153_, v_x_1150_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1157_, v_x_1158_);
lean_dec(v_x_1158_);
lean_dec_ref(v_x_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_env_1165_; lean_object* v___x_1166_; lean_object* v_asyncMode_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1163_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1164_ = lean_st_ref_get(v_a_1161_);
v_env_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_ref(v_env_1165_);
lean_dec(v___x_1164_);
v___x_1166_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1167_ = lean_ctor_get(v___x_1166_, 2);
v___x_1168_ = lean_box(0);
v___x_1169_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1163_, v___x_1166_, v_env_1165_, v_asyncMode_1167_, v___x_1168_);
v___x_1170_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1169_, v_thmName_1160_);
lean_dec(v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1172_, v_a_1173_);
lean_dec(v_a_1173_);
lean_dec(v_thmName_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1176_, v_a_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_thmName_1181_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1187_, v_x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1190_, v_x_1191_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec_ref(v_x_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1194_, lean_object* v_x_1195_, size_t v_x_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1195_, v_x_1196_, v_x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
size_t v_x_435__boxed_1203_; lean_object* v_res_1204_; 
v_x_435__boxed_1203_ = lean_unbox_usize(v_x_1201_);
lean_dec(v_x_1201_);
v_res_1204_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1199_, v_x_1200_, v_x_435__boxed_1203_, v_x_1202_);
lean_dec(v_x_1202_);
lean_dec_ref(v_x_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1205_, lean_object* v_keys_1206_, lean_object* v_vals_1207_, lean_object* v_heq_1208_, lean_object* v_i_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1206_, v_vals_1207_, v_i_1209_, v_k_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1212_, lean_object* v_keys_1213_, lean_object* v_vals_1214_, lean_object* v_heq_1215_, lean_object* v_i_1216_, lean_object* v_k_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1212_, v_keys_1213_, v_vals_1214_, v_heq_1215_, v_i_1216_, v_k_1217_);
lean_dec(v_k_1217_);
lean_dec_ref(v_vals_1214_);
lean_dec_ref(v_keys_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1219_, lean_object* v_i_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_array_get_size(v_keys_1219_);
v___x_1223_ = lean_nat_dec_lt(v_i_1220_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec(v_i_1220_);
return v___x_1223_;
}
else
{
lean_object* v_k_x27_1224_; uint8_t v___x_1225_; 
v_k_x27_1224_ = lean_array_fget_borrowed(v_keys_1219_, v_i_1220_);
v___x_1225_ = lean_name_eq(v_k_1221_, v_k_x27_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_add(v_i_1220_, v___x_1226_);
lean_dec(v_i_1220_);
v_i_1220_ = v___x_1227_;
goto _start;
}
else
{
lean_dec(v_i_1220_);
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1229_, lean_object* v_i_1230_, lean_object* v_k_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1229_, v_i_1230_, v_k_1231_);
lean_dec(v_k_1231_);
lean_dec_ref(v_keys_1229_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1234_, size_t v_x_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_object* v_es_1237_; lean_object* v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; lean_object* v_j_1241_; lean_object* v___x_1242_; 
v_es_1237_ = lean_ctor_get(v_x_1234_, 0);
v___x_1238_ = lean_box(2);
v___x_1239_ = ((size_t)31ULL);
v___x_1240_ = lean_usize_land(v_x_1235_, v___x_1239_);
v_j_1241_ = lean_usize_to_nat(v___x_1240_);
v___x_1242_ = lean_array_get_borrowed(v___x_1238_, v_es_1237_, v_j_1241_);
lean_dec(v_j_1241_);
switch(lean_obj_tag(v___x_1242_))
{
case 0:
{
lean_object* v_key_1243_; uint8_t v___x_1244_; 
v_key_1243_ = lean_ctor_get(v___x_1242_, 0);
v___x_1244_ = lean_name_eq(v_x_1236_, v_key_1243_);
return v___x_1244_;
}
case 1:
{
lean_object* v_node_1245_; size_t v___x_1246_; size_t v___x_1247_; 
v_node_1245_ = lean_ctor_get(v___x_1242_, 0);
v___x_1246_ = ((size_t)5ULL);
v___x_1247_ = lean_usize_shift_right(v_x_1235_, v___x_1246_);
v_x_1234_ = v_node_1245_;
v_x_1235_ = v___x_1247_;
goto _start;
}
default: 
{
uint8_t v___x_1249_; 
v___x_1249_ = 0;
return v___x_1249_;
}
}
}
else
{
lean_object* v_ks_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_ks_1250_ = lean_ctor_get(v_x_1234_, 0);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1250_, v___x_1251_, v_x_1236_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
size_t v_x_326__boxed_1256_; uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_x_326__boxed_1256_ = lean_unbox_usize(v_x_1254_);
lean_dec(v_x_1254_);
v_res_1257_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1253_, v_x_326__boxed_1256_, v_x_1255_);
lean_dec(v_x_1255_);
lean_dec_ref(v_x_1253_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
uint64_t v___y_1262_; 
if (lean_obj_tag(v_x_1260_) == 0)
{
uint64_t v___x_1265_; 
v___x_1265_ = 1723ULL;
v___y_1262_ = v___x_1265_;
goto v___jp_1261_;
}
else
{
uint64_t v_hash_1266_; 
v_hash_1266_ = lean_ctor_get_uint64(v_x_1260_, sizeof(void*)*2);
v___y_1262_ = v_hash_1266_;
goto v___jp_1261_;
}
v___jp_1261_:
{
size_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_uint64_to_usize(v___y_1262_);
v___x_1264_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1259_, v___x_1263_, v_x_1260_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1267_, v_x_1268_);
lean_dec(v_x_1268_);
lean_dec_ref(v_x_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_env_1276_; lean_object* v___x_1277_; lean_object* v_asyncMode_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1274_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1275_ = lean_st_ref_get(v_a_1272_);
v_env_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc_ref(v_env_1276_);
lean_dec(v___x_1275_);
v___x_1277_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1278_ = lean_ctor_get(v___x_1277_, 2);
v___x_1279_ = lean_box(0);
v___x_1280_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1274_, v___x_1277_, v_env_1276_, v_asyncMode_1278_, v___x_1279_);
v___x_1281_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1280_, v_thmName_1271_);
lean_dec(v___x_1280_);
v___x_1282_ = lean_box(v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1284_, v_a_1285_);
lean_dec(v_a_1285_);
lean_dec(v_thmName_1284_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1288_, v_a_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Meta_isEqnThm(v_thmName_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_thmName_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1302_, v_x_1303_, v_x_1304_);
lean_dec(v_x_1304_);
lean_dec_ref(v_x_1303_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1307_, lean_object* v_x_1308_, size_t v_x_1309_, lean_object* v_x_1310_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1308_, v_x_1309_, v_x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
size_t v_x_415__boxed_1316_; uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_x_415__boxed_1316_ = lean_unbox_usize(v_x_1314_);
lean_dec(v_x_1314_);
v_res_1317_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1312_, v_x_1313_, v_x_415__boxed_1316_, v_x_1315_);
lean_dec(v_x_1315_);
lean_dec_ref(v_x_1313_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1319_, lean_object* v_keys_1320_, lean_object* v_vals_1321_, lean_object* v_heq_1322_, lean_object* v_i_1323_, lean_object* v_k_1324_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1320_, v_i_1323_, v_k_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1326_, lean_object* v_keys_1327_, lean_object* v_vals_1328_, lean_object* v_heq_1329_, lean_object* v_i_1330_, lean_object* v_k_1331_){
_start:
{
uint8_t v_res_1332_; lean_object* v_r_1333_; 
v_res_1332_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1326_, v_keys_1327_, v_vals_1328_, v_heq_1329_, v_i_1330_, v_k_1331_);
lean_dec(v_k_1331_);
lean_dec_ref(v_vals_1328_);
lean_dec_ref(v_keys_1327_);
v_r_1333_ = lean_box(v_res_1332_);
return v_r_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v_ks_1338_; lean_object* v_vs_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1363_; 
v_ks_1338_ = lean_ctor_get(v_x_1334_, 0);
v_vs_1339_ = lean_ctor_get(v_x_1334_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1334_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1341_ = v_x_1334_;
v_isShared_1342_ = v_isSharedCheck_1363_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_vs_1339_);
lean_inc(v_ks_1338_);
lean_dec(v_x_1334_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1363_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = lean_array_get_size(v_ks_1338_);
v___x_1344_ = lean_nat_dec_lt(v_x_1335_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec(v_x_1335_);
v___x_1345_ = lean_array_push(v_ks_1338_, v_x_1336_);
v___x_1346_ = lean_array_push(v_vs_1339_, v_x_1337_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1346_);
lean_ctor_set(v___x_1341_, 0, v___x_1345_);
v___x_1348_ = v___x_1341_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
lean_object* v_k_x27_1350_; uint8_t v___x_1351_; 
v_k_x27_1350_ = lean_array_fget_borrowed(v_ks_1338_, v_x_1335_);
v___x_1351_ = lean_name_eq(v_x_1336_, v_k_x27_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1353_; 
if (v_isShared_1342_ == 0)
{
v___x_1353_ = v___x_1341_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_ks_1338_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_vs_1339_);
v___x_1353_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_nat_add(v_x_1335_, v___x_1354_);
lean_dec(v_x_1335_);
v_x_1334_ = v___x_1353_;
v_x_1335_ = v___x_1355_;
goto _start;
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1358_ = lean_array_fset(v_ks_1338_, v_x_1335_, v_x_1336_);
v___x_1359_ = lean_array_fset(v_vs_1339_, v_x_1335_, v_x_1337_);
lean_dec(v_x_1335_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1359_);
lean_ctor_set(v___x_1341_, 0, v___x_1358_);
v___x_1361_ = v___x_1341_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1364_, lean_object* v_k_1365_, lean_object* v_v_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1364_, v___x_1367_, v_k_1365_, v_v_1366_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1370_, size_t v_x_1371_, size_t v_x_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1370_) == 0)
{
lean_object* v_es_1375_; size_t v___x_1376_; size_t v___x_1377_; lean_object* v_j_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_es_1375_ = lean_ctor_get(v_x_1370_, 0);
v___x_1376_ = ((size_t)31ULL);
v___x_1377_ = lean_usize_land(v_x_1371_, v___x_1376_);
v_j_1378_ = lean_usize_to_nat(v___x_1377_);
v___x_1379_ = lean_array_get_size(v_es_1375_);
v___x_1380_ = lean_nat_dec_lt(v_j_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_dec(v_j_1378_);
lean_dec(v_x_1374_);
lean_dec(v_x_1373_);
return v_x_1370_;
}
else
{
lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1419_; 
lean_inc_ref(v_es_1375_);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_x_1370_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v_x_1370_, 0);
lean_dec(v_unused_1420_);
v___x_1382_ = v_x_1370_;
v_isShared_1383_ = v_isSharedCheck_1419_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v_x_1370_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1419_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_v_1384_; lean_object* v___x_1385_; lean_object* v_xs_x27_1386_; lean_object* v___y_1388_; 
v_v_1384_ = lean_array_fget(v_es_1375_, v_j_1378_);
v___x_1385_ = lean_box(0);
v_xs_x27_1386_ = lean_array_fset(v_es_1375_, v_j_1378_, v___x_1385_);
switch(lean_obj_tag(v_v_1384_))
{
case 0:
{
lean_object* v_key_1393_; lean_object* v_val_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1404_; 
v_key_1393_ = lean_ctor_get(v_v_1384_, 0);
v_val_1394_ = lean_ctor_get(v_v_1384_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_v_1384_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1396_ = v_v_1384_;
v_isShared_1397_ = v_isSharedCheck_1404_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_val_1394_);
lean_inc(v_key_1393_);
lean_dec(v_v_1384_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1404_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_name_eq(v_x_1373_, v_key_1393_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_del_object(v___x_1396_);
v___x_1399_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1393_, v_val_1394_, v_x_1373_, v_x_1374_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
v___y_1388_ = v___x_1400_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1402_; 
lean_dec(v_val_1394_);
lean_dec(v_key_1393_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 1, v_x_1374_);
lean_ctor_set(v___x_1396_, 0, v_x_1373_);
v___x_1402_ = v___x_1396_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_x_1373_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_x_1374_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
v___y_1388_ = v___x_1402_;
goto v___jp_1387_;
}
}
}
}
case 1:
{
lean_object* v_node_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1417_; 
v_node_1405_ = lean_ctor_get(v_v_1384_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_v_1384_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1407_ = v_v_1384_;
v_isShared_1408_ = v_isSharedCheck_1417_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_node_1405_);
lean_dec(v_v_1384_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1417_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
size_t v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1409_ = ((size_t)5ULL);
v___x_1410_ = lean_usize_shift_right(v_x_1371_, v___x_1409_);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_add(v_x_1372_, v___x_1411_);
v___x_1413_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1405_, v___x_1410_, v___x_1412_, v_x_1373_, v_x_1374_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1413_);
v___x_1415_ = v___x_1407_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
v___y_1388_ = v___x_1415_;
goto v___jp_1387_;
}
}
}
default: 
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_x_1373_);
lean_ctor_set(v___x_1418_, 1, v_x_1374_);
v___y_1388_ = v___x_1418_;
goto v___jp_1387_;
}
}
v___jp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = lean_array_fset(v_xs_x27_1386_, v_j_1378_, v___y_1388_);
lean_dec(v_j_1378_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1389_);
v___x_1391_ = v___x_1382_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
else
{
lean_object* v_ks_1421_; lean_object* v_vs_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1440_; 
v_ks_1421_ = lean_ctor_get(v_x_1370_, 0);
v_vs_1422_ = lean_ctor_get(v_x_1370_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1370_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1424_ = v_x_1370_;
v_isShared_1425_ = v_isSharedCheck_1440_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_vs_1422_);
lean_inc(v_ks_1421_);
lean_dec(v_x_1370_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1440_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_ks_1421_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_vs_1422_);
v___x_1427_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v_newNode_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v_newNode_1428_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1427_, v_x_1373_, v_x_1374_);
v___x_1429_ = ((size_t)7ULL);
v___x_1430_ = lean_usize_dec_le(v___x_1429_, v_x_1372_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1428_);
v___x_1432_ = lean_unsigned_to_nat(4u);
v___x_1433_ = lean_nat_dec_lt(v___x_1431_, v___x_1432_);
lean_dec(v___x_1431_);
if (v___x_1433_ == 0)
{
lean_object* v_ks_1434_; lean_object* v_vs_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_ks_1434_ = lean_ctor_get(v_newNode_1428_, 0);
lean_inc_ref(v_ks_1434_);
v_vs_1435_ = lean_ctor_get(v_newNode_1428_, 1);
lean_inc_ref(v_vs_1435_);
lean_dec_ref(v_newNode_1428_);
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1372_, v_ks_1434_, v_vs_1435_, v___x_1436_, v___x_1437_);
lean_dec_ref(v_vs_1435_);
lean_dec_ref(v_ks_1434_);
return v___x_1438_;
}
else
{
return v_newNode_1428_;
}
}
else
{
return v_newNode_1428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1441_, lean_object* v_keys_1442_, lean_object* v_vals_1443_, lean_object* v_i_1444_, lean_object* v_entries_1445_){
_start:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_array_get_size(v_keys_1442_);
v___x_1447_ = lean_nat_dec_lt(v_i_1444_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_dec(v_i_1444_);
return v_entries_1445_;
}
else
{
lean_object* v_k_1448_; lean_object* v_v_1449_; uint64_t v___y_1451_; 
v_k_1448_ = lean_array_fget_borrowed(v_keys_1442_, v_i_1444_);
v_v_1449_ = lean_array_fget_borrowed(v_vals_1443_, v_i_1444_);
if (lean_obj_tag(v_k_1448_) == 0)
{
uint64_t v___x_1462_; 
v___x_1462_ = 1723ULL;
v___y_1451_ = v___x_1462_;
goto v___jp_1450_;
}
else
{
uint64_t v_hash_1463_; 
v_hash_1463_ = lean_ctor_get_uint64(v_k_1448_, sizeof(void*)*2);
v___y_1451_ = v_hash_1463_;
goto v___jp_1450_;
}
v___jp_1450_:
{
size_t v_h_1452_; size_t v___x_1453_; lean_object* v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; size_t v_h_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_h_1452_ = lean_uint64_to_usize(v___y_1451_);
v___x_1453_ = ((size_t)5ULL);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_sub(v_depth_1441_, v___x_1455_);
v___x_1457_ = lean_usize_mul(v___x_1453_, v___x_1456_);
v_h_1458_ = lean_usize_shift_right(v_h_1452_, v___x_1457_);
v___x_1459_ = lean_nat_add(v_i_1444_, v___x_1454_);
lean_dec(v_i_1444_);
lean_inc(v_v_1449_);
lean_inc(v_k_1448_);
v___x_1460_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1445_, v_h_1458_, v_depth_1441_, v_k_1448_, v_v_1449_);
v_i_1444_ = v___x_1459_;
v_entries_1445_ = v___x_1460_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_i_1467_, lean_object* v_entries_1468_){
_start:
{
size_t v_depth_boxed_1469_; lean_object* v_res_1470_; 
v_depth_boxed_1469_ = lean_unbox_usize(v_depth_1464_);
lean_dec(v_depth_1464_);
v_res_1470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1469_, v_keys_1465_, v_vals_1466_, v_i_1467_, v_entries_1468_);
lean_dec_ref(v_vals_1466_);
lean_dec_ref(v_keys_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
size_t v_x_632__boxed_1476_; size_t v_x_633__boxed_1477_; lean_object* v_res_1478_; 
v_x_632__boxed_1476_ = lean_unbox_usize(v_x_1472_);
lean_dec(v_x_1472_);
v_x_633__boxed_1477_ = lean_unbox_usize(v_x_1473_);
lean_dec(v_x_1473_);
v_res_1478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1471_, v_x_632__boxed_1476_, v_x_633__boxed_1477_, v_x_1474_, v_x_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
uint64_t v___y_1483_; 
if (lean_obj_tag(v_x_1480_) == 0)
{
uint64_t v___x_1487_; 
v___x_1487_ = 1723ULL;
v___y_1483_ = v___x_1487_;
goto v___jp_1482_;
}
else
{
uint64_t v_hash_1488_; 
v_hash_1488_ = lean_ctor_get_uint64(v_x_1480_, sizeof(void*)*2);
v___y_1483_ = v_hash_1488_;
goto v___jp_1482_;
}
v___jp_1482_:
{
size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = lean_uint64_to_usize(v___y_1483_);
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1479_, v___x_1484_, v___x_1485_, v_x_1480_, v_x_1481_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1489_, lean_object* v_as_1490_, size_t v_i_1491_, size_t v_stop_1492_, lean_object* v_b_1493_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_eq(v_i_1491_, v_stop_1492_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; size_t v___x_1497_; size_t v___x_1498_; 
v___x_1495_ = lean_array_uget_borrowed(v_as_1490_, v_i_1491_);
lean_inc(v_declName_1489_);
lean_inc(v___x_1495_);
v___x_1496_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1493_, v___x_1495_, v_declName_1489_);
v___x_1497_ = ((size_t)1ULL);
v___x_1498_ = lean_usize_add(v_i_1491_, v___x_1497_);
v_i_1491_ = v___x_1498_;
v_b_1493_ = v___x_1496_;
goto _start;
}
else
{
lean_dec(v_declName_1489_);
return v_b_1493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1500_, lean_object* v_as_1501_, lean_object* v_i_1502_, lean_object* v_stop_1503_, lean_object* v_b_1504_){
_start:
{
size_t v_i_boxed_1505_; size_t v_stop_boxed_1506_; lean_object* v_res_1507_; 
v_i_boxed_1505_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_stop_boxed_1506_ = lean_unbox_usize(v_stop_1503_);
lean_dec(v_stop_1503_);
v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1500_, v_as_1501_, v_i_boxed_1505_, v_stop_boxed_1506_, v_b_1504_);
lean_dec_ref(v_as_1501_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1508_, lean_object* v_declName_1509_, lean_object* v_s_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = lean_array_get_size(v_eqThms_1508_);
v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_dec(v_declName_1509_);
return v_s_1510_;
}
else
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
if (v___x_1514_ == 0)
{
if (v___x_1513_ == 0)
{
lean_dec(v_declName_1509_);
return v_s_1510_;
}
else
{
size_t v___x_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = lean_usize_of_nat(v___x_1512_);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1509_, v_eqThms_1508_, v___x_1515_, v___x_1516_, v_s_1510_);
return v___x_1517_;
}
}
else
{
size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = ((size_t)0ULL);
v___x_1519_ = lean_usize_of_nat(v___x_1512_);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1509_, v_eqThms_1508_, v___x_1518_, v___x_1519_, v_s_1510_);
return v___x_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1521_, lean_object* v_declName_1522_, lean_object* v_s_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1521_, v_declName_1522_, v_s_1523_);
lean_dec_ref(v_eqThms_1521_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1525_, lean_object* v_eqThms_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___f_1529_; lean_object* v___x_1530_; lean_object* v_env_1531_; lean_object* v_nextMacroScope_1532_; lean_object* v_ngen_1533_; lean_object* v_auxDeclNGen_1534_; lean_object* v_traceState_1535_; lean_object* v_recordedDeps_1536_; lean_object* v_messages_1537_; lean_object* v_infoState_1538_; lean_object* v_snapshotTasks_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1554_; 
v___f_1529_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1529_, 0, v_eqThms_1526_);
lean_closure_set(v___f_1529_, 1, v_declName_1525_);
v___x_1530_ = lean_st_ref_take(v_a_1527_);
v_env_1531_ = lean_ctor_get(v___x_1530_, 0);
v_nextMacroScope_1532_ = lean_ctor_get(v___x_1530_, 1);
v_ngen_1533_ = lean_ctor_get(v___x_1530_, 2);
v_auxDeclNGen_1534_ = lean_ctor_get(v___x_1530_, 3);
v_traceState_1535_ = lean_ctor_get(v___x_1530_, 4);
v_recordedDeps_1536_ = lean_ctor_get(v___x_1530_, 6);
v_messages_1537_ = lean_ctor_get(v___x_1530_, 7);
v_infoState_1538_ = lean_ctor_get(v___x_1530_, 8);
v_snapshotTasks_1539_ = lean_ctor_get(v___x_1530_, 9);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1530_, 5);
lean_dec(v_unused_1555_);
v___x_1541_ = v___x_1530_;
v_isShared_1542_ = v_isSharedCheck_1554_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_snapshotTasks_1539_);
lean_inc(v_infoState_1538_);
lean_inc(v_messages_1537_);
lean_inc(v_recordedDeps_1536_);
lean_inc(v_traceState_1535_);
lean_inc(v_auxDeclNGen_1534_);
lean_inc(v_ngen_1533_);
lean_inc(v_nextMacroScope_1532_);
lean_inc(v_env_1531_);
lean_dec(v___x_1530_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1554_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v_asyncMode_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1543_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1544_ = lean_ctor_get(v___x_1543_, 2);
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1543_, v_env_1531_, v___f_1529_, v_asyncMode_1544_, v___x_1546_);
v___x_1548_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 5, v___x_1548_);
lean_ctor_set(v___x_1541_, 0, v___x_1547_);
v___x_1550_ = v___x_1541_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_nextMacroScope_1532_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_ngen_1533_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_auxDeclNGen_1534_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_traceState_1535_);
lean_ctor_set(v_reuseFailAlloc_1553_, 5, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1553_, 6, v_recordedDeps_1536_);
lean_ctor_set(v_reuseFailAlloc_1553_, 7, v_messages_1537_);
lean_ctor_set(v_reuseFailAlloc_1553_, 8, v_infoState_1538_);
lean_ctor_set(v_reuseFailAlloc_1553_, 9, v_snapshotTasks_1539_);
v___x_1550_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_st_ref_put(v_a_1527_, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1545_);
return v___x_1552_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1556_, lean_object* v_eqThms_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1556_, v_eqThms_1557_, v_a_1558_);
lean_dec(v_a_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1561_, lean_object* v_eqThms_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1561_, v_eqThms_1562_, v_a_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1567_, lean_object* v_eqThms_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1567_, v_eqThms_1568_, v_a_1569_, v_a_1570_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1574_, v_x_1575_, v_x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1578_, lean_object* v_x_1579_, size_t v_x_1580_, size_t v_x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1579_, v_x_1580_, v_x_1581_, v_x_1582_, v_x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
size_t v_x_894__boxed_1591_; size_t v_x_895__boxed_1592_; lean_object* v_res_1593_; 
v_x_894__boxed_1591_ = lean_unbox_usize(v_x_1587_);
lean_dec(v_x_1587_);
v_x_895__boxed_1592_ = lean_unbox_usize(v_x_1588_);
lean_dec(v_x_1588_);
v_res_1593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1585_, v_x_1586_, v_x_894__boxed_1591_, v_x_895__boxed_1592_, v_x_1589_, v_x_1590_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1594_, lean_object* v_n_1595_, lean_object* v_k_1596_, lean_object* v_v_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1595_, v_k_1596_, v_v_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1599_, size_t v_depth_1600_, lean_object* v_keys_1601_, lean_object* v_vals_1602_, lean_object* v_heq_1603_, lean_object* v_i_1604_, lean_object* v_entries_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1600_, v_keys_1601_, v_vals_1602_, v_i_1604_, v_entries_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1607_, lean_object* v_depth_1608_, lean_object* v_keys_1609_, lean_object* v_vals_1610_, lean_object* v_heq_1611_, lean_object* v_i_1612_, lean_object* v_entries_1613_){
_start:
{
size_t v_depth_boxed_1614_; lean_object* v_res_1615_; 
v_depth_boxed_1614_ = lean_unbox_usize(v_depth_1608_);
lean_dec(v_depth_1608_);
v_res_1615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1607_, v_depth_boxed_1614_, v_keys_1609_, v_vals_1610_, v_heq_1611_, v_i_1612_, v_entries_1613_);
lean_dec_ref(v_vals_1610_);
lean_dec_ref(v_keys_1609_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1617_, v_x_1618_, v_x_1619_, v_x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1622_, lean_object* v_env_1623_, lean_object* v_idx_1624_, lean_object* v_eqs_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_nextEq_1632_; uint8_t v___x_1633_; 
v___x_1627_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = lean_nat_add(v_idx_1624_, v___x_1628_);
lean_dec(v_idx_1624_);
lean_inc(v___x_1629_);
v___x_1630_ = l_Nat_reprFast(v___x_1629_);
v___x_1631_ = lean_string_append(v___x_1627_, v___x_1630_);
lean_dec_ref(v___x_1630_);
lean_inc(v_declName_1622_);
lean_inc_ref(v_env_1623_);
v_nextEq_1632_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1623_, v_declName_1622_, v___x_1631_);
v___x_1633_ = l_Lean_Environment_containsOnBranch(v_env_1623_, v_nextEq_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v_nextEq_1632_);
lean_dec(v___x_1629_);
lean_dec_ref(v_env_1623_);
lean_dec(v_declName_1622_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_eqs_1625_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_array_push(v_eqs_1625_, v_nextEq_1632_);
v_idx_1624_ = v___x_1629_;
v_eqs_1625_ = v___x_1635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1637_, lean_object* v_env_1638_, lean_object* v_idx_1639_, lean_object* v_eqs_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1637_, v_env_1638_, v_idx_1639_, v_eqs_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1643_, lean_object* v_env_1644_, lean_object* v_idx_1645_, lean_object* v_eqs_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1643_, v_env_1644_, v_idx_1645_, v_eqs_1646_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1653_, lean_object* v_env_1654_, lean_object* v_idx_1655_, lean_object* v_eqs_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1653_, v_env_1654_, v_idx_1655_, v_eqs_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v_env_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; uint8_t v___x_1671_; 
v___x_1666_ = lean_st_ref_get(v_a_1664_);
v_env_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc_ref_n(v_env_1667_, 3);
lean_dec(v___x_1666_);
v___x_1668_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1663_);
v___x_1669_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1667_, v_declName_1663_, v___x_1668_);
v___x_1670_ = 1;
lean_inc(v___x_1669_);
v___x_1671_ = l_Lean_Environment_contains(v_env_1667_, v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v___x_1669_);
lean_dec_ref(v_env_1667_);
lean_dec(v_declName_1663_);
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_mk_empty_array_with_capacity(v___x_1674_);
v___x_1676_ = lean_array_push(v___x_1675_, v___x_1669_);
lean_inc(v_declName_1663_);
v___x_1677_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1663_, v_env_1667_, v___x_1674_, v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc_n(v_a_1678_, 2);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1679_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1663_, v_a_1678_, v_a_1664_);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v___x_1679_, 0);
lean_dec(v_unused_1688_);
v___x_1681_ = v___x_1679_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_dec(v___x_1679_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_a_1678_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_declName_1663_);
v_a_1689_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1677_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1677_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1697_, v_a_1698_);
lean_dec(v_a_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1701_, v_a_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1715_, lean_object* v_localInsts_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1715_, v_localInsts_1716_, v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
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
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_a_1732_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1723_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1723_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1740_, lean_object* v_localInsts_1741_, lean_object* v_x_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1740_, v_localInsts_1741_, v_x_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1749_, lean_object* v_lctx_1750_, lean_object* v_localInsts_1751_, lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1750_, v_localInsts_1751_, v_x_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1759_, lean_object* v_lctx_1760_, lean_object* v_localInsts_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1759_, v_lctx_1760_, v_localInsts_1761_, v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1772_, lean_object* v_as_x27_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
if (lean_obj_tag(v_as_x27_1773_) == 0)
{
lean_object* v___x_1780_; 
lean_dec(v_declName_1772_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_b_1774_);
return v___x_1780_;
}
else
{
lean_object* v_head_1781_; lean_object* v_tail_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec_ref(v_b_1774_);
v_head_1781_ = lean_ctor_get(v_as_x27_1773_, 0);
v_tail_1782_ = lean_ctor_get(v_as_x27_1773_, 1);
v___x_1783_ = lean_box(0);
v___x_1784_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
lean_inc(v_head_1781_);
lean_inc(v___y_1778_);
lean_inc_ref(v___y_1777_);
lean_inc(v___y_1776_);
lean_inc_ref(v___y_1775_);
lean_inc(v_declName_1772_);
v___x_1785_ = lean_apply_6(v_head_1781_, v_declName_1772_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, lean_box(0));
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
if (lean_obj_tag(v_a_1786_) == 1)
{
lean_object* v_val_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1797_; 
v_val_1787_ = lean_ctor_get(v_a_1786_, 0);
lean_inc(v_val_1787_);
v___x_1788_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1772_, v_val_1787_, v___y_1778_);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1788_, 0);
lean_dec(v_unused_1798_);
v___x_1790_ = v___x_1788_;
v_isShared_1791_ = v_isSharedCheck_1797_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v___x_1788_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1797_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_a_1786_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v___x_1783_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1793_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_dec(v_a_1786_);
v_as_x27_1773_ = v_tail_1782_;
v_b_1774_ = v___x_1784_;
goto _start;
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_declName_1772_);
v_a_1800_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1785_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1785_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1808_, lean_object* v_as_x27_1809_, lean_object* v_b_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1808_, v_as_x27_1809_, v_b_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v_as_x27_1809_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
lean_inc(v_declName_1817_);
v___x_1823_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1861_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1861_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1861_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_unbox(v_a_1824_);
lean_dec(v_a_1824_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_dec(v_declName_1817_);
v___x_1829_ = lean_box(0);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1829_);
v___x_1831_ = v___x_1826_;
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
else
{
lean_object* v___x_1833_; 
lean_del_object(v___x_1826_);
lean_inc(v_declName_1817_);
v___x_1833_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1817_, v___y_1821_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
if (lean_obj_tag(v_a_1834_) == 1)
{
lean_dec_ref_known(v_a_1834_, 1);
lean_dec(v_declName_1817_);
return v___x_1833_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1836_ = lean_st_ref_get(v___x_1835_);
v___x_1837_ = lean_box(0);
v___x_1838_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1839_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1817_, v___x_1836_, v___x_1838_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___x_1836_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1852_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v_fst_1844_; 
v_fst_1844_ = lean_ctor_get(v_a_1840_, 0);
lean_inc(v_fst_1844_);
lean_dec(v_a_1840_);
if (lean_obj_tag(v_fst_1844_) == 0)
{
lean_object* v___x_1846_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1837_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1837_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
else
{
lean_object* v_val_1848_; lean_object* v___x_1850_; 
v_val_1848_ = lean_ctor_get(v_fst_1844_, 0);
lean_inc(v_val_1848_);
lean_dec_ref_known(v_fst_1844_, 1);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_val_1848_);
v___x_1850_ = v___x_1842_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_val_1848_);
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
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_a_1853_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1839_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1839_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
else
{
lean_dec(v_declName_1817_);
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_declName_1817_);
v_a_1862_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1823_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1823_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = lean_box(1);
v___x_1880_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1881_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___x_1880_);
lean_ctor_set(v___x_1882_, 2, v___x_1879_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___f_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___f_1891_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1891_, 0, v_declName_1885_);
v___x_1892_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1893_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_1894_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1892_, v___x_1893_, v___f_1891_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1902_, lean_object* v_as_1903_, lean_object* v_as_x27_1904_, lean_object* v_b_1905_, lean_object* v_a_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1902_, v_as_x27_1904_, v_b_1905_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1913_, lean_object* v_as_1914_, lean_object* v_as_x27_1915_, lean_object* v_b_1916_, lean_object* v_a_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1913_, v_as_1914_, v_as_x27_1915_, v_b_1916_, v_a_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v_as_x27_1915_);
lean_dec(v_as_1914_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1930_ = lean_unsigned_to_nat(32u);
v___x_1931_ = lean_mk_empty_array_with_capacity(v___x_1930_);
lean_dec_ref(v___x_1931_);
v___x_1932_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
lean_inc(v_declName_1924_);
v___x_1934_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1934_, 0, v_declName_1924_);
v___x_1935_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1935_, 0, lean_box(0));
lean_closure_set(v___x_1935_, 1, v_declName_1924_);
lean_closure_set(v___x_1935_, 2, v___x_1934_);
v___x_1936_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1932_, v___x_1933_, v___x_1935_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v_opts_1944_, lean_object* v_opt_1945_){
_start:
{
lean_object* v_name_1946_; lean_object* v_defValue_1947_; lean_object* v_map_1948_; lean_object* v___x_1949_; 
v_name_1946_ = lean_ctor_get(v_opt_1945_, 0);
v_defValue_1947_ = lean_ctor_get(v_opt_1945_, 1);
v_map_1948_ = lean_ctor_get(v_opts_1944_, 0);
v___x_1949_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1948_, v_name_1946_);
if (lean_obj_tag(v___x_1949_) == 0)
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_unbox(v_defValue_1947_);
return v___x_1950_;
}
else
{
lean_object* v_val_1951_; 
v_val_1951_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_val_1951_);
lean_dec_ref_known(v___x_1949_, 1);
if (lean_obj_tag(v_val_1951_) == 1)
{
uint8_t v_v_1952_; 
v_v_1952_ = lean_ctor_get_uint8(v_val_1951_, 0);
lean_dec_ref_known(v_val_1951_, 0);
return v_v_1952_;
}
else
{
uint8_t v___x_1953_; 
lean_dec(v_val_1951_);
v___x_1953_ = lean_unbox(v_defValue_1947_);
return v___x_1953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v_opts_1954_, lean_object* v_opt_1955_){
_start:
{
uint8_t v_res_1956_; lean_object* v_r_1957_; 
v_res_1956_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_1954_, v_opt_1955_);
lean_dec_ref(v_opt_1955_);
lean_dec_ref(v_opts_1954_);
v_r_1957_ = lean_box(v_res_1956_);
return v_r_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(lean_object* v___x_1958_, lean_object* v_as_1959_, size_t v_sz_1960_, size_t v_i_1961_, lean_object* v_b_1962_){
_start:
{
lean_object* v_a_1965_; uint8_t v___x_1969_; 
v___x_1969_ = lean_usize_dec_lt(v_i_1961_, v_sz_1960_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_b_1962_);
return v___x_1970_;
}
else
{
lean_object* v_a_1971_; lean_object* v_defValue_1972_; uint8_t v___x_1973_; uint8_t v___y_1987_; uint8_t v___x_1988_; 
v_a_1971_ = lean_array_uget(v_as_1959_, v_i_1961_);
v_defValue_1972_ = lean_ctor_get(v_a_1971_, 1);
v___x_1973_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_1958_, v_a_1971_);
v___x_1988_ = lean_unbox(v_defValue_1972_);
if (v___x_1988_ == 0)
{
if (v___x_1973_ == 0)
{
v___y_1987_ = v___x_1969_;
goto v___jp_1986_;
}
else
{
goto v___jp_1974_;
}
}
else
{
v___y_1987_ = v___x_1973_;
goto v___jp_1986_;
}
v___jp_1974_:
{
lean_object* v_name_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1984_; 
v_name_1975_ = lean_ctor_get(v_a_1971_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_a_1971_, 1);
lean_dec(v_unused_1985_);
v___x_1977_ = v_a_1971_;
v_isShared_1978_ = v_isSharedCheck_1984_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_name_1975_);
lean_dec(v_a_1971_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1984_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1979_, 0, v___x_1973_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 1, v___x_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_name_1975_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_array_push(v_b_1962_, v___x_1981_);
v_a_1965_ = v___x_1982_;
goto v___jp_1964_;
}
}
}
v___jp_1986_:
{
if (v___y_1987_ == 0)
{
goto v___jp_1974_;
}
else
{
lean_dec(v_a_1971_);
v_a_1965_ = v_b_1962_;
goto v___jp_1964_;
}
}
}
v___jp_1964_:
{
size_t v___x_1966_; size_t v___x_1967_; 
v___x_1966_ = ((size_t)1ULL);
v___x_1967_ = lean_usize_add(v_i_1961_, v___x_1966_);
v_i_1961_ = v___x_1967_;
v_b_1962_ = v_a_1965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg___boxed(lean_object* v___x_1989_, lean_object* v_as_1990_, lean_object* v_sz_1991_, lean_object* v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_){
_start:
{
size_t v_sz_boxed_1995_; size_t v_i_boxed_1996_; lean_object* v_res_1997_; 
v_sz_boxed_1995_ = lean_unbox_usize(v_sz_1991_);
lean_dec(v_sz_1991_);
v_i_boxed_1996_ = lean_unbox_usize(v_i_1992_);
lean_dec(v_i_1992_);
v_res_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_1989_, v_as_1990_, v_sz_boxed_1995_, v_i_boxed_1996_, v_b_1993_);
lean_dec_ref(v_as_1990_);
lean_dec_ref(v___x_1989_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(lean_object* v_msgData_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v_env_2005_; lean_object* v___x_2006_; lean_object* v_toCold_2007_; lean_object* v_mctx_2008_; lean_object* v_lctx_2009_; lean_object* v_options_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2004_ = lean_st_ref_get(v___y_2002_);
v_env_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_2004_);
v___x_2006_ = lean_st_ref_get(v___y_2000_);
v_toCold_2007_ = lean_ctor_get(v___y_2001_, 0);
v_mctx_2008_ = lean_ctor_get(v___x_2006_, 0);
lean_inc_ref(v_mctx_2008_);
lean_dec(v___x_2006_);
v_lctx_2009_ = lean_ctor_get(v___y_1999_, 2);
v_options_2010_ = lean_ctor_get(v_toCold_2007_, 2);
lean_inc_ref(v_options_2010_);
lean_inc_ref(v_lctx_2009_);
v___x_2011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2011_, 0, v_env_2005_);
lean_ctor_set(v___x_2011_, 1, v_mctx_2008_);
lean_ctor_set(v___x_2011_, 2, v_lctx_2009_);
lean_ctor_set(v___x_2011_, 3, v_options_2010_);
v___x_2012_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v_msgData_1998_);
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2___boxed(lean_object* v_msgData_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msgData_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2020_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2021_; double v___x_2022_; 
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = lean_float_of_nat(v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(lean_object* v_cls_2026_, lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_ref_2033_; lean_object* v___x_2034_; lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2080_; 
v_ref_2033_ = lean_ctor_get(v___y_2030_, 2);
v___x_2034_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2080_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2080_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v_traceState_2040_; lean_object* v_env_2041_; lean_object* v_nextMacroScope_2042_; lean_object* v_ngen_2043_; lean_object* v_auxDeclNGen_2044_; lean_object* v_cache_2045_; lean_object* v_recordedDeps_2046_; lean_object* v_messages_2047_; lean_object* v_infoState_2048_; lean_object* v_snapshotTasks_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2079_; 
v___x_2039_ = lean_st_ref_take(v___y_2031_);
v_traceState_2040_ = lean_ctor_get(v___x_2039_, 4);
v_env_2041_ = lean_ctor_get(v___x_2039_, 0);
v_nextMacroScope_2042_ = lean_ctor_get(v___x_2039_, 1);
v_ngen_2043_ = lean_ctor_get(v___x_2039_, 2);
v_auxDeclNGen_2044_ = lean_ctor_get(v___x_2039_, 3);
v_cache_2045_ = lean_ctor_get(v___x_2039_, 5);
v_recordedDeps_2046_ = lean_ctor_get(v___x_2039_, 6);
v_messages_2047_ = lean_ctor_get(v___x_2039_, 7);
v_infoState_2048_ = lean_ctor_get(v___x_2039_, 8);
v_snapshotTasks_2049_ = lean_ctor_get(v___x_2039_, 9);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2051_ = v___x_2039_;
v_isShared_2052_ = v_isSharedCheck_2079_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snapshotTasks_2049_);
lean_inc(v_infoState_2048_);
lean_inc(v_messages_2047_);
lean_inc(v_recordedDeps_2046_);
lean_inc(v_cache_2045_);
lean_inc(v_traceState_2040_);
lean_inc(v_auxDeclNGen_2044_);
lean_inc(v_ngen_2043_);
lean_inc(v_nextMacroScope_2042_);
lean_inc(v_env_2041_);
lean_dec(v___x_2039_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2079_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
uint64_t v_tid_2053_; lean_object* v_traces_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2078_; 
v_tid_2053_ = lean_ctor_get_uint64(v_traceState_2040_, sizeof(void*)*1);
v_traces_2054_ = lean_ctor_get(v_traceState_2040_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_traceState_2040_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2056_ = v_traceState_2040_;
v_isShared_2057_ = v_isSharedCheck_2078_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_traces_2054_);
lean_dec(v_traceState_2040_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2078_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; double v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
v___x_2061_ = 0;
v___x_2062_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_2063_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2063_, 0, v_cls_2026_);
lean_ctor_set(v___x_2063_, 1, v___x_2059_);
lean_ctor_set(v___x_2063_, 2, v___x_2062_);
lean_ctor_set_float(v___x_2063_, sizeof(void*)*3, v___x_2060_);
lean_ctor_set_float(v___x_2063_, sizeof(void*)*3 + 8, v___x_2060_);
lean_ctor_set_uint8(v___x_2063_, sizeof(void*)*3 + 16, v___x_2061_);
v___x_2064_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__2));
v___x_2065_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v_a_2035_);
lean_ctor_set(v___x_2065_, 2, v___x_2064_);
lean_inc(v_ref_2033_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_ref_2033_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = l_Lean_PersistentArray_push___redArg(v_traces_2054_, v___x_2066_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2067_);
v___x_2069_ = v___x_2056_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2067_);
lean_ctor_set_uint64(v_reuseFailAlloc_2077_, sizeof(void*)*1, v_tid_2053_);
v___x_2069_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 4, v___x_2069_);
v___x_2071_ = v___x_2051_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_env_2041_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_nextMacroScope_2042_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_ngen_2043_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_auxDeclNGen_2044_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2076_, 5, v_cache_2045_);
lean_ctor_set(v_reuseFailAlloc_2076_, 6, v_recordedDeps_2046_);
lean_ctor_set(v_reuseFailAlloc_2076_, 7, v_messages_2047_);
lean_ctor_set(v_reuseFailAlloc_2076_, 8, v_infoState_2048_);
lean_ctor_set(v_reuseFailAlloc_2076_, 9, v_snapshotTasks_2049_);
v___x_2071_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_st_ref_put(v___y_2031_, v___x_2071_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2058_);
v___x_2074_ = v___x_2037_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2058_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___boxed(lean_object* v_cls_2081_, lean_object* v_msg_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v_cls_2081_, v_msg_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2088_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2091_; size_t v_sz_2092_; 
v___x_2091_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2092_ = lean_array_size(v___x_2091_);
return v_sz_2092_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_2094_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
lean_ctor_set(v___x_2094_, 2, v___x_2093_);
lean_ctor_set(v___x_2094_, 3, v___x_2093_);
lean_ctor_set(v___x_2094_, 4, v___x_2093_);
lean_ctor_set(v___x_2094_, 5, v___x_2093_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_2103_ = l_Lean_Name_append(v___x_2102_, v___x_2101_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; size_t v_sz_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2113_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2110_);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2116_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2117_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2118_ = ((size_t)0ULL);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2113_, v___x_2116_, v_sz_2117_, v___x_2118_, v___x_2115_);
lean_dec_ref(v___x_2113_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2183_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2183_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2183_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = lean_array_get_size(v_a_2120_);
v___x_2169_ = lean_nat_dec_eq(v___x_2168_, v___x_2114_);
if (v___x_2169_ == 0)
{
lean_object* v_toCold_2170_; lean_object* v_options_2171_; uint8_t v_hasTrace_2172_; 
v_toCold_2170_ = lean_ctor_get(v_a_2110_, 0);
v_options_2171_ = lean_ctor_get(v_toCold_2170_, 2);
v_hasTrace_2172_ = lean_ctor_get_uint8(v_options_2171_, sizeof(void*)*1);
if (v_hasTrace_2172_ == 0)
{
v___y_2125_ = v_a_2109_;
v___y_2126_ = v_a_2111_;
goto v___jp_2124_;
}
else
{
lean_object* v_inheritedTraceOptions_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_inheritedTraceOptions_2173_ = lean_ctor_get(v_toCold_2170_, 11);
v___x_2174_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2175_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2176_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2173_, v_options_2171_, v___x_2175_);
if (v___x_2176_ == 0)
{
v___y_2125_ = v_a_2109_;
v___y_2126_ = v_a_2111_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2177_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2107_);
v___x_2178_ = l_Lean_MessageData_ofName(v_declName_2107_);
v___x_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2(v___x_2174_, v___x_2179_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_dec_ref_known(v___x_2180_, 1);
v___y_2125_ = v_a_2109_;
v___y_2126_ = v_a_2111_;
goto v___jp_2124_;
}
else
{
lean_del_object(v___x_2122_);
lean_dec(v_a_2120_);
lean_dec(v_declName_2107_);
return v___x_2180_;
}
}
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_del_object(v___x_2122_);
lean_dec(v_a_2120_);
lean_dec(v_declName_2107_);
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
v___jp_2124_:
{
lean_object* v___x_2127_; lean_object* v_env_2128_; lean_object* v_nextMacroScope_2129_; lean_object* v_ngen_2130_; lean_object* v_auxDeclNGen_2131_; lean_object* v_traceState_2132_; lean_object* v_recordedDeps_2133_; lean_object* v_messages_2134_; lean_object* v_infoState_2135_; lean_object* v_snapshotTasks_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2166_; 
v___x_2127_ = lean_st_ref_take(v___y_2126_);
v_env_2128_ = lean_ctor_get(v___x_2127_, 0);
v_nextMacroScope_2129_ = lean_ctor_get(v___x_2127_, 1);
v_ngen_2130_ = lean_ctor_get(v___x_2127_, 2);
v_auxDeclNGen_2131_ = lean_ctor_get(v___x_2127_, 3);
v_traceState_2132_ = lean_ctor_get(v___x_2127_, 4);
v_recordedDeps_2133_ = lean_ctor_get(v___x_2127_, 6);
v_messages_2134_ = lean_ctor_get(v___x_2127_, 7);
v_infoState_2135_ = lean_ctor_get(v___x_2127_, 8);
v_snapshotTasks_2136_ = lean_ctor_get(v___x_2127_, 9);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v___x_2127_, 5);
lean_dec(v_unused_2167_);
v___x_2138_ = v___x_2127_;
v_isShared_2139_ = v_isSharedCheck_2166_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_snapshotTasks_2136_);
lean_inc(v_infoState_2135_);
lean_inc(v_messages_2134_);
lean_inc(v_recordedDeps_2133_);
lean_inc(v_traceState_2132_);
lean_inc(v_auxDeclNGen_2131_);
lean_inc(v_ngen_2130_);
lean_inc(v_nextMacroScope_2129_);
lean_inc(v_env_2128_);
lean_dec(v___x_2127_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2166_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2140_ = l_Lean_Meta_eqnOptionsExt;
v___x_2141_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2140_, v_env_2128_, v_declName_2107_, v_a_2120_);
v___x_2142_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 5, v___x_2142_);
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2144_ = v___x_2138_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_nextMacroScope_2129_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_ngen_2130_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_auxDeclNGen_2131_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_traceState_2132_);
lean_ctor_set(v_reuseFailAlloc_2165_, 5, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2165_, 6, v_recordedDeps_2133_);
lean_ctor_set(v_reuseFailAlloc_2165_, 7, v_messages_2134_);
lean_ctor_set(v_reuseFailAlloc_2165_, 8, v_infoState_2135_);
lean_ctor_set(v_reuseFailAlloc_2165_, 9, v_snapshotTasks_2136_);
v___x_2144_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_mctx_2147_; lean_object* v_zetaDeltaFVarIds_2148_; lean_object* v_postponed_2149_; lean_object* v_diag_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2163_; 
v___x_2145_ = lean_st_ref_put(v___y_2126_, v___x_2144_);
v___x_2146_ = lean_st_ref_take(v___y_2125_);
v_mctx_2147_ = lean_ctor_get(v___x_2146_, 0);
v_zetaDeltaFVarIds_2148_ = lean_ctor_get(v___x_2146_, 2);
v_postponed_2149_ = lean_ctor_get(v___x_2146_, 3);
v_diag_2150_ = lean_ctor_get(v___x_2146_, 4);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v___x_2146_, 1);
lean_dec(v_unused_2164_);
v___x_2152_ = v___x_2146_;
v_isShared_2153_ = v_isSharedCheck_2163_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_diag_2150_);
lean_inc(v_postponed_2149_);
lean_inc(v_zetaDeltaFVarIds_2148_);
lean_inc(v_mctx_2147_);
lean_dec(v___x_2146_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2163_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v___x_2155_);
v___x_2157_ = v___x_2152_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_mctx_2147_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_zetaDeltaFVarIds_2148_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_postponed_2149_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_diag_2150_);
v___x_2157_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_st_ref_put(v___y_2125_, v___x_2157_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2154_);
v___x_2160_ = v___x_2122_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2154_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
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
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_declName_2107_);
v_a_2184_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2119_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2119_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v___x_2199_, lean_object* v_as_2200_, size_t v_sz_2201_, size_t v_i_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___redArg(v___x_2199_, v_as_2200_, v_sz_2201_, v_i_2202_, v_b_2203_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v___x_2210_, lean_object* v_as_2211_, lean_object* v_sz_2212_, lean_object* v_i_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2212_);
lean_dec(v_sz_2212_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2210_, v_as_2211_, v_sz_boxed_2220_, v_i_boxed_2221_, v_b_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec_ref(v_as_2211_);
lean_dec_ref(v___x_2210_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_st_mk_ref(v___x_2224_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2229_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = l_Lean_initializing();
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v_f_2229_);
v___x_2232_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2234_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2235_ = lean_st_ref_take(v___x_2234_);
v___x_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2236_, 0, v_f_2229_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = lean_st_ref_put(v___x_2234_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2245_, lean_object* v_as_x27_2246_, lean_object* v_b_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
if (lean_obj_tag(v_as_x27_2246_) == 0)
{
lean_object* v___x_2253_; 
lean_dec(v_declName_2245_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_b_2247_);
return v___x_2253_;
}
else
{
lean_object* v_head_2254_; lean_object* v_tail_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_dec_ref(v_b_2247_);
v_head_2254_ = lean_ctor_get(v_as_x27_2246_, 0);
v_tail_2255_ = lean_ctor_get(v_as_x27_2246_, 1);
v___x_2256_ = lean_box(0);
v___x_2257_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
lean_inc(v_head_2254_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
lean_inc(v_declName_2245_);
v___x_2258_ = lean_apply_6(v_head_2254_, v_declName_2245_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, lean_box(0));
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2269_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2269_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2269_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
if (lean_obj_tag(v_a_2259_) == 1)
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec(v_declName_2245_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_a_2259_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2256_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2264_);
v___x_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_del_object(v___x_2261_);
lean_dec(v_a_2259_);
v_as_x27_2246_ = v_tail_2255_;
v_b_2247_ = v___x_2257_;
goto _start;
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_declName_2245_);
v_a_2270_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2258_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2258_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2278_, lean_object* v_as_x27_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2278_, v_as_x27_2279_, v_b_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v_as_x27_2279_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2287_, lean_object* v_declName_2288_, uint8_t v_nonRec_2289_, lean_object* v___x_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2299_; lean_object* v_env_2300_; uint8_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2299_ = lean_st_ref_get(v___y_2294_);
v_env_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc_ref(v_env_2300_);
lean_dec(v___x_2299_);
v___x_2301_ = 1;
lean_inc(v___x_2287_);
v___x_2302_ = l_Lean_Environment_contains(v_env_2300_, v___x_2287_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
lean_dec(v___x_2287_);
lean_inc(v_declName_2288_);
v___x_2303_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2288_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; uint8_t v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = lean_unbox(v_a_2304_);
lean_dec(v_a_2304_);
if (v___x_2305_ == 0)
{
lean_dec_ref(v___x_2290_);
lean_dec(v_declName_2288_);
goto v___jp_2296_;
}
else
{
lean_object* v___x_2306_; 
lean_inc(v_declName_2288_);
v___x_2306_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2288_, v___y_2294_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; uint8_t v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_unbox(v_a_2307_);
lean_dec(v_a_2307_);
if (v___x_2308_ == 0)
{
if (v_nonRec_2289_ == 0)
{
lean_dec_ref(v___x_2290_);
lean_dec(v_declName_2288_);
goto v___jp_2296_;
}
else
{
lean_object* v___x_2309_; lean_object* v_env_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2309_ = lean_st_ref_get(v___y_2294_);
v_env_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc_ref(v_env_2310_);
lean_dec(v___x_2309_);
lean_inc(v_declName_2288_);
v___x_2311_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2310_, v_declName_2288_, v___x_2290_);
v___x_2312_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2288_, v___x_2311_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2312_;
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_dec_ref(v___x_2290_);
v___x_2313_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2314_ = lean_st_ref_get(v___x_2313_);
v___x_2315_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2316_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2288_, v___x_2314_, v___x_2315_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___x_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2326_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_fst_2321_; 
v_fst_2321_ = lean_ctor_get(v_a_2317_, 0);
lean_inc(v_fst_2321_);
lean_dec(v_a_2317_);
if (lean_obj_tag(v_fst_2321_) == 0)
{
lean_del_object(v___x_2319_);
goto v___jp_2296_;
}
else
{
lean_object* v_val_2322_; lean_object* v___x_2324_; 
v_val_2322_ = lean_ctor_get(v_fst_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v_fst_2321_, 1);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_val_2322_);
v___x_2324_ = v___x_2319_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_val_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_a_2327_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2316_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2316_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___x_2290_);
lean_dec(v_declName_2288_);
v_a_2335_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2306_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2306_);
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
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___x_2290_);
lean_dec(v_declName_2288_);
v_a_2343_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2303_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2303_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_dec_ref(v___x_2290_);
lean_dec(v_declName_2288_);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2287_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
v___jp_2296_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_box(0);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2353_, lean_object* v_declName_2354_, lean_object* v_nonRec_2355_, lean_object* v___x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
uint8_t v_nonRec_boxed_2362_; lean_object* v_res_2363_; 
v_nonRec_boxed_2362_ = lean_unbox(v_nonRec_2355_);
v_res_2363_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2353_, v_declName_2354_, v_nonRec_boxed_2362_, v___x_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_ref_2370_; lean_object* v___x_2371_; lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2380_; 
v_ref_2370_ = lean_ctor_get(v___y_2367_, 2);
v___x_2371_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2_spec__2(v_msg_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_inc(v_ref_2370_);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_ref_2370_);
lean_ctor_set(v___x_2376_, 1, v_a_2372_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 1);
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2388_, uint8_t v_isExporting_2389_, lean_object* v___x_2390_, lean_object* v___y_2391_, lean_object* v___x_2392_, lean_object* v_a_x3f_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v_env_2396_; lean_object* v_nextMacroScope_2397_; lean_object* v_ngen_2398_; lean_object* v_auxDeclNGen_2399_; lean_object* v_traceState_2400_; lean_object* v_recordedDeps_2401_; lean_object* v_messages_2402_; lean_object* v_infoState_2403_; lean_object* v_snapshotTasks_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2429_; 
v___x_2395_ = lean_st_ref_take(v___y_2388_);
v_env_2396_ = lean_ctor_get(v___x_2395_, 0);
v_nextMacroScope_2397_ = lean_ctor_get(v___x_2395_, 1);
v_ngen_2398_ = lean_ctor_get(v___x_2395_, 2);
v_auxDeclNGen_2399_ = lean_ctor_get(v___x_2395_, 3);
v_traceState_2400_ = lean_ctor_get(v___x_2395_, 4);
v_recordedDeps_2401_ = lean_ctor_get(v___x_2395_, 6);
v_messages_2402_ = lean_ctor_get(v___x_2395_, 7);
v_infoState_2403_ = lean_ctor_get(v___x_2395_, 8);
v_snapshotTasks_2404_ = lean_ctor_get(v___x_2395_, 9);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v___x_2395_, 5);
lean_dec(v_unused_2430_);
v___x_2406_ = v___x_2395_;
v_isShared_2407_ = v_isSharedCheck_2429_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_snapshotTasks_2404_);
lean_inc(v_infoState_2403_);
lean_inc(v_messages_2402_);
lean_inc(v_recordedDeps_2401_);
lean_inc(v_traceState_2400_);
lean_inc(v_auxDeclNGen_2399_);
lean_inc(v_ngen_2398_);
lean_inc(v_nextMacroScope_2397_);
lean_inc(v_env_2396_);
lean_dec(v___x_2395_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2429_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = l_Lean_Environment_setExporting(v_env_2396_, v_isExporting_2389_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 5, v___x_2390_);
lean_ctor_set(v___x_2406_, 0, v___x_2408_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_nextMacroScope_2397_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_ngen_2398_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_auxDeclNGen_2399_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_traceState_2400_);
lean_ctor_set(v_reuseFailAlloc_2428_, 5, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2428_, 6, v_recordedDeps_2401_);
lean_ctor_set(v_reuseFailAlloc_2428_, 7, v_messages_2402_);
lean_ctor_set(v_reuseFailAlloc_2428_, 8, v_infoState_2403_);
lean_ctor_set(v_reuseFailAlloc_2428_, 9, v_snapshotTasks_2404_);
v___x_2410_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_mctx_2413_; lean_object* v_zetaDeltaFVarIds_2414_; lean_object* v_postponed_2415_; lean_object* v_diag_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2426_; 
v___x_2411_ = lean_st_ref_put(v___y_2388_, v___x_2410_);
v___x_2412_ = lean_st_ref_take(v___y_2391_);
v_mctx_2413_ = lean_ctor_get(v___x_2412_, 0);
v_zetaDeltaFVarIds_2414_ = lean_ctor_get(v___x_2412_, 2);
v_postponed_2415_ = lean_ctor_get(v___x_2412_, 3);
v_diag_2416_ = lean_ctor_get(v___x_2412_, 4);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v___x_2412_, 1);
lean_dec(v_unused_2427_);
v___x_2418_ = v___x_2412_;
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_diag_2416_);
lean_inc(v_postponed_2415_);
lean_inc(v_zetaDeltaFVarIds_2414_);
lean_inc(v_mctx_2413_);
lean_dec(v___x_2412_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_box(0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v___x_2392_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_mctx_2413_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_zetaDeltaFVarIds_2414_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_postponed_2415_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v_diag_2416_);
v___x_2422_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_st_ref_put(v___y_2391_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2420_);
return v___x_2424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2431_, lean_object* v_isExporting_2432_, lean_object* v___x_2433_, lean_object* v___y_2434_, lean_object* v___x_2435_, lean_object* v_a_x3f_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v_isExporting_boxed_2438_; lean_object* v_res_2439_; 
v_isExporting_boxed_2438_ = lean_unbox(v_isExporting_2432_);
v_res_2439_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2431_, v_isExporting_boxed_2438_, v___x_2433_, v___y_2434_, v___x_2435_, v_a_x3f_2436_);
lean_dec(v_a_x3f_2436_);
lean_dec(v___y_2434_);
lean_dec(v___y_2431_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2440_, uint8_t v_isExporting_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; lean_object* v_env_2448_; lean_object* v___x_2449_; uint8_t v_isModule_2450_; 
v___x_2447_ = lean_st_ref_get(v___y_2445_);
v_env_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc_ref(v_env_2448_);
lean_dec(v___x_2447_);
v___x_2449_ = l_Lean_Environment_header(v_env_2448_);
v_isModule_2450_ = lean_ctor_get_uint8(v___x_2449_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2449_);
if (v_isModule_2450_ == 0)
{
lean_object* v___x_2451_; 
lean_dec_ref(v_env_2448_);
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2451_ = lean_apply_5(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, lean_box(0));
return v___x_2451_;
}
else
{
uint8_t v_isExporting_2452_; 
v_isExporting_2452_ = lean_ctor_get_uint8(v_env_2448_, sizeof(void*)*8);
lean_dec_ref(v_env_2448_);
if (v_isExporting_2441_ == 0)
{
if (v_isExporting_2452_ == 0)
{
lean_object* v___x_2519_; 
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2519_ = lean_apply_5(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, lean_box(0));
return v___x_2519_;
}
else
{
goto v___jp_2453_;
}
}
else
{
if (v_isExporting_2452_ == 0)
{
goto v___jp_2453_;
}
else
{
lean_object* v___x_2520_; 
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2520_ = lean_apply_5(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, lean_box(0));
return v___x_2520_;
}
}
v___jp_2453_:
{
lean_object* v___x_2454_; lean_object* v_env_2455_; lean_object* v_nextMacroScope_2456_; lean_object* v_ngen_2457_; lean_object* v_auxDeclNGen_2458_; lean_object* v_traceState_2459_; lean_object* v_recordedDeps_2460_; lean_object* v_messages_2461_; lean_object* v_infoState_2462_; lean_object* v_snapshotTasks_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2517_; 
v___x_2454_ = lean_st_ref_take(v___y_2445_);
v_env_2455_ = lean_ctor_get(v___x_2454_, 0);
v_nextMacroScope_2456_ = lean_ctor_get(v___x_2454_, 1);
v_ngen_2457_ = lean_ctor_get(v___x_2454_, 2);
v_auxDeclNGen_2458_ = lean_ctor_get(v___x_2454_, 3);
v_traceState_2459_ = lean_ctor_get(v___x_2454_, 4);
v_recordedDeps_2460_ = lean_ctor_get(v___x_2454_, 6);
v_messages_2461_ = lean_ctor_get(v___x_2454_, 7);
v_infoState_2462_ = lean_ctor_get(v___x_2454_, 8);
v_snapshotTasks_2463_ = lean_ctor_get(v___x_2454_, 9);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v___x_2454_, 5);
lean_dec(v_unused_2518_);
v___x_2465_ = v___x_2454_;
v_isShared_2466_ = v_isSharedCheck_2517_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_snapshotTasks_2463_);
lean_inc(v_infoState_2462_);
lean_inc(v_messages_2461_);
lean_inc(v_recordedDeps_2460_);
lean_inc(v_traceState_2459_);
lean_inc(v_auxDeclNGen_2458_);
lean_inc(v_ngen_2457_);
lean_inc(v_nextMacroScope_2456_);
lean_inc(v_env_2455_);
lean_dec(v___x_2454_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2517_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2467_ = l_Lean_Environment_setExporting(v_env_2455_, v_isExporting_2441_);
v___x_2468_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 5, v___x_2468_);
lean_ctor_set(v___x_2465_, 0, v___x_2467_);
v___x_2470_ = v___x_2465_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_nextMacroScope_2456_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_ngen_2457_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_auxDeclNGen_2458_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v_traceState_2459_);
lean_ctor_set(v_reuseFailAlloc_2516_, 5, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2516_, 6, v_recordedDeps_2460_);
lean_ctor_set(v_reuseFailAlloc_2516_, 7, v_messages_2461_);
lean_ctor_set(v_reuseFailAlloc_2516_, 8, v_infoState_2462_);
lean_ctor_set(v_reuseFailAlloc_2516_, 9, v_snapshotTasks_2463_);
v___x_2470_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_mctx_2473_; lean_object* v_zetaDeltaFVarIds_2474_; lean_object* v_postponed_2475_; lean_object* v_diag_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2514_; 
v___x_2471_ = lean_st_ref_put(v___y_2445_, v___x_2470_);
v___x_2472_ = lean_st_ref_take(v___y_2443_);
v_mctx_2473_ = lean_ctor_get(v___x_2472_, 0);
v_zetaDeltaFVarIds_2474_ = lean_ctor_get(v___x_2472_, 2);
v_postponed_2475_ = lean_ctor_get(v___x_2472_, 3);
v_diag_2476_ = lean_ctor_get(v___x_2472_, 4);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v___x_2472_, 1);
lean_dec(v_unused_2515_);
v___x_2478_ = v___x_2472_;
v_isShared_2479_ = v_isSharedCheck_2514_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_diag_2476_);
lean_inc(v_postponed_2475_);
lean_inc(v_zetaDeltaFVarIds_2474_);
lean_inc(v_mctx_2473_);
lean_dec(v___x_2472_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2514_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2480_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v___x_2480_);
v___x_2482_ = v___x_2478_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_mctx_2473_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_zetaDeltaFVarIds_2474_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v_postponed_2475_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v_diag_2476_);
v___x_2482_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; lean_object* v_r_2484_; 
v___x_2483_ = lean_st_ref_put(v___y_2443_, v___x_2482_);
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v_r_2484_ = lean_apply_5(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, lean_box(0));
if (lean_obj_tag(v_r_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2501_; 
v_a_2485_ = lean_ctor_get(v_r_2484_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_r_2484_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2487_ = v_r_2484_;
v_isShared_2488_ = v_isSharedCheck_2501_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v_r_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2501_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
lean_inc(v_a_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 1);
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
v___x_2491_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2445_, v_isExporting_2452_, v___x_2468_, v___y_2443_, v___x_2480_, v___x_2490_);
lean_dec_ref(v___x_2490_);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v___x_2491_, 0);
lean_dec(v_unused_2499_);
v___x_2493_ = v___x_2491_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_dec(v___x_2491_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v_a_2485_);
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2485_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
v_a_2502_ = lean_ctor_get(v_r_2484_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v_r_2484_, 1);
v___x_2503_ = lean_box(0);
v___x_2504_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2445_, v_isExporting_2452_, v___x_2468_, v___y_2443_, v___x_2480_, v___x_2503_);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v___x_2504_, 0);
lean_dec(v_unused_2512_);
v___x_2506_ = v___x_2504_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_dec(v___x_2504_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
lean_ctor_set_tag(v___x_2506_, 1);
lean_ctor_set(v___x_2506_, 0, v_a_2502_);
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2502_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2521_, lean_object* v_isExporting_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
uint8_t v_isExporting_boxed_2528_; lean_object* v_res_2529_; 
v_isExporting_boxed_2528_ = lean_unbox(v_isExporting_2522_);
v_res_2529_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2521_, v_isExporting_boxed_2528_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2530_, uint8_t v_when_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
if (v_when_2531_ == 0)
{
lean_object* v___x_2537_; 
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v___x_2537_ = lean_apply_5(v_x_2530_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, lean_box(0));
return v___x_2537_;
}
else
{
uint8_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = 0;
v___x_2539_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2530_, v___x_2538_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2540_, lean_object* v_when_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
uint8_t v_when_boxed_2547_; lean_object* v_res_2548_; 
v_when_boxed_2547_ = lean_unbox(v_when_2541_);
v_res_2548_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2540_, v_when_boxed_2547_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2548_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2558_, uint8_t v_nonRec_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; lean_object* v_env_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___f_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2565_ = lean_st_ref_get(v___y_2563_);
v_env_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_ref(v_env_2566_);
lean_dec(v___x_2565_);
v___x_2567_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2558_);
v___x_2568_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2566_, v_declName_2558_, v___x_2567_);
v___x_2569_ = lean_box(v_nonRec_2559_);
lean_inc(v___x_2568_);
v___f_2570_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2570_, 0, v___x_2568_);
lean_closure_set(v___f_2570_, 1, v_declName_2558_);
lean_closure_set(v___f_2570_, 2, v___x_2569_);
lean_closure_set(v___f_2570_, 3, v___x_2567_);
v___x_2571_ = 1;
v___x_2572_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2570_, v___x_2571_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
if (lean_obj_tag(v_a_2573_) == 1)
{
lean_object* v_val_2574_; uint8_t v___x_2575_; 
v_val_2574_ = lean_ctor_get(v_a_2573_, 0);
lean_inc(v_val_2574_);
lean_dec_ref_known(v_a_2573_, 1);
v___x_2575_ = lean_name_eq(v_val_2574_, v___x_2568_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref_known(v___x_2572_, 1);
v___x_2576_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2577_ = l_Lean_MessageData_ofName(v_val_2574_);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = l_Lean_MessageData_ofName(v___x_2568_);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2584_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
else
{
lean_dec(v_val_2574_);
lean_dec(v___x_2568_);
return v___x_2572_;
}
}
else
{
lean_dec(v_a_2573_);
lean_dec(v___x_2568_);
return v___x_2572_;
}
}
else
{
lean_dec(v___x_2568_);
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2594_, lean_object* v_nonRec_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
uint8_t v_nonRec_boxed_2601_; lean_object* v_res_2602_; 
v_nonRec_boxed_2601_ = lean_unbox(v_nonRec_2595_);
v_res_2602_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2594_, v_nonRec_boxed_2601_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2603_, uint8_t v_nonRec_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2610_ = lean_box(v_nonRec_2604_);
v___f_2611_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2611_, 0, v_declName_2603_);
lean_closure_set(v___f_2611_, 1, v___x_2610_);
v___x_2612_ = lean_unsigned_to_nat(32u);
v___x_2613_ = lean_mk_empty_array_with_capacity(v___x_2612_);
lean_dec_ref(v___x_2613_);
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2));
v___x_2616_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2614_, v___x_2615_, v___f_2611_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2617_, lean_object* v_nonRec_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
uint8_t v_nonRec_boxed_2624_; lean_object* v_res_2625_; 
v_nonRec_boxed_2624_ = lean_unbox(v_nonRec_2618_);
v_res_2625_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2617_, v_nonRec_boxed_2624_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2626_, lean_object* v_as_2627_, lean_object* v_as_x27_2628_, lean_object* v_b_2629_, lean_object* v_a_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2626_, v_as_x27_2628_, v_b_2629_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2637_, lean_object* v_as_2638_, lean_object* v_as_x27_2639_, lean_object* v_b_2640_, lean_object* v_a_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2637_, v_as_2638_, v_as_x27_2639_, v_b_2640_, v_a_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v_as_x27_2639_);
lean_dec(v_as_2638_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2648_, lean_object* v_x_2649_, uint8_t v_isExporting_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2649_, v_isExporting_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2657_, lean_object* v_x_2658_, lean_object* v_isExporting_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
uint8_t v_isExporting_boxed_2665_; lean_object* v_res_2666_; 
v_isExporting_boxed_2665_ = lean_unbox(v_isExporting_2659_);
v_res_2666_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2657_, v_x_2658_, v_isExporting_boxed_2665_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2667_, lean_object* v_x_2668_, uint8_t v_when_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2668_, v_when_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2676_, lean_object* v_x_2677_, lean_object* v_when_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v_when_boxed_2684_; lean_object* v_res_2685_; 
v_when_boxed_2684_ = lean_unbox(v_when_2678_);
v_res_2685_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2676_, v_x_2677_, v_when_boxed_2684_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2686_, lean_object* v_msg_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2694_, lean_object* v_msg_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2694_, v_msg_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2701_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_unsigned_to_nat(32u);
v___x_2703_ = lean_mk_empty_array_with_capacity(v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2705_ = ((size_t)5ULL);
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_unsigned_to_nat(32u);
v___x_2708_ = lean_mk_empty_array_with_capacity(v___x_2707_);
v___x_2709_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2710_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v___x_2708_);
lean_ctor_set(v___x_2710_, 2, v___x_2706_);
lean_ctor_set(v___x_2710_, 3, v___x_2706_);
lean_ctor_set_usize(v___x_2710_, 4, v___x_2705_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; lean_object* v_traceState_2714_; lean_object* v_traces_2715_; lean_object* v___x_2716_; lean_object* v_traceState_2717_; lean_object* v_env_2718_; lean_object* v_nextMacroScope_2719_; lean_object* v_ngen_2720_; lean_object* v_auxDeclNGen_2721_; lean_object* v_cache_2722_; lean_object* v_recordedDeps_2723_; lean_object* v_messages_2724_; lean_object* v_infoState_2725_; lean_object* v_snapshotTasks_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2745_; 
v___x_2713_ = lean_st_ref_get(v___y_2711_);
v_traceState_2714_ = lean_ctor_get(v___x_2713_, 4);
lean_inc_ref(v_traceState_2714_);
lean_dec(v___x_2713_);
v_traces_2715_ = lean_ctor_get(v_traceState_2714_, 0);
lean_inc_ref(v_traces_2715_);
lean_dec_ref(v_traceState_2714_);
v___x_2716_ = lean_st_ref_take(v___y_2711_);
v_traceState_2717_ = lean_ctor_get(v___x_2716_, 4);
v_env_2718_ = lean_ctor_get(v___x_2716_, 0);
v_nextMacroScope_2719_ = lean_ctor_get(v___x_2716_, 1);
v_ngen_2720_ = lean_ctor_get(v___x_2716_, 2);
v_auxDeclNGen_2721_ = lean_ctor_get(v___x_2716_, 3);
v_cache_2722_ = lean_ctor_get(v___x_2716_, 5);
v_recordedDeps_2723_ = lean_ctor_get(v___x_2716_, 6);
v_messages_2724_ = lean_ctor_get(v___x_2716_, 7);
v_infoState_2725_ = lean_ctor_get(v___x_2716_, 8);
v_snapshotTasks_2726_ = lean_ctor_get(v___x_2716_, 9);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2728_ = v___x_2716_;
v_isShared_2729_ = v_isSharedCheck_2745_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_snapshotTasks_2726_);
lean_inc(v_infoState_2725_);
lean_inc(v_messages_2724_);
lean_inc(v_recordedDeps_2723_);
lean_inc(v_cache_2722_);
lean_inc(v_traceState_2717_);
lean_inc(v_auxDeclNGen_2721_);
lean_inc(v_ngen_2720_);
lean_inc(v_nextMacroScope_2719_);
lean_inc(v_env_2718_);
lean_dec(v___x_2716_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2745_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
uint64_t v_tid_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2743_; 
v_tid_2730_ = lean_ctor_get_uint64(v_traceState_2717_, sizeof(void*)*1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_traceState_2717_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v_traceState_2717_, 0);
lean_dec(v_unused_2744_);
v___x_2732_ = v_traceState_2717_;
v_isShared_2733_ = v_isSharedCheck_2743_;
goto v_resetjp_2731_;
}
else
{
lean_dec(v_traceState_2717_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2743_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2734_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2734_);
lean_ctor_set_uint64(v_reuseFailAlloc_2742_, sizeof(void*)*1, v_tid_2730_);
v___x_2736_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2738_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 4, v___x_2736_);
v___x_2738_ = v___x_2728_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_env_2718_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_nextMacroScope_2719_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_ngen_2720_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v_auxDeclNGen_2721_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2741_, 5, v_cache_2722_);
lean_ctor_set(v_reuseFailAlloc_2741_, 6, v_recordedDeps_2723_);
lean_ctor_set(v_reuseFailAlloc_2741_, 7, v_messages_2724_);
lean_ctor_set(v_reuseFailAlloc_2741_, 8, v_infoState_2725_);
lean_ctor_set(v_reuseFailAlloc_2741_, 9, v_snapshotTasks_2726_);
v___x_2738_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_st_ref_put(v___y_2711_, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_traces_2715_);
return v___x_2740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2746_);
lean_dec(v___y_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = 0;
v___x_2762_ = lean_box(v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2771_ = l_Lean_stringToMessageData(v___x_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2772_, lean_object* v_x_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2777_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2778_ = l_Lean_MessageData_ofName(v_name_2772_);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2781_, v_x_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec_ref(v_x_2782_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2787_){
_start:
{
if (lean_obj_tag(v_x_2787_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_a_2789_ = lean_ctor_get(v_x_2787_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_x_2787_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v_x_2787_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v_x_2787_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 1);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
v_a_2797_ = lean_ctor_get(v_x_2787_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_x_2787_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v_x_2787_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v_x_2787_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set_tag(v___x_2799_, 0);
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2808_){
_start:
{
if (lean_obj_tag(v_e_2808_) == 0)
{
uint8_t v___x_2809_; 
v___x_2809_ = 2;
return v___x_2809_;
}
else
{
lean_object* v_a_2810_; uint8_t v___x_2811_; 
v_a_2810_ = lean_ctor_get(v_e_2808_, 0);
v___x_2811_ = lean_unbox(v_a_2810_);
if (v___x_2811_ == 0)
{
uint8_t v___x_2812_; 
v___x_2812_ = 1;
return v___x_2812_;
}
else
{
uint8_t v___x_2813_; 
v___x_2813_ = 0;
return v___x_2813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2814_){
_start:
{
uint8_t v_res_2815_; lean_object* v_r_2816_; 
v_res_2815_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2814_);
lean_dec_ref(v_e_2814_);
v_r_2816_ = lean_box(v_res_2815_);
return v_r_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2817_, size_t v_i_2818_, lean_object* v_bs_2819_){
_start:
{
uint8_t v___x_2820_; 
v___x_2820_ = lean_usize_dec_lt(v_i_2818_, v_sz_2817_);
if (v___x_2820_ == 0)
{
return v_bs_2819_;
}
else
{
lean_object* v_v_2821_; lean_object* v_msg_2822_; lean_object* v___x_2823_; lean_object* v_bs_x27_2824_; size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v_v_2821_ = lean_array_uget_borrowed(v_bs_2819_, v_i_2818_);
v_msg_2822_ = lean_ctor_get(v_v_2821_, 1);
lean_inc_ref(v_msg_2822_);
v___x_2823_ = lean_unsigned_to_nat(0u);
v_bs_x27_2824_ = lean_array_uset(v_bs_2819_, v_i_2818_, v___x_2823_);
v___x_2825_ = ((size_t)1ULL);
v___x_2826_ = lean_usize_add(v_i_2818_, v___x_2825_);
v___x_2827_ = lean_array_uset(v_bs_x27_2824_, v_i_2818_, v_msg_2822_);
v_i_2818_ = v___x_2826_;
v_bs_2819_ = v___x_2827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2829_, lean_object* v_i_2830_, lean_object* v_bs_2831_){
_start:
{
size_t v_sz_boxed_2832_; size_t v_i_boxed_2833_; lean_object* v_res_2834_; 
v_sz_boxed_2832_ = lean_unbox_usize(v_sz_2829_);
lean_dec(v_sz_2829_);
v_i_boxed_2833_ = lean_unbox_usize(v_i_2830_);
lean_dec(v_i_2830_);
v_res_2834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2832_, v_i_boxed_2833_, v_bs_2831_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2835_, lean_object* v_data_2836_, lean_object* v_ref_2837_, lean_object* v_msg_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_toCold_2842_; lean_object* v_currRecDepth_2843_; lean_object* v_ref_2844_; uint16_t v_optionFlags_2845_; uint8_t v_suppressElabErrors_2846_; uint8_t v_isRecordingDeps_2847_; lean_object* v_ref_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v_traceState_2851_; lean_object* v_traces_2852_; lean_object* v___x_2853_; size_t v_sz_2854_; size_t v___x_2855_; lean_object* v___x_2856_; lean_object* v_msg_2857_; lean_object* v___x_2858_; lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2897_; 
v_toCold_2842_ = lean_ctor_get(v___y_2839_, 0);
v_currRecDepth_2843_ = lean_ctor_get(v___y_2839_, 1);
v_ref_2844_ = lean_ctor_get(v___y_2839_, 2);
v_optionFlags_2845_ = lean_ctor_get_uint16(v___y_2839_, sizeof(void*)*3);
v_suppressElabErrors_2846_ = lean_ctor_get_uint8(v___y_2839_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2847_ = lean_ctor_get_uint8(v___y_2839_, sizeof(void*)*3 + 3);
v_ref_2848_ = l_Lean_replaceRef(v_ref_2837_, v_ref_2844_);
lean_inc(v_currRecDepth_2843_);
lean_inc_ref(v_toCold_2842_);
v___x_2849_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2849_, 0, v_toCold_2842_);
lean_ctor_set(v___x_2849_, 1, v_currRecDepth_2843_);
lean_ctor_set(v___x_2849_, 2, v_ref_2848_);
lean_ctor_set_uint16(v___x_2849_, sizeof(void*)*3, v_optionFlags_2845_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*3 + 2, v_suppressElabErrors_2846_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*3 + 3, v_isRecordingDeps_2847_);
v___x_2850_ = lean_st_ref_get(v___y_2840_);
v_traceState_2851_ = lean_ctor_get(v___x_2850_, 4);
lean_inc_ref(v_traceState_2851_);
lean_dec(v___x_2850_);
v_traces_2852_ = lean_ctor_get(v_traceState_2851_, 0);
lean_inc_ref(v_traces_2852_);
lean_dec_ref(v_traceState_2851_);
v___x_2853_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2852_);
lean_dec_ref(v_traces_2852_);
v_sz_2854_ = lean_array_size(v___x_2853_);
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2854_, v___x_2855_, v___x_2853_);
v_msg_2857_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2857_, 0, v_data_2836_);
lean_ctor_set(v_msg_2857_, 1, v_msg_2838_);
lean_ctor_set(v_msg_2857_, 2, v___x_2856_);
v___x_2858_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2857_, v___x_2849_, v___y_2840_);
lean_dec_ref_known(v___x_2849_, 3);
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2861_ = v___x_2858_;
v_isShared_2862_ = v_isSharedCheck_2897_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2897_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; lean_object* v_traceState_2864_; lean_object* v_env_2865_; lean_object* v_nextMacroScope_2866_; lean_object* v_ngen_2867_; lean_object* v_auxDeclNGen_2868_; lean_object* v_cache_2869_; lean_object* v_recordedDeps_2870_; lean_object* v_messages_2871_; lean_object* v_infoState_2872_; lean_object* v_snapshotTasks_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2896_; 
v___x_2863_ = lean_st_ref_take(v___y_2840_);
v_traceState_2864_ = lean_ctor_get(v___x_2863_, 4);
v_env_2865_ = lean_ctor_get(v___x_2863_, 0);
v_nextMacroScope_2866_ = lean_ctor_get(v___x_2863_, 1);
v_ngen_2867_ = lean_ctor_get(v___x_2863_, 2);
v_auxDeclNGen_2868_ = lean_ctor_get(v___x_2863_, 3);
v_cache_2869_ = lean_ctor_get(v___x_2863_, 5);
v_recordedDeps_2870_ = lean_ctor_get(v___x_2863_, 6);
v_messages_2871_ = lean_ctor_get(v___x_2863_, 7);
v_infoState_2872_ = lean_ctor_get(v___x_2863_, 8);
v_snapshotTasks_2873_ = lean_ctor_get(v___x_2863_, 9);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2875_ = v___x_2863_;
v_isShared_2876_ = v_isSharedCheck_2896_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_snapshotTasks_2873_);
lean_inc(v_infoState_2872_);
lean_inc(v_messages_2871_);
lean_inc(v_recordedDeps_2870_);
lean_inc(v_cache_2869_);
lean_inc(v_traceState_2864_);
lean_inc(v_auxDeclNGen_2868_);
lean_inc(v_ngen_2867_);
lean_inc(v_nextMacroScope_2866_);
lean_inc(v_env_2865_);
lean_dec(v___x_2863_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2896_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
uint64_t v_tid_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2894_; 
v_tid_2877_ = lean_ctor_get_uint64(v_traceState_2864_, sizeof(void*)*1);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_traceState_2864_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v_traceState_2864_, 0);
lean_dec(v_unused_2895_);
v___x_2879_ = v_traceState_2864_;
v_isShared_2880_ = v_isSharedCheck_2894_;
goto v_resetjp_2878_;
}
else
{
lean_dec(v_traceState_2864_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2894_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v_ref_2837_);
lean_ctor_set(v___x_2882_, 1, v_a_2859_);
v___x_2883_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2835_, v___x_2882_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2883_);
v___x_2885_ = v___x_2879_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2883_);
lean_ctor_set_uint64(v_reuseFailAlloc_2893_, sizeof(void*)*1, v_tid_2877_);
v___x_2885_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2887_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v___x_2885_);
v___x_2887_ = v___x_2875_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_env_2865_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_nextMacroScope_2866_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_ngen_2867_);
lean_ctor_set(v_reuseFailAlloc_2892_, 3, v_auxDeclNGen_2868_);
lean_ctor_set(v_reuseFailAlloc_2892_, 4, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2892_, 5, v_cache_2869_);
lean_ctor_set(v_reuseFailAlloc_2892_, 6, v_recordedDeps_2870_);
lean_ctor_set(v_reuseFailAlloc_2892_, 7, v_messages_2871_);
lean_ctor_set(v_reuseFailAlloc_2892_, 8, v_infoState_2872_);
lean_ctor_set(v_reuseFailAlloc_2892_, 9, v_snapshotTasks_2873_);
v___x_2887_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = lean_st_ref_put(v___y_2840_, v___x_2887_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2881_);
v___x_2890_ = v___x_2861_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2881_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2898_, lean_object* v_data_2899_, lean_object* v_ref_2900_, lean_object* v_msg_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2898_, v_data_2899_, v_ref_2900_, v_msg_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2905_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2908_ = l_Lean_stringToMessageData(v___x_2907_);
return v___x_2908_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2909_; double v___x_2910_; 
v___x_2909_ = lean_unsigned_to_nat(1000u);
v___x_2910_ = lean_float_of_nat(v___x_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2911_, uint8_t v_collapsed_2912_, lean_object* v_tag_2913_, lean_object* v_opts_2914_, uint8_t v_clsEnabled_2915_, lean_object* v_oldTraces_2916_, lean_object* v_msg_2917_, lean_object* v_resStartStop_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_fst_2922_; lean_object* v_snd_2923_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v_data_2927_; lean_object* v_fst_2938_; lean_object* v_snd_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___y_2943_; lean_object* v_a_2944_; uint8_t v___y_2959_; double v___y_2991_; 
v_fst_2922_ = lean_ctor_get(v_resStartStop_2918_, 0);
lean_inc(v_fst_2922_);
v_snd_2923_ = lean_ctor_get(v_resStartStop_2918_, 1);
lean_inc(v_snd_2923_);
lean_dec_ref(v_resStartStop_2918_);
v_fst_2938_ = lean_ctor_get(v_snd_2923_, 0);
lean_inc(v_fst_2938_);
v_snd_2939_ = lean_ctor_get(v_snd_2923_, 1);
lean_inc(v_snd_2939_);
lean_dec(v_snd_2923_);
v___x_2940_ = l_Lean_trace_profiler;
v___x_2941_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2914_, v___x_2940_);
if (v___x_2941_ == 0)
{
v___y_2959_ = v___x_2941_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2997_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_opts_2914_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; double v___x_3000_; double v___x_3001_; double v___x_3002_; 
v___x_2998_ = l_Lean_trace_profiler_threshold;
v___x_2999_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2914_, v___x_2998_);
v___x_3000_ = lean_float_of_nat(v___x_2999_);
v___x_3001_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3002_ = lean_float_div(v___x_3000_, v___x_3001_);
v___y_2991_ = v___x_3002_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; double v___x_3005_; 
v___x_3003_ = l_Lean_trace_profiler_threshold;
v___x_3004_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2914_, v___x_3003_);
v___x_3005_ = lean_float_of_nat(v___x_3004_);
v___y_2991_ = v___x_3005_;
goto v___jp_2990_;
}
}
v___jp_2924_:
{
lean_object* v___x_2928_; 
lean_inc(v___y_2926_);
v___x_2928_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2916_, v_data_2927_, v___y_2926_, v___y_2925_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v___x_2929_; 
lean_dec_ref_known(v___x_2928_, 1);
v___x_2929_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2922_);
return v___x_2929_;
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_fst_2922_);
v_a_2930_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2928_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2928_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
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
v___jp_2942_:
{
uint8_t v_result_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; double v___x_2948_; lean_object* v_data_2949_; 
v_result_2945_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2922_);
v___x_2946_ = lean_box(v_result_2945_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
v___x_2948_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__0);
lean_inc_ref(v_tag_2913_);
lean_inc_ref(v___x_2947_);
lean_inc(v_cls_2911_);
v_data_2949_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2949_, 0, v_cls_2911_);
lean_ctor_set(v_data_2949_, 1, v___x_2947_);
lean_ctor_set(v_data_2949_, 2, v_tag_2913_);
lean_ctor_set_float(v_data_2949_, sizeof(void*)*3, v___x_2948_);
lean_ctor_set_float(v_data_2949_, sizeof(void*)*3 + 8, v___x_2948_);
lean_ctor_set_uint8(v_data_2949_, sizeof(void*)*3 + 16, v_collapsed_2912_);
if (v___x_2941_ == 0)
{
lean_dec_ref_known(v___x_2947_, 1);
lean_dec(v_snd_2939_);
lean_dec(v_fst_2938_);
lean_dec_ref(v_tag_2913_);
lean_dec(v_cls_2911_);
v___y_2925_ = v_a_2944_;
v___y_2926_ = v___y_2943_;
v_data_2927_ = v_data_2949_;
goto v___jp_2924_;
}
else
{
lean_object* v_data_2950_; double v___x_2951_; double v___x_2952_; 
lean_dec_ref_known(v_data_2949_, 3);
v_data_2950_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2950_, 0, v_cls_2911_);
lean_ctor_set(v_data_2950_, 1, v___x_2947_);
lean_ctor_set(v_data_2950_, 2, v_tag_2913_);
v___x_2951_ = lean_unbox_float(v_fst_2938_);
lean_dec(v_fst_2938_);
lean_ctor_set_float(v_data_2950_, sizeof(void*)*3, v___x_2951_);
v___x_2952_ = lean_unbox_float(v_snd_2939_);
lean_dec(v_snd_2939_);
lean_ctor_set_float(v_data_2950_, sizeof(void*)*3 + 8, v___x_2952_);
lean_ctor_set_uint8(v_data_2950_, sizeof(void*)*3 + 16, v_collapsed_2912_);
v___y_2925_ = v_a_2944_;
v___y_2926_ = v___y_2943_;
v_data_2927_ = v_data_2950_;
goto v___jp_2924_;
}
}
v___jp_2953_:
{
lean_object* v_ref_2954_; lean_object* v___x_2955_; 
v_ref_2954_ = lean_ctor_get(v___y_2919_, 2);
lean_inc(v___y_2920_);
lean_inc_ref(v___y_2919_);
lean_inc(v_fst_2922_);
v___x_2955_ = lean_apply_4(v_msg_2917_, v_fst_2922_, v___y_2919_, v___y_2920_, lean_box(0));
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___y_2943_ = v_ref_2954_;
v_a_2944_ = v_a_2956_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_2957_; 
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2943_ = v_ref_2954_;
v_a_2944_ = v___x_2957_;
goto v___jp_2942_;
}
}
v___jp_2958_:
{
if (v_clsEnabled_2915_ == 0)
{
if (v___y_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v_traceState_2961_; lean_object* v_env_2962_; lean_object* v_nextMacroScope_2963_; lean_object* v_ngen_2964_; lean_object* v_auxDeclNGen_2965_; lean_object* v_cache_2966_; lean_object* v_recordedDeps_2967_; lean_object* v_messages_2968_; lean_object* v_infoState_2969_; lean_object* v_snapshotTasks_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v_snd_2939_);
lean_dec(v_fst_2938_);
lean_dec_ref(v_msg_2917_);
lean_dec_ref(v_tag_2913_);
lean_dec(v_cls_2911_);
v___x_2960_ = lean_st_ref_take(v___y_2920_);
v_traceState_2961_ = lean_ctor_get(v___x_2960_, 4);
v_env_2962_ = lean_ctor_get(v___x_2960_, 0);
v_nextMacroScope_2963_ = lean_ctor_get(v___x_2960_, 1);
v_ngen_2964_ = lean_ctor_get(v___x_2960_, 2);
v_auxDeclNGen_2965_ = lean_ctor_get(v___x_2960_, 3);
v_cache_2966_ = lean_ctor_get(v___x_2960_, 5);
v_recordedDeps_2967_ = lean_ctor_get(v___x_2960_, 6);
v_messages_2968_ = lean_ctor_get(v___x_2960_, 7);
v_infoState_2969_ = lean_ctor_get(v___x_2960_, 8);
v_snapshotTasks_2970_ = lean_ctor_get(v___x_2960_, 9);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2972_ = v___x_2960_;
v_isShared_2973_ = v_isSharedCheck_2989_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_snapshotTasks_2970_);
lean_inc(v_infoState_2969_);
lean_inc(v_messages_2968_);
lean_inc(v_recordedDeps_2967_);
lean_inc(v_cache_2966_);
lean_inc(v_traceState_2961_);
lean_inc(v_auxDeclNGen_2965_);
lean_inc(v_ngen_2964_);
lean_inc(v_nextMacroScope_2963_);
lean_inc(v_env_2962_);
lean_dec(v___x_2960_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2989_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
uint64_t v_tid_2974_; lean_object* v_traces_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2988_; 
v_tid_2974_ = lean_ctor_get_uint64(v_traceState_2961_, sizeof(void*)*1);
v_traces_2975_ = lean_ctor_get(v_traceState_2961_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_traceState_2961_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2977_ = v_traceState_2961_;
v_isShared_2978_ = v_isSharedCheck_2988_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_traces_2975_);
lean_dec(v_traceState_2961_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2988_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2979_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2916_, v_traces_2975_);
lean_dec_ref(v_traces_2975_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2979_);
v___x_2981_ = v___x_2977_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2979_);
lean_ctor_set_uint64(v_reuseFailAlloc_2987_, sizeof(void*)*1, v_tid_2974_);
v___x_2981_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 4, v___x_2981_);
v___x_2983_ = v___x_2972_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_env_2962_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_nextMacroScope_2963_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_ngen_2964_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_auxDeclNGen_2965_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v_cache_2966_);
lean_ctor_set(v_reuseFailAlloc_2986_, 6, v_recordedDeps_2967_);
lean_ctor_set(v_reuseFailAlloc_2986_, 7, v_messages_2968_);
lean_ctor_set(v_reuseFailAlloc_2986_, 8, v_infoState_2969_);
lean_ctor_set(v_reuseFailAlloc_2986_, 9, v_snapshotTasks_2970_);
v___x_2983_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_st_ref_put(v___y_2920_, v___x_2983_);
v___x_2985_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2922_);
return v___x_2985_;
}
}
}
}
}
else
{
goto v___jp_2953_;
}
}
else
{
goto v___jp_2953_;
}
}
v___jp_2990_:
{
double v___x_2992_; double v___x_2993_; double v___x_2994_; uint8_t v___x_2995_; 
v___x_2992_ = lean_unbox_float(v_snd_2939_);
v___x_2993_ = lean_unbox_float(v_fst_2938_);
v___x_2994_ = lean_float_sub(v___x_2992_, v___x_2993_);
v___x_2995_ = lean_float_decLt(v___y_2991_, v___x_2994_);
v___y_2959_ = v___x_2995_;
goto v___jp_2958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3006_, lean_object* v_collapsed_3007_, lean_object* v_tag_3008_, lean_object* v_opts_3009_, lean_object* v_clsEnabled_3010_, lean_object* v_oldTraces_3011_, lean_object* v_msg_3012_, lean_object* v_resStartStop_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
uint8_t v_collapsed_boxed_3017_; uint8_t v_clsEnabled_boxed_3018_; lean_object* v_res_3019_; 
v_collapsed_boxed_3017_ = lean_unbox(v_collapsed_3007_);
v_clsEnabled_boxed_3018_ = lean_unbox(v_clsEnabled_3010_);
v_res_3019_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3006_, v_collapsed_boxed_3017_, v_tag_3008_, v_opts_3009_, v_clsEnabled_boxed_3018_, v_oldTraces_3011_, v_msg_3012_, v_resStartStop_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec_ref(v_opts_3009_);
return v_res_3019_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
lean_ctor_set(v___x_3024_, 2, v___x_3023_);
lean_ctor_set(v___x_3024_, 3, v___x_3023_);
lean_ctor_set(v___x_3024_, 4, v___x_3022_);
lean_ctor_set(v___x_3024_, 5, v___x_3022_);
lean_ctor_set(v___x_3024_, 6, v___x_3022_);
lean_ctor_set(v___x_3024_, 7, v___x_3022_);
lean_ctor_set(v___x_3024_, 8, v___x_3022_);
lean_ctor_set(v___x_3024_, 9, v___x_3022_);
lean_ctor_set(v___x_3024_, 10, v___x_3022_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3026_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
lean_ctor_set(v___x_3026_, 2, v___x_3025_);
lean_ctor_set(v___x_3026_, 3, v___x_3025_);
lean_ctor_set(v___x_3026_, 4, v___x_3025_);
lean_ctor_set(v___x_3026_, 5, v___x_3025_);
return v___x_3026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_3028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
lean_ctor_set(v___x_3028_, 2, v___x_3027_);
lean_ctor_set(v___x_3028_, 3, v___x_3027_);
lean_ctor_set(v___x_3028_, 4, v___x_3027_);
return v___x_3028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__2___closed__1));
v___x_3034_ = l_Lean_Name_append(v___x_3033_, v___x_3032_);
return v___x_3034_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3035_; double v___x_3036_; 
v___x_3035_ = lean_unsigned_to_nat(1000000000u);
v___x_3036_ = lean_float_of_nat(v___x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3037_, lean_object* v___f_3038_, lean_object* v_name_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_toCold_3043_; lean_object* v_options_3044_; uint8_t v_hasTrace_3045_; 
v_toCold_3043_ = lean_ctor_get(v___y_3040_, 0);
v_options_3044_ = lean_ctor_get(v_toCold_3043_, 2);
v_hasTrace_3045_ = lean_ctor_get_uint8(v_options_3044_, sizeof(void*)*1);
if (v_hasTrace_3045_ == 0)
{
lean_object* v___x_3046_; lean_object* v_env_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v___f_3038_);
v___x_3046_ = lean_st_ref_get(v___y_3041_);
v_env_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc_ref(v_env_3047_);
lean_dec(v___x_3046_);
lean_inc(v_name_3039_);
v___x_3048_ = l_Lean_Meta_declFromEqLikeName(v_env_3047_, v_name_3039_);
if (lean_obj_tag(v___x_3048_) == 1)
{
lean_object* v_val_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3154_; 
v_val_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3154_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_val_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3154_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v_fst_3053_; lean_object* v_snd_3054_; lean_object* v___x_3055_; lean_object* v_env_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v_fst_3053_ = lean_ctor_get(v_val_3049_, 0);
lean_inc_n(v_fst_3053_, 2);
v_snd_3054_ = lean_ctor_get(v_val_3049_, 1);
lean_inc_n(v_snd_3054_, 2);
lean_dec(v_val_3049_);
v___x_3055_ = lean_st_ref_get(v___y_3041_);
v_env_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc_ref(v_env_3056_);
lean_dec(v___x_3055_);
v___x_3057_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3056_, v_fst_3053_, v_snd_3054_);
v___x_3058_ = lean_name_eq(v_name_3039_, v___x_3057_);
lean_dec(v___x_3057_);
lean_dec(v_name_3039_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_dec(v_snd_3054_);
lean_dec(v_fst_3053_);
lean_dec(v___x_3037_);
v___x_3059_ = lean_box(v_hasTrace_3045_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3059_);
v___x_3061_ = v___x_3051_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
else
{
uint8_t v___x_3063_; lean_object* v_a_3065_; 
lean_inc(v_snd_3054_);
v___x_3063_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3054_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v_a_3082_; 
lean_del_object(v___x_3051_);
v___x_3079_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3080_ = lean_string_dec_eq(v_snd_3054_, v___x_3079_);
lean_dec(v_snd_3054_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v_fst_3053_);
lean_dec(v___x_3037_);
v___x_3094_ = lean_box(v_hasTrace_3045_);
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
return v___x_3095_;
}
else
{
uint8_t v___x_3096_; uint8_t v___x_3097_; uint8_t v___x_3098_; lean_object* v___x_3099_; uint64_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3096_ = 1;
v___x_3097_ = 0;
v___x_3098_ = 2;
v___x_3099_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3099_, 0, v___x_3063_);
lean_ctor_set_uint8(v___x_3099_, 1, v___x_3063_);
lean_ctor_set_uint8(v___x_3099_, 2, v___x_3063_);
lean_ctor_set_uint8(v___x_3099_, 3, v___x_3063_);
lean_ctor_set_uint8(v___x_3099_, 4, v___x_3063_);
lean_ctor_set_uint8(v___x_3099_, 5, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 6, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 7, v___x_3063_);
lean_ctor_set_uint8(v___x_3099_, 8, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 9, v___x_3096_);
lean_ctor_set_uint8(v___x_3099_, 10, v___x_3097_);
lean_ctor_set_uint8(v___x_3099_, 11, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 12, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 13, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 14, v___x_3098_);
lean_ctor_set_uint8(v___x_3099_, 15, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 16, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 17, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 18, v___x_3080_);
lean_ctor_set_uint8(v___x_3099_, 19, v___x_3063_);
v___x_3100_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3099_);
v___x_3101_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3101_, 0, v___x_3099_);
lean_ctor_set_uint64(v___x_3101_, sizeof(void*)*1, v___x_3100_);
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3104_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3105_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3106_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3107_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3107_, 0, v___x_3101_);
lean_ctor_set(v___x_3107_, 1, v___x_3037_);
lean_ctor_set(v___x_3107_, 2, v___x_3104_);
lean_ctor_set(v___x_3107_, 3, v___x_3105_);
lean_ctor_set(v___x_3107_, 4, v___x_3106_);
lean_ctor_set(v___x_3107_, 5, v___x_3102_);
lean_ctor_set(v___x_3107_, 6, v___x_3106_);
lean_ctor_set_uint8(v___x_3107_, sizeof(void*)*7, v___x_3063_);
lean_ctor_set_uint8(v___x_3107_, sizeof(void*)*7 + 1, v___x_3063_);
lean_ctor_set_uint8(v___x_3107_, sizeof(void*)*7 + 2, v___x_3063_);
lean_ctor_set_uint8(v___x_3107_, sizeof(void*)*7 + 3, v___x_3058_);
v___x_3108_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3109_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3110_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3108_);
lean_ctor_set(v___x_3111_, 1, v___x_3109_);
lean_ctor_set(v___x_3111_, 2, v___x_3037_);
lean_ctor_set(v___x_3111_, 3, v___x_3103_);
lean_ctor_set(v___x_3111_, 4, v___x_3110_);
v___x_3112_ = lean_st_mk_ref(v___x_3111_);
v___x_3113_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3053_, v___x_3058_, v___x_3107_, v___x_3112_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3107_, 7);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3115_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v___x_3115_ = lean_st_ref_get(v___x_3112_);
lean_dec(v___x_3112_);
lean_dec(v___x_3115_);
v_a_3082_ = v_a_3114_;
goto v___jp_3081_;
}
else
{
lean_dec(v___x_3112_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3116_; 
v_a_3116_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3113_, 1);
v_a_3082_ = v_a_3116_;
goto v___jp_3081_;
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
v_a_3117_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3113_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3113_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
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
v___jp_3081_:
{
if (lean_obj_tag(v_a_3082_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_box(v___x_3063_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
else
{
lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3092_; 
v_isSharedCheck_3092_ = !lean_is_exclusive(v_a_3082_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; 
v_unused_3093_ = lean_ctor_get(v_a_3082_, 0);
lean_dec(v_unused_3093_);
v___x_3086_ = v_a_3082_;
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
else
{
lean_dec(v_a_3082_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = lean_box(v___x_3080_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set_tag(v___x_3086_, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3088_);
v___x_3090_ = v___x_3086_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
else
{
uint8_t v___x_3125_; uint8_t v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; uint64_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec(v_snd_3054_);
v___x_3125_ = 1;
v___x_3126_ = 0;
v___x_3127_ = 2;
v___x_3128_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3128_, 0, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3128_, 1, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3128_, 2, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3128_, 3, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3128_, 4, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3128_, 5, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 6, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 7, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3128_, 8, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 9, v___x_3125_);
lean_ctor_set_uint8(v___x_3128_, 10, v___x_3126_);
lean_ctor_set_uint8(v___x_3128_, 11, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 12, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 13, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 14, v___x_3127_);
lean_ctor_set_uint8(v___x_3128_, 15, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 16, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 17, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 18, v___x_3063_);
lean_ctor_set_uint8(v___x_3128_, 19, v_hasTrace_3045_);
v___x_3129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set_uint64(v___x_3130_, sizeof(void*)*1, v___x_3129_);
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3133_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3134_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3135_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3136_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3136_, 0, v___x_3130_);
lean_ctor_set(v___x_3136_, 1, v___x_3037_);
lean_ctor_set(v___x_3136_, 2, v___x_3133_);
lean_ctor_set(v___x_3136_, 3, v___x_3134_);
lean_ctor_set(v___x_3136_, 4, v___x_3135_);
lean_ctor_set(v___x_3136_, 5, v___x_3131_);
lean_ctor_set(v___x_3136_, 6, v___x_3135_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7 + 1, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7 + 2, v_hasTrace_3045_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7 + 3, v___x_3058_);
v___x_3137_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3138_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3139_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3137_);
lean_ctor_set(v___x_3140_, 1, v___x_3138_);
lean_ctor_set(v___x_3140_, 2, v___x_3037_);
lean_ctor_set(v___x_3140_, 3, v___x_3132_);
lean_ctor_set(v___x_3140_, 4, v___x_3139_);
v___x_3141_ = lean_st_mk_ref(v___x_3140_);
v___x_3142_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3053_, v___x_3136_, v___x_3141_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3136_, 7);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = lean_st_ref_get(v___x_3141_);
lean_dec(v___x_3141_);
lean_dec(v___x_3144_);
v_a_3065_ = v_a_3143_;
goto v___jp_3064_;
}
else
{
lean_dec(v___x_3141_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3145_; 
v_a_3145_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3142_, 1);
v_a_3065_ = v_a_3145_;
goto v___jp_3064_;
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_del_object(v___x_3051_);
v_a_3146_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3142_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3142_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
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
}
v___jp_3064_:
{
if (lean_obj_tag(v_a_3065_) == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3066_ = lean_box(v_hasTrace_3045_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3066_);
v___x_3068_ = v___x_3051_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
else
{
lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3077_; 
lean_del_object(v___x_3051_);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_a_3065_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v_a_3065_, 0);
lean_dec(v_unused_3078_);
v___x_3071_ = v_a_3065_;
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
else
{
lean_dec(v_a_3065_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_box(v___x_3063_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3073_);
v___x_3075_ = v___x_3071_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_dec(v___x_3048_);
lean_dec(v_name_3039_);
lean_dec(v___x_3037_);
v___x_3155_ = lean_box(v_hasTrace_3045_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3157_; lean_object* v___f_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v_a_3166_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v_a_3181_; uint8_t v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v_a_3189_; lean_object* v___y_3191_; lean_object* v___y_3192_; uint8_t v___y_3193_; uint8_t v___y_3194_; lean_object* v_a_3195_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v_a_3199_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v_a_3204_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v_a_3216_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v_a_3221_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3232_; lean_object* v___y_3233_; uint8_t v___y_3234_; lean_object* v_a_3235_; lean_object* v___y_3238_; lean_object* v___y_3239_; uint8_t v___y_3240_; uint8_t v___y_3241_; lean_object* v_a_3242_; 
v_inheritedTraceOptions_3157_ = lean_ctor_get(v_toCold_3043_, 11);
lean_inc(v_name_3039_);
v___f_3158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3158_, 0, v_name_3039_);
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3160_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__2___closed__1));
v___x_3161_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3157_, v_options_3044_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3371_ = l_Lean_trace_profiler;
v___x_3372_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3044_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v_env_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v___f_3158_);
lean_dec_ref(v___f_3038_);
v___x_3373_ = lean_st_ref_get(v___y_3041_);
v_env_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc_ref(v_env_3374_);
lean_dec(v___x_3373_);
lean_inc(v_name_3039_);
v___x_3375_ = l_Lean_Meta_declFromEqLikeName(v_env_3374_, v_name_3039_);
if (lean_obj_tag(v___x_3375_) == 1)
{
lean_object* v_val_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3481_; 
v_val_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3481_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_val_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3481_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_fst_3380_; lean_object* v_snd_3381_; lean_object* v___x_3382_; lean_object* v_env_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v_fst_3380_ = lean_ctor_get(v_val_3376_, 0);
lean_inc_n(v_fst_3380_, 2);
v_snd_3381_ = lean_ctor_get(v_val_3376_, 1);
lean_inc_n(v_snd_3381_, 2);
lean_dec(v_val_3376_);
v___x_3382_ = lean_st_ref_get(v___y_3041_);
v_env_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_ref(v_env_3383_);
lean_dec(v___x_3382_);
v___x_3384_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3383_, v_fst_3380_, v_snd_3381_);
v___x_3385_ = lean_name_eq(v_name_3039_, v___x_3384_);
lean_dec(v___x_3384_);
lean_dec(v_name_3039_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
lean_dec(v_snd_3381_);
lean_dec(v_fst_3380_);
lean_dec(v___x_3037_);
v___x_3386_ = lean_box(v___x_3372_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3386_);
v___x_3388_ = v___x_3378_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
else
{
uint8_t v___x_3390_; lean_object* v_a_3392_; 
lean_inc(v_snd_3381_);
v___x_3390_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3381_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3406_; uint8_t v___x_3407_; lean_object* v_a_3409_; 
lean_del_object(v___x_3378_);
v___x_3406_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3407_ = lean_string_dec_eq(v_snd_3381_, v___x_3406_);
lean_dec(v_snd_3381_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec(v_fst_3380_);
lean_dec(v___x_3037_);
v___x_3421_ = lean_box(v___x_3372_);
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
else
{
uint8_t v___x_3423_; uint8_t v___x_3424_; uint8_t v___x_3425_; lean_object* v___x_3426_; uint64_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3423_ = 1;
v___x_3424_ = 0;
v___x_3425_ = 2;
v___x_3426_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3426_, 0, v___x_3390_);
lean_ctor_set_uint8(v___x_3426_, 1, v___x_3390_);
lean_ctor_set_uint8(v___x_3426_, 2, v___x_3390_);
lean_ctor_set_uint8(v___x_3426_, 3, v___x_3390_);
lean_ctor_set_uint8(v___x_3426_, 4, v___x_3390_);
lean_ctor_set_uint8(v___x_3426_, 5, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 6, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 7, v___x_3390_);
lean_ctor_set_uint8(v___x_3426_, 8, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 9, v___x_3423_);
lean_ctor_set_uint8(v___x_3426_, 10, v___x_3424_);
lean_ctor_set_uint8(v___x_3426_, 11, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 12, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 13, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 14, v___x_3425_);
lean_ctor_set_uint8(v___x_3426_, 15, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 16, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 17, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 18, v___x_3407_);
lean_ctor_set_uint8(v___x_3426_, 19, v___x_3390_);
v___x_3427_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3426_);
v___x_3428_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set_uint64(v___x_3428_, sizeof(void*)*1, v___x_3427_);
v___x_3429_ = lean_unsigned_to_nat(0u);
v___x_3430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3431_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3432_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3433_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3434_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3434_, 0, v___x_3428_);
lean_ctor_set(v___x_3434_, 1, v___x_3037_);
lean_ctor_set(v___x_3434_, 2, v___x_3431_);
lean_ctor_set(v___x_3434_, 3, v___x_3432_);
lean_ctor_set(v___x_3434_, 4, v___x_3433_);
lean_ctor_set(v___x_3434_, 5, v___x_3429_);
lean_ctor_set(v___x_3434_, 6, v___x_3433_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*7, v___x_3390_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*7 + 1, v___x_3390_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*7 + 2, v___x_3390_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*7 + 3, v_hasTrace_3045_);
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3436_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3435_);
lean_ctor_set(v___x_3438_, 1, v___x_3436_);
lean_ctor_set(v___x_3438_, 2, v___x_3037_);
lean_ctor_set(v___x_3438_, 3, v___x_3430_);
lean_ctor_set(v___x_3438_, 4, v___x_3437_);
v___x_3439_ = lean_st_mk_ref(v___x_3438_);
v___x_3440_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3380_, v_hasTrace_3045_, v___x_3434_, v___x_3439_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3434_, 7);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3442_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3442_ = lean_st_ref_get(v___x_3439_);
lean_dec(v___x_3439_);
lean_dec(v___x_3442_);
v_a_3409_ = v_a_3441_;
goto v___jp_3408_;
}
else
{
lean_dec(v___x_3439_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3443_; 
v_a_3443_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3440_, 1);
v_a_3409_ = v_a_3443_;
goto v___jp_3408_;
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3444_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3440_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3440_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
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
v___jp_3408_:
{
if (lean_obj_tag(v_a_3409_) == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = lean_box(v___x_3390_);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
else
{
lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3419_; 
v_isSharedCheck_3419_ = !lean_is_exclusive(v_a_3409_);
if (v_isSharedCheck_3419_ == 0)
{
lean_object* v_unused_3420_; 
v_unused_3420_ = lean_ctor_get(v_a_3409_, 0);
lean_dec(v_unused_3420_);
v___x_3413_ = v_a_3409_;
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
else
{
lean_dec(v_a_3409_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_box(v___x_3407_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
else
{
uint8_t v___x_3452_; uint8_t v___x_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; uint64_t v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_dec(v_snd_3381_);
v___x_3452_ = 1;
v___x_3453_ = 0;
v___x_3454_ = 2;
v___x_3455_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3455_, 0, v___x_3372_);
lean_ctor_set_uint8(v___x_3455_, 1, v___x_3372_);
lean_ctor_set_uint8(v___x_3455_, 2, v___x_3372_);
lean_ctor_set_uint8(v___x_3455_, 3, v___x_3372_);
lean_ctor_set_uint8(v___x_3455_, 4, v___x_3372_);
lean_ctor_set_uint8(v___x_3455_, 5, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 6, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 7, v___x_3372_);
lean_ctor_set_uint8(v___x_3455_, 8, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 9, v___x_3452_);
lean_ctor_set_uint8(v___x_3455_, 10, v___x_3453_);
lean_ctor_set_uint8(v___x_3455_, 11, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 12, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 13, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 14, v___x_3454_);
lean_ctor_set_uint8(v___x_3455_, 15, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 16, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 17, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 18, v___x_3390_);
lean_ctor_set_uint8(v___x_3455_, 19, v___x_3372_);
v___x_3456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3455_);
v___x_3457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set_uint64(v___x_3457_, sizeof(void*)*1, v___x_3456_);
v___x_3458_ = lean_unsigned_to_nat(0u);
v___x_3459_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3460_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3461_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3462_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3463_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3463_, 0, v___x_3457_);
lean_ctor_set(v___x_3463_, 1, v___x_3037_);
lean_ctor_set(v___x_3463_, 2, v___x_3460_);
lean_ctor_set(v___x_3463_, 3, v___x_3461_);
lean_ctor_set(v___x_3463_, 4, v___x_3462_);
lean_ctor_set(v___x_3463_, 5, v___x_3458_);
lean_ctor_set(v___x_3463_, 6, v___x_3462_);
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*7, v___x_3372_);
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*7 + 1, v___x_3372_);
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*7 + 2, v___x_3372_);
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*7 + 3, v_hasTrace_3045_);
v___x_3464_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3466_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3464_);
lean_ctor_set(v___x_3467_, 1, v___x_3465_);
lean_ctor_set(v___x_3467_, 2, v___x_3037_);
lean_ctor_set(v___x_3467_, 3, v___x_3459_);
lean_ctor_set(v___x_3467_, 4, v___x_3466_);
v___x_3468_ = lean_st_mk_ref(v___x_3467_);
v___x_3469_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3380_, v___x_3463_, v___x_3468_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3463_, 7);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v___x_3471_ = lean_st_ref_get(v___x_3468_);
lean_dec(v___x_3468_);
lean_dec(v___x_3471_);
v_a_3392_ = v_a_3470_;
goto v___jp_3391_;
}
else
{
lean_dec(v___x_3468_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3472_; 
v_a_3472_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3469_, 1);
v_a_3392_ = v_a_3472_;
goto v___jp_3391_;
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_del_object(v___x_3378_);
v_a_3473_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3469_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3469_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
v___jp_3391_:
{
if (lean_obj_tag(v_a_3392_) == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3393_ = lean_box(v___x_3372_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3393_);
v___x_3395_ = v___x_3378_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
else
{
lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3404_; 
lean_del_object(v___x_3378_);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_a_3392_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v_a_3392_, 0);
lean_dec(v_unused_3405_);
v___x_3398_ = v_a_3392_;
v_isShared_3399_ = v_isSharedCheck_3404_;
goto v_resetjp_3397_;
}
else
{
lean_dec(v_a_3392_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3404_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3400_ = lean_box(v___x_3390_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3400_);
v___x_3402_ = v___x_3398_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v___x_3375_);
lean_dec(v_name_3039_);
lean_dec(v___x_3037_);
v___x_3482_ = lean_box(v___x_3372_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
}
else
{
goto v___jp_3243_;
}
}
else
{
goto v___jp_3243_;
}
v___jp_3163_:
{
lean_object* v___x_3167_; double v___x_3168_; double v___x_3169_; double v___x_3170_; double v___x_3171_; double v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3167_ = lean_io_mono_nanos_now();
v___x_3168_ = lean_float_of_nat(v___y_3165_);
v___x_3169_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3170_ = lean_float_div(v___x_3168_, v___x_3169_);
v___x_3171_ = lean_float_of_nat(v___x_3167_);
v___x_3172_ = lean_float_div(v___x_3171_, v___x_3169_);
v___x_3173_ = lean_box_float(v___x_3170_);
v___x_3174_ = lean_box_float(v___x_3172_);
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_a_3166_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3159_, v_hasTrace_3045_, v___x_3160_, v_options_3044_, v___x_3162_, v___y_3164_, v___f_3158_, v___x_3176_, v___y_3040_, v___y_3041_);
return v___x_3177_;
}
v___jp_3178_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(v_a_3181_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
v___y_3164_ = v___y_3179_;
v___y_3165_ = v___y_3180_;
v_a_3166_ = v___x_3183_;
goto v___jp_3163_;
}
v___jp_3184_:
{
if (lean_obj_tag(v_a_3189_) == 0)
{
v___y_3179_ = v___y_3186_;
v___y_3180_ = v___y_3187_;
v_a_3181_ = v___y_3188_;
goto v___jp_3178_;
}
else
{
lean_dec_ref_known(v_a_3189_, 1);
v___y_3179_ = v___y_3186_;
v___y_3180_ = v___y_3187_;
v_a_3181_ = v___y_3185_;
goto v___jp_3178_;
}
}
v___jp_3190_:
{
if (lean_obj_tag(v_a_3195_) == 0)
{
v___y_3179_ = v___y_3191_;
v___y_3180_ = v___y_3192_;
v_a_3181_ = v___y_3194_;
goto v___jp_3178_;
}
else
{
lean_dec_ref_known(v_a_3195_, 1);
v___y_3179_ = v___y_3191_;
v___y_3180_ = v___y_3192_;
v_a_3181_ = v___y_3193_;
goto v___jp_3178_;
}
}
v___jp_3196_:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_a_3199_);
v___y_3164_ = v___y_3197_;
v___y_3165_ = v___y_3198_;
v_a_3166_ = v___x_3200_;
goto v___jp_3163_;
}
v___jp_3201_:
{
lean_object* v___x_3205_; double v___x_3206_; double v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3205_ = lean_io_get_num_heartbeats();
v___x_3206_ = lean_float_of_nat(v___y_3203_);
v___x_3207_ = lean_float_of_nat(v___x_3205_);
v___x_3208_ = lean_box_float(v___x_3206_);
v___x_3209_ = lean_box_float(v___x_3207_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3208_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_a_3204_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3159_, v_hasTrace_3045_, v___x_3160_, v_options_3044_, v___x_3162_, v___y_3202_, v___f_3158_, v___x_3211_, v___y_3040_, v___y_3041_);
return v___x_3212_;
}
v___jp_3213_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v_a_3216_);
v___y_3202_ = v___y_3214_;
v___y_3203_ = v___y_3215_;
v_a_3204_ = v___x_3217_;
goto v___jp_3201_;
}
v___jp_3218_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_box(v_a_3221_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v___y_3202_ = v___y_3219_;
v___y_3203_ = v___y_3220_;
v_a_3204_ = v___x_3223_;
goto v___jp_3201_;
}
v___jp_3224_:
{
if (lean_obj_tag(v___y_3227_) == 0)
{
lean_object* v_a_3228_; uint8_t v___x_3229_; 
v_a_3228_ = lean_ctor_get(v___y_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___y_3227_, 1);
v___x_3229_ = lean_unbox(v_a_3228_);
lean_dec(v_a_3228_);
v___y_3219_ = v___y_3225_;
v___y_3220_ = v___y_3226_;
v_a_3221_ = v___x_3229_;
goto v___jp_3218_;
}
else
{
lean_object* v_a_3230_; 
v_a_3230_ = lean_ctor_get(v___y_3227_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___y_3227_, 1);
v___y_3214_ = v___y_3225_;
v___y_3215_ = v___y_3226_;
v_a_3216_ = v_a_3230_;
goto v___jp_3213_;
}
}
v___jp_3231_:
{
if (lean_obj_tag(v_a_3235_) == 0)
{
uint8_t v___x_3236_; 
v___x_3236_ = 0;
v___y_3219_ = v___y_3232_;
v___y_3220_ = v___y_3233_;
v_a_3221_ = v___x_3236_;
goto v___jp_3218_;
}
else
{
lean_dec_ref_known(v_a_3235_, 1);
v___y_3219_ = v___y_3232_;
v___y_3220_ = v___y_3233_;
v_a_3221_ = v___y_3234_;
goto v___jp_3218_;
}
}
v___jp_3237_:
{
if (lean_obj_tag(v_a_3242_) == 0)
{
v___y_3219_ = v___y_3238_;
v___y_3220_ = v___y_3239_;
v_a_3221_ = v___y_3241_;
goto v___jp_3218_;
}
else
{
lean_dec_ref_known(v_a_3242_, 1);
v___y_3219_ = v___y_3238_;
v___y_3220_ = v___y_3239_;
v_a_3221_ = v___y_3240_;
goto v___jp_3218_;
}
}
v___jp_3243_:
{
lean_object* v___x_3244_; lean_object* v_a_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3244_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3041_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref(v___x_3244_);
v___x_3246_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3247_ = l_Lean_Option_get___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v_options_3044_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v_env_3250_; lean_object* v___x_3251_; 
lean_dec_ref(v___f_3038_);
v___x_3248_ = lean_io_mono_nanos_now();
v___x_3249_ = lean_st_ref_get(v___y_3041_);
v_env_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc_ref(v_env_3250_);
lean_dec(v___x_3249_);
lean_inc(v_name_3039_);
v___x_3251_ = l_Lean_Meta_declFromEqLikeName(v_env_3250_, v_name_3039_);
if (lean_obj_tag(v___x_3251_) == 1)
{
lean_object* v_val_3252_; lean_object* v_fst_3253_; lean_object* v_snd_3254_; lean_object* v___x_3255_; lean_object* v_env_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_val_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_val_3252_);
lean_dec_ref_known(v___x_3251_, 1);
v_fst_3253_ = lean_ctor_get(v_val_3252_, 0);
lean_inc_n(v_fst_3253_, 2);
v_snd_3254_ = lean_ctor_get(v_val_3252_, 1);
lean_inc_n(v_snd_3254_, 2);
lean_dec(v_val_3252_);
v___x_3255_ = lean_st_ref_get(v___y_3041_);
v_env_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc_ref(v_env_3256_);
lean_dec(v___x_3255_);
v___x_3257_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3256_, v_fst_3253_, v_snd_3254_);
v___x_3258_ = lean_name_eq(v_name_3039_, v___x_3257_);
lean_dec(v___x_3257_);
lean_dec(v_name_3039_);
if (v___x_3258_ == 0)
{
lean_dec(v_snd_3254_);
lean_dec(v_fst_3253_);
lean_dec(v___x_3037_);
v___y_3179_ = v_a_3245_;
v___y_3180_ = v___x_3248_;
v_a_3181_ = v___x_3247_;
goto v___jp_3178_;
}
else
{
uint8_t v___x_3259_; 
lean_inc(v_snd_3254_);
v___x_3259_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3254_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3261_ = lean_string_dec_eq(v_snd_3254_, v___x_3260_);
lean_dec(v_snd_3254_);
if (v___x_3261_ == 0)
{
lean_dec(v_fst_3253_);
lean_dec(v___x_3037_);
v___y_3179_ = v_a_3245_;
v___y_3180_ = v___x_3248_;
v_a_3181_ = v___x_3247_;
goto v___jp_3178_;
}
else
{
uint8_t v___x_3262_; uint8_t v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; uint64_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3262_ = 1;
v___x_3263_ = 0;
v___x_3264_ = 2;
v___x_3265_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3265_, 0, v___x_3259_);
lean_ctor_set_uint8(v___x_3265_, 1, v___x_3259_);
lean_ctor_set_uint8(v___x_3265_, 2, v___x_3259_);
lean_ctor_set_uint8(v___x_3265_, 3, v___x_3259_);
lean_ctor_set_uint8(v___x_3265_, 4, v___x_3259_);
lean_ctor_set_uint8(v___x_3265_, 5, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 6, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 7, v___x_3259_);
lean_ctor_set_uint8(v___x_3265_, 8, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 9, v___x_3262_);
lean_ctor_set_uint8(v___x_3265_, 10, v___x_3263_);
lean_ctor_set_uint8(v___x_3265_, 11, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 12, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 13, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 14, v___x_3264_);
lean_ctor_set_uint8(v___x_3265_, 15, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 16, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 17, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 18, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, 19, v___x_3259_);
v___x_3266_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3265_);
v___x_3267_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set_uint64(v___x_3267_, sizeof(void*)*1, v___x_3266_);
v___x_3268_ = lean_unsigned_to_nat(0u);
v___x_3269_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3270_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3271_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3272_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3273_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3273_, 0, v___x_3267_);
lean_ctor_set(v___x_3273_, 1, v___x_3037_);
lean_ctor_set(v___x_3273_, 2, v___x_3270_);
lean_ctor_set(v___x_3273_, 3, v___x_3271_);
lean_ctor_set(v___x_3273_, 4, v___x_3272_);
lean_ctor_set(v___x_3273_, 5, v___x_3268_);
lean_ctor_set(v___x_3273_, 6, v___x_3272_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*7, v___x_3259_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*7 + 1, v___x_3259_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*7 + 2, v___x_3259_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*7 + 3, v_hasTrace_3045_);
v___x_3274_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3275_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3276_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3274_);
lean_ctor_set(v___x_3277_, 1, v___x_3275_);
lean_ctor_set(v___x_3277_, 2, v___x_3037_);
lean_ctor_set(v___x_3277_, 3, v___x_3269_);
lean_ctor_set(v___x_3277_, 4, v___x_3276_);
v___x_3278_ = lean_st_mk_ref(v___x_3277_);
v___x_3279_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3253_, v_hasTrace_3045_, v___x_3273_, v___x_3278_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3273_, 7);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3281_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v___x_3281_ = lean_st_ref_get(v___x_3278_);
lean_dec(v___x_3278_);
lean_dec(v___x_3281_);
v___y_3185_ = v___x_3261_;
v___y_3186_ = v_a_3245_;
v___y_3187_ = v___x_3248_;
v___y_3188_ = v___x_3259_;
v_a_3189_ = v_a_3280_;
goto v___jp_3184_;
}
else
{
lean_dec(v___x_3278_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3282_; 
v_a_3282_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3279_, 1);
v___y_3185_ = v___x_3261_;
v___y_3186_ = v_a_3245_;
v___y_3187_ = v___x_3248_;
v___y_3188_ = v___x_3259_;
v_a_3189_ = v_a_3282_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3283_; 
v_a_3283_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3279_, 1);
v___y_3197_ = v_a_3245_;
v___y_3198_ = v___x_3248_;
v_a_3199_ = v_a_3283_;
goto v___jp_3196_;
}
}
}
}
else
{
uint8_t v___x_3284_; uint8_t v___x_3285_; uint8_t v___x_3286_; lean_object* v___x_3287_; uint64_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_snd_3254_);
v___x_3284_ = 1;
v___x_3285_ = 0;
v___x_3286_ = 2;
v___x_3287_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3287_, 0, v___x_3247_);
lean_ctor_set_uint8(v___x_3287_, 1, v___x_3247_);
lean_ctor_set_uint8(v___x_3287_, 2, v___x_3247_);
lean_ctor_set_uint8(v___x_3287_, 3, v___x_3247_);
lean_ctor_set_uint8(v___x_3287_, 4, v___x_3247_);
lean_ctor_set_uint8(v___x_3287_, 5, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 6, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 7, v___x_3247_);
lean_ctor_set_uint8(v___x_3287_, 8, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 9, v___x_3284_);
lean_ctor_set_uint8(v___x_3287_, 10, v___x_3285_);
lean_ctor_set_uint8(v___x_3287_, 11, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 12, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 13, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 14, v___x_3286_);
lean_ctor_set_uint8(v___x_3287_, 15, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 16, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 17, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 18, v___x_3259_);
lean_ctor_set_uint8(v___x_3287_, 19, v___x_3247_);
v___x_3288_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set_uint64(v___x_3289_, sizeof(void*)*1, v___x_3288_);
v___x_3290_ = lean_unsigned_to_nat(0u);
v___x_3291_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3292_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3293_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3294_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3295_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3295_, 0, v___x_3289_);
lean_ctor_set(v___x_3295_, 1, v___x_3037_);
lean_ctor_set(v___x_3295_, 2, v___x_3292_);
lean_ctor_set(v___x_3295_, 3, v___x_3293_);
lean_ctor_set(v___x_3295_, 4, v___x_3294_);
lean_ctor_set(v___x_3295_, 5, v___x_3290_);
lean_ctor_set(v___x_3295_, 6, v___x_3294_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*7, v___x_3247_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*7 + 1, v___x_3247_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*7 + 2, v___x_3247_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*7 + 3, v_hasTrace_3045_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3298_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3296_);
lean_ctor_set(v___x_3299_, 1, v___x_3297_);
lean_ctor_set(v___x_3299_, 2, v___x_3037_);
lean_ctor_set(v___x_3299_, 3, v___x_3291_);
lean_ctor_set(v___x_3299_, 4, v___x_3298_);
v___x_3300_ = lean_st_mk_ref(v___x_3299_);
v___x_3301_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3253_, v___x_3295_, v___x_3300_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3295_, 7);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = lean_st_ref_get(v___x_3300_);
lean_dec(v___x_3300_);
lean_dec(v___x_3303_);
v___y_3191_ = v_a_3245_;
v___y_3192_ = v___x_3248_;
v___y_3193_ = v___x_3259_;
v___y_3194_ = v___x_3247_;
v_a_3195_ = v_a_3302_;
goto v___jp_3190_;
}
else
{
lean_dec(v___x_3300_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3304_; 
v_a_3304_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3301_, 1);
v___y_3191_ = v_a_3245_;
v___y_3192_ = v___x_3248_;
v___y_3193_ = v___x_3259_;
v___y_3194_ = v___x_3247_;
v_a_3195_ = v_a_3304_;
goto v___jp_3190_;
}
else
{
lean_object* v_a_3305_; 
v_a_3305_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3301_, 1);
v___y_3197_ = v_a_3245_;
v___y_3198_ = v___x_3248_;
v_a_3199_ = v_a_3305_;
goto v___jp_3196_;
}
}
}
}
}
else
{
lean_dec(v___x_3251_);
lean_dec(v_name_3039_);
lean_dec(v___x_3037_);
v___y_3179_ = v_a_3245_;
v___y_3180_ = v___x_3248_;
v_a_3181_ = v___x_3247_;
goto v___jp_3178_;
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v_env_3308_; lean_object* v___x_3309_; 
v___x_3306_ = lean_io_get_num_heartbeats();
v___x_3307_ = lean_st_ref_get(v___y_3041_);
v_env_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc_ref(v_env_3308_);
lean_dec(v___x_3307_);
lean_inc(v_name_3039_);
v___x_3309_ = l_Lean_Meta_declFromEqLikeName(v_env_3308_, v_name_3039_);
if (lean_obj_tag(v___x_3309_) == 1)
{
lean_object* v_val_3310_; lean_object* v_fst_3311_; lean_object* v_snd_3312_; lean_object* v___x_3313_; lean_object* v_env_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v_val_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_val_3310_);
lean_dec_ref_known(v___x_3309_, 1);
v_fst_3311_ = lean_ctor_get(v_val_3310_, 0);
lean_inc_n(v_fst_3311_, 2);
v_snd_3312_ = lean_ctor_get(v_val_3310_, 1);
lean_inc_n(v_snd_3312_, 2);
lean_dec(v_val_3310_);
v___x_3313_ = lean_st_ref_get(v___y_3041_);
v_env_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc_ref(v_env_3314_);
lean_dec(v___x_3313_);
v___x_3315_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3314_, v_fst_3311_, v_snd_3312_);
v___x_3316_ = lean_name_eq(v_name_3039_, v___x_3315_);
lean_dec(v___x_3315_);
lean_dec(v_name_3039_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec(v_snd_3312_);
lean_dec(v_fst_3311_);
lean_dec(v___x_3037_);
v___x_3317_ = lean_box(0);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
v___x_3318_ = lean_apply_4(v___f_3038_, v___x_3317_, v___y_3040_, v___y_3041_, lean_box(0));
v___y_3225_ = v_a_3245_;
v___y_3226_ = v___x_3306_;
v___y_3227_ = v___x_3318_;
goto v___jp_3224_;
}
else
{
uint8_t v___x_3319_; 
lean_inc(v_snd_3312_);
v___x_3319_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3312_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3321_ = lean_string_dec_eq(v_snd_3312_, v___x_3320_);
lean_dec(v_snd_3312_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec(v_fst_3311_);
lean_dec(v___x_3037_);
v___x_3322_ = lean_box(0);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
v___x_3323_ = lean_apply_4(v___f_3038_, v___x_3322_, v___y_3040_, v___y_3041_, lean_box(0));
v___y_3225_ = v_a_3245_;
v___y_3226_ = v___x_3306_;
v___y_3227_ = v___x_3323_;
goto v___jp_3224_;
}
else
{
uint8_t v___x_3324_; uint8_t v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; uint64_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec_ref(v___f_3038_);
v___x_3324_ = 1;
v___x_3325_ = 0;
v___x_3326_ = 2;
v___x_3327_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3327_, 0, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 1, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 2, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 3, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 4, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 5, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 6, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 7, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 8, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 9, v___x_3324_);
lean_ctor_set_uint8(v___x_3327_, 10, v___x_3325_);
lean_ctor_set_uint8(v___x_3327_, 11, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 12, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 13, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 14, v___x_3326_);
lean_ctor_set_uint8(v___x_3327_, 15, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 16, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 17, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 18, v___x_3321_);
lean_ctor_set_uint8(v___x_3327_, 19, v___x_3319_);
v___x_3328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3327_);
v___x_3329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set_uint64(v___x_3329_, sizeof(void*)*1, v___x_3328_);
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3332_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3334_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3335_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3335_, 0, v___x_3329_);
lean_ctor_set(v___x_3335_, 1, v___x_3037_);
lean_ctor_set(v___x_3335_, 2, v___x_3332_);
lean_ctor_set(v___x_3335_, 3, v___x_3333_);
lean_ctor_set(v___x_3335_, 4, v___x_3334_);
lean_ctor_set(v___x_3335_, 5, v___x_3330_);
lean_ctor_set(v___x_3335_, 6, v___x_3334_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7, v___x_3319_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7 + 1, v___x_3319_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7 + 2, v___x_3319_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7 + 3, v___x_3247_);
v___x_3336_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3337_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3338_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3336_);
lean_ctor_set(v___x_3339_, 1, v___x_3337_);
lean_ctor_set(v___x_3339_, 2, v___x_3037_);
lean_ctor_set(v___x_3339_, 3, v___x_3331_);
lean_ctor_set(v___x_3339_, 4, v___x_3338_);
v___x_3340_ = lean_st_mk_ref(v___x_3339_);
v___x_3341_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3311_, v___x_3247_, v___x_3335_, v___x_3340_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3335_, 7);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = lean_st_ref_get(v___x_3340_);
lean_dec(v___x_3340_);
lean_dec(v___x_3343_);
v___y_3238_ = v_a_3245_;
v___y_3239_ = v___x_3306_;
v___y_3240_ = v___x_3321_;
v___y_3241_ = v___x_3319_;
v_a_3242_ = v_a_3342_;
goto v___jp_3237_;
}
else
{
lean_dec(v___x_3340_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3344_; 
v_a_3344_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3341_, 1);
v___y_3238_ = v_a_3245_;
v___y_3239_ = v___x_3306_;
v___y_3240_ = v___x_3321_;
v___y_3241_ = v___x_3319_;
v_a_3242_ = v_a_3344_;
goto v___jp_3237_;
}
else
{
lean_object* v_a_3345_; 
v_a_3345_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3341_, 1);
v___y_3214_ = v_a_3245_;
v___y_3215_ = v___x_3306_;
v_a_3216_ = v_a_3345_;
goto v___jp_3213_;
}
}
}
}
else
{
uint8_t v___x_3346_; uint8_t v___x_3347_; uint8_t v___x_3348_; uint8_t v___x_3349_; lean_object* v___x_3350_; uint64_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v_snd_3312_);
lean_dec_ref(v___f_3038_);
v___x_3346_ = 0;
v___x_3347_ = 1;
v___x_3348_ = 0;
v___x_3349_ = 2;
v___x_3350_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3350_, 0, v___x_3346_);
lean_ctor_set_uint8(v___x_3350_, 1, v___x_3346_);
lean_ctor_set_uint8(v___x_3350_, 2, v___x_3346_);
lean_ctor_set_uint8(v___x_3350_, 3, v___x_3346_);
lean_ctor_set_uint8(v___x_3350_, 4, v___x_3346_);
lean_ctor_set_uint8(v___x_3350_, 5, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 6, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 7, v___x_3346_);
lean_ctor_set_uint8(v___x_3350_, 8, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 9, v___x_3347_);
lean_ctor_set_uint8(v___x_3350_, 10, v___x_3348_);
lean_ctor_set_uint8(v___x_3350_, 11, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 12, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 13, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 14, v___x_3349_);
lean_ctor_set_uint8(v___x_3350_, 15, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 16, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 17, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 18, v___x_3319_);
lean_ctor_set_uint8(v___x_3350_, 19, v___x_3346_);
v___x_3351_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3350_);
v___x_3352_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set_uint64(v___x_3352_, sizeof(void*)*1, v___x_3351_);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3355_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3356_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3357_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3358_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3358_, 0, v___x_3352_);
lean_ctor_set(v___x_3358_, 1, v___x_3037_);
lean_ctor_set(v___x_3358_, 2, v___x_3355_);
lean_ctor_set(v___x_3358_, 3, v___x_3356_);
lean_ctor_set(v___x_3358_, 4, v___x_3357_);
lean_ctor_set(v___x_3358_, 5, v___x_3353_);
lean_ctor_set(v___x_3358_, 6, v___x_3357_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*7, v___x_3346_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*7 + 1, v___x_3346_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*7 + 2, v___x_3346_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*7 + 3, v___x_3247_);
v___x_3359_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3360_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3361_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3359_);
lean_ctor_set(v___x_3362_, 1, v___x_3360_);
lean_ctor_set(v___x_3362_, 2, v___x_3037_);
lean_ctor_set(v___x_3362_, 3, v___x_3354_);
lean_ctor_set(v___x_3362_, 4, v___x_3361_);
v___x_3363_ = lean_st_mk_ref(v___x_3362_);
v___x_3364_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3311_, v___x_3358_, v___x_3363_, v___y_3040_, v___y_3041_);
lean_dec_ref_known(v___x_3358_, 7);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = lean_st_ref_get(v___x_3363_);
lean_dec(v___x_3363_);
lean_dec(v___x_3366_);
v___y_3232_ = v_a_3245_;
v___y_3233_ = v___x_3306_;
v___y_3234_ = v___x_3319_;
v_a_3235_ = v_a_3365_;
goto v___jp_3231_;
}
else
{
lean_dec(v___x_3363_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3367_; 
v_a_3367_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3364_, 1);
v___y_3232_ = v_a_3245_;
v___y_3233_ = v___x_3306_;
v___y_3234_ = v___x_3319_;
v_a_3235_ = v_a_3367_;
goto v___jp_3231_;
}
else
{
lean_object* v_a_3368_; 
v_a_3368_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3364_, 1);
v___y_3214_ = v_a_3245_;
v___y_3215_ = v___x_3306_;
v_a_3216_ = v_a_3368_;
goto v___jp_3213_;
}
}
}
}
}
else
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec(v___x_3309_);
lean_dec(v_name_3039_);
lean_dec(v___x_3037_);
v___x_3369_ = lean_box(0);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
v___x_3370_ = lean_apply_4(v___f_3038_, v___x_3369_, v___y_3040_, v___y_3041_, lean_box(0));
v___y_3225_ = v_a_3245_;
v___y_3226_ = v___x_3306_;
v___y_3227_ = v___x_3370_;
goto v___jp_3224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3484_, lean_object* v___f_3485_, lean_object* v_name_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3484_, v___f_3485_, v_name_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_unsigned_to_nat(3137104340u);
v___x_3536_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3537_ = l_Lean_Name_num___override(v___x_3536_, v___x_3535_);
return v___x_3537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3540_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3541_ = l_Lean_Name_str___override(v___x_3540_, v___x_3539_);
return v___x_3541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3544_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3545_ = l_Lean_Name_str___override(v___x_3544_, v___x_3543_);
return v___x_3545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = lean_unsigned_to_nat(2u);
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3548_ = l_Lean_Name_num___override(v___x_3547_, v___x_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3550_; lean_object* v___x_3551_; 
v___f_3550_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3551_ = l_Lean_registerReservedNameAction(v___f_3550_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec_ref_known(v___x_3551_, 1);
v___x_3552_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3553_ = 0;
v___x_3554_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3555_ = l_Lean_registerTraceClass(v___x_3552_, v___x_3553_, v___x_3554_);
return v___x_3555_;
}
else
{
return v___x_3551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3558_, lean_object* v_x_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3559_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3564_, lean_object* v_x_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3564_, v_x_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3569_;
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
