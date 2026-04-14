// Lean compiler output
// Module: Lean.Meta.WrapInstance
// Imports: public import Lean.Meta.Closure public import Lean.Meta.SynthInstance public import Lean.Meta.CtorRecognizer public import Lean.Meta.AppBuilder import Lean.Structure
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
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureParentInfo(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getFieldInfo_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferInstanceAs"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "wrap"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "wrap instance bodies in `inferInstanceAs` and the default `deriving` handler"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reuseSubInstances"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(10, 196, 243, 125, 230, 240, 101, 207)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "when recursing into sub-instances, reuse existing instances for the target type instead of re-wrapping them, which can be important to avoid non-defeq instance diamonds"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 247, 150, 241, 101, 127, 32, 183)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 83, 182, 188, 30, 204, 110, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "wrap non-reducible instances in auxiliary definitions to fix their types"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 217, 132, 111, 195, 190, 14, 255)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 208, 243, 158, 154, 215, 49, 58)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "wrap data fields in auxiliary definitions to fix their types"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(59, 4, 237, 30, 122, 190, 35, 247)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_data;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wrapInstance"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 191, 244, 235, 250, 100, 130, 195)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "WrapInstance"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 173, 45, 246, 47, 55, 243, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(185, 135, 228, 210, 15, 68, 162, 204)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 3, 219, 249, 198, 148, 9, 129)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 244, 76, 43, 236, 107, 113, 110)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 218, 192, 96, 244, 90, 226, 106)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 37, 133, 70, 202, 123, 99, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(201, 48, 88, 11, 50, 139, 104, 61)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 200, 58, 34, 117, 240, 39, 228)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 33, 3, 130, 142, 149, 29, 62)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "no such field "};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "could not reduce type `"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "parent type depends on instance fields"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "self"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 226, 111, 209, 39, 160, 197, 219)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_wrapInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "error when attempting to reuse existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "using projection of existing instance `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "did not find existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_wrapInstance___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "did not reduce to constructor application, returning/wrapping as is: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found inherited field `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` from parent `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "using existing instance "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof field "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " does not have expected type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " but "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = ", wrapping in auxiliary theorem: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "wrapInstance: incorrect number of arguments for constructor application `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "wrapInstance: `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not unify with the conclusion of `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_wrapInstance___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "class is "};
static const lean_object* l_Lean_Meta_wrapInstance___closed__2 = (const lean_object*)&l_Lean_Meta_wrapInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_));
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_));
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_));
v___x_85_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_82_, v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_));
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_));
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_));
v___x_111_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_();
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_));
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_));
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_));
v___x_137_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_134_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4____boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_();
return v_res_139_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_unsigned_to_nat(3246864463u);
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_186_ = l_Lean_Name_num___override(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_190_ = l_Lean_Name_str___override(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_193_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_194_ = l_Lean_Name_str___override(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_197_ = l_Lean_Name_num___override(v___x_196_, v___x_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_200_ = 0;
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_202_ = l_Lean_registerTraceClass(v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2____boxed(lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; lean_object* v_env_212_; lean_object* v___x_213_; lean_object* v_mctx_214_; lean_object* v_lctx_215_; lean_object* v_options_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_211_ = lean_st_ref_get(v___y_209_);
v_env_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_env_212_);
lean_dec(v___x_211_);
v___x_213_ = lean_st_ref_get(v___y_207_);
v_mctx_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc_ref(v_mctx_214_);
lean_dec(v___x_213_);
v_lctx_215_ = lean_ctor_get(v___y_206_, 2);
v_options_216_ = lean_ctor_get(v___y_208_, 2);
lean_inc_ref(v_options_216_);
lean_inc_ref(v_lctx_215_);
v___x_217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_217_, 0, v_env_212_);
lean_ctor_set(v___x_217_, 1, v_mctx_214_);
lean_ctor_set(v___x_217_, 2, v_lctx_215_);
lean_ctor_set(v___x_217_, 3, v_options_216_);
v___x_218_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_msgData_205_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1___boxed(lean_object* v_msgData_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msgData_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_ref_233_ = lean_ctor_get(v___y_230_, 5);
v___x_234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
lean_inc(v_ref_233_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_233_);
lean_ctor_set(v___x_239_, 1, v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg___boxed(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(lean_object* v_structName_260_, lean_object* v_field_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_env_268_; lean_object* v___x_269_; lean_object* v___x_270_; size_t v_sz_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_st_ref_get(v_a_265_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref_n(v_env_268_, 3);
lean_dec(v___x_267_);
lean_inc(v_structName_260_);
v___x_269_ = l_Lean_getStructureParentInfo(v_env_268_, v_structName_260_);
v___x_270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0));
v_sz_271_ = lean_array_size(v___x_269_);
v___x_272_ = ((size_t)0ULL);
lean_inc(v_field_261_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(v_env_268_, v_field_261_, v___x_269_, v_sz_271_, v___x_272_, v___x_270_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
lean_dec_ref(v___x_269_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_304_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_304_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_304_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_304_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_fst_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_302_; 
v_fst_278_ = lean_ctor_get(v_a_274_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_a_274_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v_a_274_, 1);
lean_dec(v_unused_303_);
v___x_280_ = v_a_274_;
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_fst_278_);
lean_dec(v_a_274_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
if (lean_obj_tag(v_fst_278_) == 0)
{
lean_object* v___x_282_; 
lean_inc(v_field_261_);
lean_inc(v_structName_260_);
v___x_282_ = l_Lean_getFieldInfo_x3f(v_env_268_, v_structName_260_, v_field_261_);
if (lean_obj_tag(v___x_282_) == 1)
{
lean_object* v_val_283_; lean_object* v___x_285_; 
lean_dec(v_field_261_);
v_val_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_val_283_);
lean_dec_ref(v___x_282_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v_val_283_);
lean_ctor_set(v___x_280_, 0, v_structName_260_);
v___x_285_ = v___x_280_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_structName_260_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_val_283_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_285_);
v___x_287_ = v___x_276_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v___x_282_);
lean_del_object(v___x_280_);
lean_del_object(v___x_276_);
v___x_290_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1);
v___x_291_ = l_Lean_MessageData_ofName(v_field_261_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_MessageData_ofName(v_structName_260_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_296_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_297_;
}
}
else
{
lean_object* v_val_298_; lean_object* v___x_300_; 
lean_del_object(v___x_280_);
lean_dec_ref(v_env_268_);
lean_dec(v_field_261_);
lean_dec(v_structName_260_);
v_val_298_ = lean_ctor_get(v_fst_278_, 0);
lean_inc(v_val_298_);
lean_dec_ref(v_fst_278_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_val_298_);
v___x_300_ = v___x_276_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_val_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v_env_268_);
lean_dec(v_field_261_);
lean_dec(v_structName_260_);
v_a_305_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_273_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_273_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(lean_object* v___x_313_, lean_object* v_field_314_, lean_object* v_as_315_, size_t v_sz_316_, size_t v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_lt(v_i_317_, v_sz_316_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec(v_field_314_);
lean_dec_ref(v___x_313_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_b_318_);
return v___x_325_;
}
else
{
lean_object* v_a_326_; lean_object* v_structName_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_b_318_);
v_a_326_ = lean_array_uget_borrowed(v_as_315_, v_i_317_);
v_structName_327_ = lean_ctor_get(v_a_326_, 0);
v___x_328_ = lean_box(0);
lean_inc(v_structName_327_);
lean_inc_ref(v___x_313_);
v___x_329_ = l_Lean_findField_x3f(v___x_313_, v_structName_327_, v_field_314_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; 
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0));
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_317_, v___x_331_);
v_i_317_ = v___x_332_;
v_b_318_ = v___x_330_;
goto _start;
}
else
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v___x_313_);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_329_, 0);
lean_dec(v_unused_359_);
v___x_335_ = v___x_329_;
v_isShared_336_ = v_isSharedCheck_358_;
goto v_resetjp_334_;
}
else
{
lean_dec(v___x_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_358_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; 
lean_inc(v_structName_327_);
v___x_337_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_structName_327_, v_field_314_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_349_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_349_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v_a_338_);
v___x_343_ = v___x_335_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_348_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_328_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_del_object(v___x_335_);
v_a_350_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_337_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___boxed(lean_object* v___x_360_, lean_object* v_field_361_, lean_object* v_as_362_, lean_object* v_sz_363_, lean_object* v_i_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_363_);
lean_dec(v_sz_363_);
v_i_boxed_372_ = lean_unbox_usize(v_i_364_);
lean_dec(v_i_364_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(v___x_360_, v_field_361_, v_as_362_, v_sz_boxed_371_, v_i_boxed_372_, v_b_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec_ref(v_as_362_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___boxed(lean_object* v_structName_374_, lean_object* v_field_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_structName_374_, v_field_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___boxed(lean_object* v_00_u03b1_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(v_00_u03b1_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_398_; double v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_float_of_nat(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(lean_object* v_cls_405_, lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_458_; 
v_ref_412_ = lean_ctor_get(v___y_409_, 5);
v___x_413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_458_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_458_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_458_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_traceState_419_; lean_object* v_env_420_; lean_object* v_nextMacroScope_421_; lean_object* v_ngen_422_; lean_object* v_auxDeclNGen_423_; lean_object* v_cache_424_; lean_object* v_messages_425_; lean_object* v_infoState_426_; lean_object* v_snapshotTasks_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_457_; 
v___x_418_ = lean_st_ref_take(v___y_410_);
v_traceState_419_ = lean_ctor_get(v___x_418_, 4);
v_env_420_ = lean_ctor_get(v___x_418_, 0);
v_nextMacroScope_421_ = lean_ctor_get(v___x_418_, 1);
v_ngen_422_ = lean_ctor_get(v___x_418_, 2);
v_auxDeclNGen_423_ = lean_ctor_get(v___x_418_, 3);
v_cache_424_ = lean_ctor_get(v___x_418_, 5);
v_messages_425_ = lean_ctor_get(v___x_418_, 6);
v_infoState_426_ = lean_ctor_get(v___x_418_, 7);
v_snapshotTasks_427_ = lean_ctor_get(v___x_418_, 8);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_457_ == 0)
{
v___x_429_ = v___x_418_;
v_isShared_430_ = v_isSharedCheck_457_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snapshotTasks_427_);
lean_inc(v_infoState_426_);
lean_inc(v_messages_425_);
lean_inc(v_cache_424_);
lean_inc(v_traceState_419_);
lean_inc(v_auxDeclNGen_423_);
lean_inc(v_ngen_422_);
lean_inc(v_nextMacroScope_421_);
lean_inc(v_env_420_);
lean_dec(v___x_418_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_457_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint64_t v_tid_431_; lean_object* v_traces_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_456_; 
v_tid_431_ = lean_ctor_get_uint64(v_traceState_419_, sizeof(void*)*1);
v_traces_432_ = lean_ctor_get(v_traceState_419_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_traceState_419_);
if (v_isSharedCheck_456_ == 0)
{
v___x_434_ = v_traceState_419_;
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_traces_432_);
lean_dec(v_traceState_419_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; double v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
v___x_438_ = 0;
v___x_439_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_440_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_440_, 0, v_cls_405_);
lean_ctor_set(v___x_440_, 1, v___x_436_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
lean_ctor_set_float(v___x_440_, sizeof(void*)*3, v___x_437_);
lean_ctor_set_float(v___x_440_, sizeof(void*)*3 + 8, v___x_437_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*3 + 16, v___x_438_);
v___x_441_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2));
v___x_442_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v_a_414_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
lean_inc(v_ref_412_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_ref_412_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_PersistentArray_push___redArg(v_traces_432_, v___x_443_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_444_);
v___x_446_ = v___x_434_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_444_);
lean_ctor_set_uint64(v_reuseFailAlloc_455_, sizeof(void*)*1, v_tid_431_);
v___x_446_ = v_reuseFailAlloc_455_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 4, v___x_446_);
v___x_448_ = v___x_429_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_env_420_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_nextMacroScope_421_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_ngen_422_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_auxDeclNGen_423_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_cache_424_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_messages_425_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_infoState_426_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_snapshotTasks_427_);
v___x_448_ = v_reuseFailAlloc_454_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_st_ref_set(v___y_410_, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3));
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_450_);
v___x_452_ = v___x_416_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___boxed(lean_object* v_cls_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v_cls_459_, v_msg_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_466_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0(void){
_start:
{
lean_object* v___x_467_; lean_object* v_dummy_468_; 
v___x_467_ = lean_box(0);
v_dummy_468_ = l_Lean_Expr_sort___override(v___x_467_);
return v_dummy_468_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_473_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
v___x_474_ = l_Lean_Name_append(v___x_473_, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_x_481_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v_head_493_; lean_object* v_tail_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_552_; 
v_head_493_ = lean_ctor_get(v_x_482_, 0);
v_tail_494_ = lean_ctor_get(v_x_482_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_552_ == 0)
{
v___x_496_ = v_x_482_;
v_isShared_497_ = v_isSharedCheck_552_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_tail_494_);
lean_inc(v_head_493_);
lean_dec(v_x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_552_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; 
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc_ref(v_x_481_);
v___x_498_ = lean_infer_type(v_x_481_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
v___x_500_ = lean_whnf(v_a_499_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = l_Lean_Expr_getAppFn(v_a_501_);
if (lean_obj_tag(v___x_502_) == 4)
{
lean_object* v_us_503_; lean_object* v_dummy_504_; lean_object* v_nargs_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_del_object(v___x_496_);
v_us_503_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_us_503_);
lean_dec_ref(v___x_502_);
v_dummy_504_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_505_ = l_Lean_Expr_getAppNumArgs(v_a_501_);
lean_inc(v_nargs_505_);
v___x_506_ = lean_mk_array(v_nargs_505_, v_dummy_504_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_sub(v_nargs_505_, v___x_507_);
lean_dec(v_nargs_505_);
v___x_509_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_501_, v___x_506_, v___x_508_);
v___x_510_ = l_Lean_Expr_const___override(v_head_493_, v_us_503_);
v___x_511_ = l_Lean_mkAppN(v___x_510_, v___x_509_);
lean_dec_ref(v___x_509_);
v___x_512_ = l_Lean_Expr_app___override(v___x_511_, v_x_481_);
v_x_481_ = v___x_512_;
v_x_482_ = v_tail_494_;
goto _start;
}
else
{
lean_object* v_options_514_; uint8_t v_hasTrace_515_; 
lean_dec_ref(v___x_502_);
lean_dec(v_tail_494_);
lean_dec(v_head_493_);
lean_dec_ref(v_x_481_);
v_options_514_ = lean_ctor_get(v___y_485_, 2);
v_hasTrace_515_ = lean_ctor_get_uint8(v_options_514_, sizeof(void*)*1);
if (v_hasTrace_515_ == 0)
{
lean_dec(v_a_501_);
lean_del_object(v___x_496_);
goto v___jp_488_;
}
else
{
lean_object* v_inheritedTraceOptions_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_inheritedTraceOptions_516_ = lean_ctor_get(v___y_485_, 13);
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_518_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_519_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_516_, v_options_514_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v_a_501_);
lean_del_object(v___x_496_);
goto v___jp_488_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5);
v___x_521_ = l_Lean_MessageData_ofExpr(v_a_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 7);
lean_ctor_set(v___x_496_, 1, v___x_521_);
lean_ctor_set(v___x_496_, 0, v___x_520_);
v___x_523_ = v___x_496_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_535_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v___x_517_, v___x_525_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_dec_ref(v___x_526_);
goto v___jp_488_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
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
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_del_object(v___x_496_);
lean_dec(v_tail_494_);
lean_dec(v_head_493_);
lean_dec_ref(v_x_481_);
v_a_536_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_500_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_500_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_del_object(v___x_496_);
lean_dec(v_tail_494_);
lean_dec(v_head_493_);
lean_dec_ref(v_x_481_);
v_a_544_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_498_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_498_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
v___jp_488_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___boxed(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(v_x_553_, v_x_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_560_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(lean_object* v_val_564_, lean_object* v_self_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_574_; 
lean_inc_ref(v_self_565_);
v___x_574_ = l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(v_self_565_, v_val_564_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
if (lean_obj_tag(v_a_575_) == 0)
{
lean_dec_ref(v_self_565_);
return v___x_574_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___x_574_);
v_val_576_ = lean_ctor_get(v_a_575_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_575_);
if (v_isSharedCheck_630_ == 0)
{
v___x_578_ = v_a_575_;
v_isShared_579_ = v_isSharedCheck_630_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_a_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_630_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; 
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
v___x_580_ = lean_infer_type(v_val_576_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
v___x_582_ = lean_whnf(v_a_581_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_613_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_613_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_613_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_613_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = l_Lean_Expr_fvarId_x21(v_self_565_);
lean_dec_ref(v_self_565_);
v___x_588_ = l_Lean_Expr_containsFVar(v_a_583_, v___x_587_);
lean_dec(v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_590_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_a_583_);
v___x_590_ = v___x_578_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_583_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_590_);
v___x_592_ = v___x_585_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v_options_595_; uint8_t v_hasTrace_596_; 
lean_del_object(v___x_585_);
lean_del_object(v___x_578_);
v_options_595_ = lean_ctor_get(v___y_568_, 2);
v_hasTrace_596_ = lean_ctor_get_uint8(v_options_595_, sizeof(void*)*1);
if (v_hasTrace_596_ == 0)
{
lean_dec(v_a_583_);
goto v___jp_571_;
}
else
{
lean_object* v_inheritedTraceOptions_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_inheritedTraceOptions_597_ = lean_ctor_get(v___y_568_, 13);
v___x_598_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_599_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_597_, v_options_595_, v___x_599_);
if (v___x_600_ == 0)
{
lean_dec(v_a_583_);
goto v___jp_571_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1);
v___x_602_ = l_Lean_indentExpr(v_a_583_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v___x_598_, v___x_603_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_dec_ref(v___x_604_);
goto v___jp_571_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
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
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_del_object(v___x_578_);
lean_dec_ref(v_self_565_);
v_a_614_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_582_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_582_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_del_object(v___x_578_);
lean_dec_ref(v_self_565_);
v_a_622_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_580_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_580_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_self_565_);
return v___x_574_;
}
v___jp_571_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed(lean_object* v_val_631_, lean_object* v_self_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(v_val_631_, v_self_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(lean_object* v_k_639_, lean_object* v_b_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
v___x_646_ = lean_apply_6(v_k_639_, v_b_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_k_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(v_k_647_, v_b_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(lean_object* v_name_655_, uint8_t v_bi_656_, lean_object* v_type_657_, lean_object* v_k_658_, uint8_t v_kind_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; 
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_665_, 0, v_k_658_);
v___x_666_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_655_, v_bi_656_, v_type_657_, v___f_665_, v_kind_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
return v___x_666_;
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_name_675_, lean_object* v_bi_676_, lean_object* v_type_677_, lean_object* v_k_678_, lean_object* v_kind_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v_bi_boxed_685_; uint8_t v_kind_boxed_686_; lean_object* v_res_687_; 
v_bi_boxed_685_ = lean_unbox(v_bi_676_);
v_kind_boxed_686_ = lean_unbox(v_kind_679_);
v_res_687_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_675_, v_bi_boxed_685_, v_type_677_, v_k_678_, v_kind_boxed_686_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(lean_object* v_name_688_, lean_object* v_type_689_, lean_object* v_k_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; 
v___x_696_ = 0;
v___x_697_ = 0;
v___x_698_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_688_, v___x_696_, v_type_689_, v_k_690_, v___x_697_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg___boxed(lean_object* v_name_699_, lean_object* v_type_700_, lean_object* v_k_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v_name_699_, v_type_700_, v_k_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(lean_object* v_structName_711_, lean_object* v_parentStructName_712_, lean_object* v_structType_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_env_720_; lean_object* v___x_721_; 
v___x_719_ = lean_st_ref_get(v_a_717_);
v_env_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_env_720_);
lean_dec(v___x_719_);
v___x_721_ = l_Lean_getPathToBaseStructure_x3f(v_env_720_, v_parentStructName_712_, v_structName_711_);
if (lean_obj_tag(v___x_721_) == 1)
{
lean_object* v_val_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_val_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v___x_721_);
v___f_723_ = lean_alloc_closure((void*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed), 7, 1);
lean_closure_set(v___f_723_, 0, v_val_722_);
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1));
v___x_725_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v___x_724_, v_structType_713_, v___f_723_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v___x_721_);
lean_dec_ref(v_structType_713_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___boxed(lean_object* v_structName_728_, lean_object* v_parentStructName_729_, lean_object* v_structType_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_structName_728_, v_parentStructName_729_, v_structType_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_parentStructName_729_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(lean_object* v_00_u03b1_737_, lean_object* v_name_738_, uint8_t v_bi_739_, lean_object* v_type_740_, lean_object* v_k_741_, uint8_t v_kind_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_738_, v_bi_739_, v_type_740_, v_k_741_, v_kind_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___boxed(lean_object* v_00_u03b1_749_, lean_object* v_name_750_, lean_object* v_bi_751_, lean_object* v_type_752_, lean_object* v_k_753_, lean_object* v_kind_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
uint8_t v_bi_boxed_760_; uint8_t v_kind_boxed_761_; lean_object* v_res_762_; 
v_bi_boxed_760_ = lean_unbox(v_bi_751_);
v_kind_boxed_761_ = lean_unbox(v_kind_754_);
v_res_762_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(v_00_u03b1_749_, v_name_750_, v_bi_boxed_760_, v_type_752_, v_k_753_, v_kind_boxed_761_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(lean_object* v_00_u03b1_763_, lean_object* v_name_764_, lean_object* v_type_765_, lean_object* v_k_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v_name_764_, v_type_765_, v_k_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___boxed(lean_object* v_00_u03b1_773_, lean_object* v_name_774_, lean_object* v_type_775_, lean_object* v_k_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(v_00_u03b1_773_, v_name_774_, v_type_775_, v_k_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_782_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object* v_opts_783_, lean_object* v_opt_784_){
_start:
{
lean_object* v_name_785_; lean_object* v_defValue_786_; lean_object* v_map_787_; lean_object* v___x_788_; 
v_name_785_ = lean_ctor_get(v_opt_784_, 0);
v_defValue_786_ = lean_ctor_get(v_opt_784_, 1);
v_map_787_ = lean_ctor_get(v_opts_783_, 0);
v___x_788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_787_, v_name_785_);
if (lean_obj_tag(v___x_788_) == 0)
{
uint8_t v___x_789_; 
v___x_789_ = lean_unbox(v_defValue_786_);
return v___x_789_;
}
else
{
lean_object* v_val_790_; 
v_val_790_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_790_);
lean_dec_ref(v___x_788_);
if (lean_obj_tag(v_val_790_) == 1)
{
uint8_t v_v_791_; 
v_v_791_ = lean_ctor_get_uint8(v_val_790_, 0);
lean_dec_ref(v_val_790_);
return v_v_791_;
}
else
{
uint8_t v___x_792_; 
lean_dec(v_val_790_);
v___x_792_ = lean_unbox(v_defValue_786_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object* v_opts_793_, lean_object* v_opt_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_793_, v_opt_794_);
lean_dec_ref(v_opt_794_);
lean_dec_ref(v_opts_793_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object* v_kind_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v_auxDeclNGen_801_; lean_object* v___x_802_; lean_object* v_env_803_; lean_object* v___x_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v___x_807_; lean_object* v_env_808_; lean_object* v_nextMacroScope_809_; lean_object* v_ngen_810_; lean_object* v_traceState_811_; lean_object* v_cache_812_; lean_object* v_messages_813_; lean_object* v_infoState_814_; lean_object* v_snapshotTasks_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
v___x_800_ = lean_st_ref_get(v___y_798_);
v_auxDeclNGen_801_ = lean_ctor_get(v___x_800_, 3);
lean_inc_ref(v_auxDeclNGen_801_);
lean_dec(v___x_800_);
v___x_802_ = lean_st_ref_get(v___y_798_);
v_env_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_env_803_);
lean_dec(v___x_802_);
v___x_804_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_803_, v_auxDeclNGen_801_, v_kind_797_);
v_fst_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_snd_806_);
lean_dec_ref(v___x_804_);
v___x_807_ = lean_st_ref_take(v___y_798_);
v_env_808_ = lean_ctor_get(v___x_807_, 0);
v_nextMacroScope_809_ = lean_ctor_get(v___x_807_, 1);
v_ngen_810_ = lean_ctor_get(v___x_807_, 2);
v_traceState_811_ = lean_ctor_get(v___x_807_, 4);
v_cache_812_ = lean_ctor_get(v___x_807_, 5);
v_messages_813_ = lean_ctor_get(v___x_807_, 6);
v_infoState_814_ = lean_ctor_get(v___x_807_, 7);
v_snapshotTasks_815_ = lean_ctor_get(v___x_807_, 8);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_807_, 3);
lean_dec(v_unused_825_);
v___x_817_ = v___x_807_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snapshotTasks_815_);
lean_inc(v_infoState_814_);
lean_inc(v_messages_813_);
lean_inc(v_cache_812_);
lean_inc(v_traceState_811_);
lean_inc(v_ngen_810_);
lean_inc(v_nextMacroScope_809_);
lean_inc(v_env_808_);
lean_dec(v___x_807_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 3, v_snd_806_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_env_808_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_nextMacroScope_809_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_ngen_810_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_snd_806_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_traceState_811_);
lean_ctor_set(v_reuseFailAlloc_823_, 5, v_cache_812_);
lean_ctor_set(v_reuseFailAlloc_823_, 6, v_messages_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 7, v_infoState_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 8, v_snapshotTasks_815_);
v___x_820_ = v_reuseFailAlloc_823_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_st_ref_set(v___y_798_, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_fst_805_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object* v_kind_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_826_, v___y_827_);
lean_dec(v___y_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object* v_kind_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_830_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object* v_kind_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(v_kind_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_843_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_844_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_850_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
lean_ctor_set(v___x_850_, 2, v___x_849_);
lean_ctor_set(v___x_850_, 3, v___x_849_);
lean_ctor_set(v___x_850_, 4, v___x_849_);
lean_ctor_set(v___x_850_, 5, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object* v_declName_851_, uint8_t v_s_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; lean_object* v_env_857_; lean_object* v_nextMacroScope_858_; lean_object* v_ngen_859_; lean_object* v_auxDeclNGen_860_; lean_object* v_traceState_861_; lean_object* v_messages_862_; lean_object* v_infoState_863_; lean_object* v_snapshotTasks_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_893_; 
v___x_856_ = lean_st_ref_take(v___y_854_);
v_env_857_ = lean_ctor_get(v___x_856_, 0);
v_nextMacroScope_858_ = lean_ctor_get(v___x_856_, 1);
v_ngen_859_ = lean_ctor_get(v___x_856_, 2);
v_auxDeclNGen_860_ = lean_ctor_get(v___x_856_, 3);
v_traceState_861_ = lean_ctor_get(v___x_856_, 4);
v_messages_862_ = lean_ctor_get(v___x_856_, 6);
v_infoState_863_ = lean_ctor_get(v___x_856_, 7);
v_snapshotTasks_864_ = lean_ctor_get(v___x_856_, 8);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_856_, 5);
lean_dec(v_unused_894_);
v___x_866_ = v___x_856_;
v_isShared_867_ = v_isSharedCheck_893_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snapshotTasks_864_);
lean_inc(v_infoState_863_);
lean_inc(v_messages_862_);
lean_inc(v_traceState_861_);
lean_inc(v_auxDeclNGen_860_);
lean_inc(v_ngen_859_);
lean_inc(v_nextMacroScope_858_);
lean_inc(v_env_857_);
lean_dec(v___x_856_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_893_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_868_ = 0;
v___x_869_ = lean_box(0);
v___x_870_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_857_, v_declName_851_, v_s_852_, v___x_868_, v___x_869_);
v___x_871_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 5, v___x_871_);
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_873_ = v___x_866_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_nextMacroScope_858_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_ngen_859_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_auxDeclNGen_860_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_traceState_861_);
lean_ctor_set(v_reuseFailAlloc_892_, 5, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_892_, 6, v_messages_862_);
lean_ctor_set(v_reuseFailAlloc_892_, 7, v_infoState_863_);
lean_ctor_set(v_reuseFailAlloc_892_, 8, v_snapshotTasks_864_);
v___x_873_ = v_reuseFailAlloc_892_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_mctx_876_; lean_object* v_zetaDeltaFVarIds_877_; lean_object* v_postponed_878_; lean_object* v_diag_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
v___x_874_ = lean_st_ref_set(v___y_854_, v___x_873_);
v___x_875_ = lean_st_ref_take(v___y_853_);
v_mctx_876_ = lean_ctor_get(v___x_875_, 0);
v_zetaDeltaFVarIds_877_ = lean_ctor_get(v___x_875_, 2);
v_postponed_878_ = lean_ctor_get(v___x_875_, 3);
v_diag_879_ = lean_ctor_get(v___x_875_, 4);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_875_, 1);
lean_dec(v_unused_891_);
v___x_881_ = v___x_875_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_diag_879_);
lean_inc(v_postponed_878_);
lean_inc(v_zetaDeltaFVarIds_877_);
lean_inc(v_mctx_876_);
lean_dec(v___x_875_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v___x_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_mctx_876_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_zetaDeltaFVarIds_877_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_postponed_878_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_diag_879_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_st_ref_set(v___y_853_, v___x_885_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object* v_declName_895_, lean_object* v_s_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v_s_boxed_900_; lean_object* v_res_901_; 
v_s_boxed_900_ = lean_unbox(v_s_896_);
v_res_901_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_895_, v_s_boxed_900_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec(v___y_897_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object* v_declName_902_, uint8_t v_s_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_902_, v_s_903_, v___y_905_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object* v_declName_910_, lean_object* v_s_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_s_boxed_917_; lean_object* v_res_918_; 
v_s_boxed_917_ = lean_unbox(v_s_911_);
v_res_918_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(v_declName_910_, v_s_boxed_917_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(lean_object* v_e_919_, lean_object* v___y_920_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Expr_hasMVar(v_e_919_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v_e_919_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; lean_object* v_mctx_925_; lean_object* v___x_926_; lean_object* v_fst_927_; lean_object* v_snd_928_; lean_object* v___x_929_; lean_object* v_cache_930_; lean_object* v_zetaDeltaFVarIds_931_; lean_object* v_postponed_932_; lean_object* v_diag_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_942_; 
v___x_924_ = lean_st_ref_get(v___y_920_);
v_mctx_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc_ref(v_mctx_925_);
lean_dec(v___x_924_);
v___x_926_ = l_Lean_instantiateMVarsCore(v_mctx_925_, v_e_919_);
v_fst_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_fst_927_);
v_snd_928_ = lean_ctor_get(v___x_926_, 1);
lean_inc(v_snd_928_);
lean_dec_ref(v___x_926_);
v___x_929_ = lean_st_ref_take(v___y_920_);
v_cache_930_ = lean_ctor_get(v___x_929_, 1);
v_zetaDeltaFVarIds_931_ = lean_ctor_get(v___x_929_, 2);
v_postponed_932_ = lean_ctor_get(v___x_929_, 3);
v_diag_933_ = lean_ctor_get(v___x_929_, 4);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_943_);
v___x_935_ = v___x_929_;
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_diag_933_);
lean_inc(v_postponed_932_);
lean_inc(v_zetaDeltaFVarIds_931_);
lean_inc(v_cache_930_);
lean_dec(v___x_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_snd_928_);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_snd_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_cache_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_zetaDeltaFVarIds_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_postponed_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_diag_933_);
v___x_938_ = v_reuseFailAlloc_941_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_st_ref_set(v___y_920_, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_fst_927_);
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object* v_e_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_e_944_, v___y_945_);
lean_dec(v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5(lean_object* v_e_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_e_948_, v___y_950_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object* v_e_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5(v_e_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_961_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_unsigned_to_nat(32u);
v___x_963_ = lean_mk_empty_array_with_capacity(v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_965_ = ((size_t)5ULL);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_unsigned_to_nat(32u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0);
v___x_970_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set(v___x_970_, 2, v___x_966_);
lean_ctor_set(v___x_970_, 3, v___x_966_);
lean_ctor_set_usize(v___x_970_, 4, v___x_965_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v_traceState_974_; lean_object* v_traces_975_; lean_object* v___x_976_; lean_object* v_traceState_977_; lean_object* v_env_978_; lean_object* v_nextMacroScope_979_; lean_object* v_ngen_980_; lean_object* v_auxDeclNGen_981_; lean_object* v_cache_982_; lean_object* v_messages_983_; lean_object* v_infoState_984_; lean_object* v_snapshotTasks_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1004_; 
v___x_973_ = lean_st_ref_get(v___y_971_);
v_traceState_974_ = lean_ctor_get(v___x_973_, 4);
lean_inc_ref(v_traceState_974_);
lean_dec(v___x_973_);
v_traces_975_ = lean_ctor_get(v_traceState_974_, 0);
lean_inc_ref(v_traces_975_);
lean_dec_ref(v_traceState_974_);
v___x_976_ = lean_st_ref_take(v___y_971_);
v_traceState_977_ = lean_ctor_get(v___x_976_, 4);
v_env_978_ = lean_ctor_get(v___x_976_, 0);
v_nextMacroScope_979_ = lean_ctor_get(v___x_976_, 1);
v_ngen_980_ = lean_ctor_get(v___x_976_, 2);
v_auxDeclNGen_981_ = lean_ctor_get(v___x_976_, 3);
v_cache_982_ = lean_ctor_get(v___x_976_, 5);
v_messages_983_ = lean_ctor_get(v___x_976_, 6);
v_infoState_984_ = lean_ctor_get(v___x_976_, 7);
v_snapshotTasks_985_ = lean_ctor_get(v___x_976_, 8);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_987_ = v___x_976_;
v_isShared_988_ = v_isSharedCheck_1004_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snapshotTasks_985_);
lean_inc(v_infoState_984_);
lean_inc(v_messages_983_);
lean_inc(v_cache_982_);
lean_inc(v_traceState_977_);
lean_inc(v_auxDeclNGen_981_);
lean_inc(v_ngen_980_);
lean_inc(v_nextMacroScope_979_);
lean_inc(v_env_978_);
lean_dec(v___x_976_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1004_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
uint64_t v_tid_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1002_; 
v_tid_989_ = lean_ctor_get_uint64(v_traceState_977_, sizeof(void*)*1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_traceState_977_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_traceState_977_, 0);
lean_dec(v_unused_1003_);
v___x_991_ = v_traceState_977_;
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
else
{
lean_dec(v_traceState_977_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_993_);
lean_ctor_set_uint64(v_reuseFailAlloc_1001_, sizeof(void*)*1, v_tid_989_);
v___x_995_ = v_reuseFailAlloc_1001_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v___x_995_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_env_978_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_nextMacroScope_979_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_ngen_980_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_auxDeclNGen_981_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1000_, 5, v_cache_982_);
lean_ctor_set(v_reuseFailAlloc_1000_, 6, v_messages_983_);
lean_ctor_set(v_reuseFailAlloc_1000_, 7, v_infoState_984_);
lean_ctor_set(v_reuseFailAlloc_1000_, 8, v_snapshotTasks_985_);
v___x_997_ = v_reuseFailAlloc_1000_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_st_ref_set(v___y_971_, v___x_997_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v_traces_975_);
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___y_1005_);
lean_dec(v___y_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11(lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11(v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1019_;
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Meta_wrapInstance___lam__0___closed__0));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object* v_expectedType_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = lean_obj_once(&l_Lean_Meta_wrapInstance___lam__0___closed__1, &l_Lean_Meta_wrapInstance___lam__0___closed__1_once, _init_l_Lean_Meta_wrapInstance___lam__0___closed__1);
v___x_1031_ = l_Lean_MessageData_ofExpr(v_expectedType_1023_);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object* v_expectedType_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Meta_wrapInstance___lam__0(v_expectedType_1034_, v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_x_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
if (lean_obj_tag(v_a_1042_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_List_reverse___redArg(v_a_1043_);
return v___x_1044_;
}
else
{
lean_object* v_head_1045_; lean_object* v_tail_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1055_; 
v_head_1045_ = lean_ctor_get(v_a_1042_, 0);
v_tail_1046_ = lean_ctor_get(v_a_1042_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1042_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1048_ = v_a_1042_;
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_tail_1046_);
lean_inc(v_head_1045_);
lean_dec(v_a_1042_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = l_Lean_MessageData_ofExpr(v_head_1045_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_a_1043_);
lean_ctor_set(v___x_1048_, 0, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_a_1043_);
v___x_1052_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
v_a_1042_ = v_tail_1046_;
v_a_1043_ = v___x_1052_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
lean_ctor_set(v___x_1061_, 2, v___x_1060_);
lean_ctor_set(v___x_1061_, 3, v___x_1060_);
lean_ctor_set(v___x_1061_, 4, v___x_1059_);
lean_ctor_set(v___x_1061_, 5, v___x_1059_);
lean_ctor_set(v___x_1061_, 6, v___x_1059_);
lean_ctor_set(v___x_1061_, 7, v___x_1059_);
lean_ctor_set(v___x_1061_, 8, v___x_1059_);
lean_ctor_set(v___x_1061_, 9, v___x_1059_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_unsigned_to_nat(32u);
v___x_1063_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1065_ = ((size_t)5ULL);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_unsigned_to_nat(32u);
v___x_1068_ = lean_mk_empty_array_with_capacity(v___x_1067_);
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3);
v___x_1070_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
lean_ctor_set(v___x_1070_, 2, v___x_1066_);
lean_ctor_set(v___x_1070_, 3, v___x_1066_);
lean_ctor_set_usize(v___x_1070_, 4, v___x_1065_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = lean_box(1);
v___x_1072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4);
v___x_1073_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1);
v___x_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1072_);
lean_ctor_set(v___x_1074_, 2, v___x_1071_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v_env_1101_; uint8_t v___x_1102_; 
v___x_1100_ = lean_st_ref_get(v___y_1098_);
v_env_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_env_1101_);
lean_dec(v___x_1100_);
v___x_1102_ = l_Lean_Name_isAnonymous(v_declHint_1097_);
if (v___x_1102_ == 0)
{
uint8_t v_isExporting_1103_; 
v_isExporting_1103_ = lean_ctor_get_uint8(v_env_1101_, sizeof(void*)*8);
if (v_isExporting_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_msg_1096_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
lean_inc_ref(v_env_1101_);
v___x_1105_ = l_Lean_Environment_setExporting(v_env_1101_, v___x_1102_);
lean_inc(v_declHint_1097_);
lean_inc_ref(v___x_1105_);
v___x_1106_ = l_Lean_Environment_contains(v___x_1105_, v_declHint_1097_, v_isExporting_1103_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_dec_ref(v___x_1105_);
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_msg_1096_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_c_1113_; lean_object* v___x_1114_; 
v___x_1108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2);
v___x_1109_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5);
v___x_1110_ = l_Lean_Options_empty;
v___x_1111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1105_);
lean_ctor_set(v___x_1111_, 1, v___x_1108_);
lean_ctor_set(v___x_1111_, 2, v___x_1109_);
lean_ctor_set(v___x_1111_, 3, v___x_1110_);
lean_inc(v_declHint_1097_);
v___x_1112_ = l_Lean_MessageData_ofConstName(v_declHint_1097_, v___x_1102_);
v_c_1113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1113_, 0, v___x_1111_);
lean_ctor_set(v_c_1113_, 1, v___x_1112_);
v___x_1114_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1101_, v_declHint_1097_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_c_1113_);
v___x_1117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_MessageData_note(v___x_1118_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_msg_1096_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
else
{
lean_object* v_val_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1157_; 
v_val_1122_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1124_ = v___x_1114_;
v_isShared_1125_ = v_isSharedCheck_1157_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_val_1122_);
lean_dec(v___x_1114_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1157_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_mod_1129_; uint8_t v___x_1130_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = l_Lean_Environment_header(v_env_1101_);
lean_dec_ref(v_env_1101_);
v___x_1128_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1127_);
v_mod_1129_ = lean_array_get(v___x_1126_, v___x_1128_, v_val_1122_);
lean_dec(v_val_1122_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = l_Lean_isPrivateName(v_declHint_1097_);
lean_dec(v_declHint_1097_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_c_1113_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_note(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_msg_1096_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1140_);
v___x_1142_ = v___x_1124_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_c_1113_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_note(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_msg_1096_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1153_);
v___x_1155_ = v___x_1124_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_msg_1096_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___boxed(lean_object* v_msg_1159_, lean_object* v_declHint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(v_msg_1159_, v_declHint_1160_, v___y_1161_);
lean_dec(v___y_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(lean_object* v_msg_1164_, lean_object* v_declHint_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
v___x_1171_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(v_msg_1164_, v_declHint_1165_, v___y_1169_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = l_Lean_unknownIdentifierMessageTag;
v___x_1177_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v_a_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28___boxed(lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(v_msg_1182_, v_declHint_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(lean_object* v_ref_1190_, lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_fileName_1197_; lean_object* v_fileMap_1198_; lean_object* v_options_1199_; lean_object* v_currRecDepth_1200_; lean_object* v_maxRecDepth_1201_; lean_object* v_ref_1202_; lean_object* v_currNamespace_1203_; lean_object* v_openDecls_1204_; lean_object* v_initHeartbeats_1205_; lean_object* v_maxHeartbeats_1206_; lean_object* v_quotContext_1207_; lean_object* v_currMacroScope_1208_; uint8_t v_diag_1209_; lean_object* v_cancelTk_x3f_1210_; uint8_t v_suppressElabErrors_1211_; lean_object* v_inheritedTraceOptions_1212_; lean_object* v_ref_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_fileName_1197_ = lean_ctor_get(v___y_1194_, 0);
v_fileMap_1198_ = lean_ctor_get(v___y_1194_, 1);
v_options_1199_ = lean_ctor_get(v___y_1194_, 2);
v_currRecDepth_1200_ = lean_ctor_get(v___y_1194_, 3);
v_maxRecDepth_1201_ = lean_ctor_get(v___y_1194_, 4);
v_ref_1202_ = lean_ctor_get(v___y_1194_, 5);
v_currNamespace_1203_ = lean_ctor_get(v___y_1194_, 6);
v_openDecls_1204_ = lean_ctor_get(v___y_1194_, 7);
v_initHeartbeats_1205_ = lean_ctor_get(v___y_1194_, 8);
v_maxHeartbeats_1206_ = lean_ctor_get(v___y_1194_, 9);
v_quotContext_1207_ = lean_ctor_get(v___y_1194_, 10);
v_currMacroScope_1208_ = lean_ctor_get(v___y_1194_, 11);
v_diag_1209_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*14);
v_cancelTk_x3f_1210_ = lean_ctor_get(v___y_1194_, 12);
v_suppressElabErrors_1211_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1212_ = lean_ctor_get(v___y_1194_, 13);
v_ref_1213_ = l_Lean_replaceRef(v_ref_1190_, v_ref_1202_);
lean_inc_ref(v_inheritedTraceOptions_1212_);
lean_inc(v_cancelTk_x3f_1210_);
lean_inc(v_currMacroScope_1208_);
lean_inc(v_quotContext_1207_);
lean_inc(v_maxHeartbeats_1206_);
lean_inc(v_initHeartbeats_1205_);
lean_inc(v_openDecls_1204_);
lean_inc(v_currNamespace_1203_);
lean_inc(v_maxRecDepth_1201_);
lean_inc(v_currRecDepth_1200_);
lean_inc_ref(v_options_1199_);
lean_inc_ref(v_fileMap_1198_);
lean_inc_ref(v_fileName_1197_);
v___x_1214_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1214_, 0, v_fileName_1197_);
lean_ctor_set(v___x_1214_, 1, v_fileMap_1198_);
lean_ctor_set(v___x_1214_, 2, v_options_1199_);
lean_ctor_set(v___x_1214_, 3, v_currRecDepth_1200_);
lean_ctor_set(v___x_1214_, 4, v_maxRecDepth_1201_);
lean_ctor_set(v___x_1214_, 5, v_ref_1213_);
lean_ctor_set(v___x_1214_, 6, v_currNamespace_1203_);
lean_ctor_set(v___x_1214_, 7, v_openDecls_1204_);
lean_ctor_set(v___x_1214_, 8, v_initHeartbeats_1205_);
lean_ctor_set(v___x_1214_, 9, v_maxHeartbeats_1206_);
lean_ctor_set(v___x_1214_, 10, v_quotContext_1207_);
lean_ctor_set(v___x_1214_, 11, v_currMacroScope_1208_);
lean_ctor_set(v___x_1214_, 12, v_cancelTk_x3f_1210_);
lean_ctor_set(v___x_1214_, 13, v_inheritedTraceOptions_1212_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*14, v_diag_1209_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*14 + 1, v_suppressElabErrors_1211_);
v___x_1215_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_1191_, v___y_1192_, v___y_1193_, v___x_1214_, v___y_1195_);
lean_dec_ref(v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg___boxed(lean_object* v_ref_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(v_ref_1216_, v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_ref_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(lean_object* v_ref_1224_, lean_object* v_msg_1225_, lean_object* v_declHint_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; 
v___x_1232_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(v_msg_1225_, v_declHint_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(v_ref_1224_, v_a_1233_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v_declHint_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(v_ref_1235_, v_msg_1236_, v_declHint_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v_ref_1235_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0));
v___x_1246_ = l_Lean_stringToMessageData(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(lean_object* v_ref_1247_, lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1254_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1);
v___x_1255_ = 0;
lean_inc(v_constName_1248_);
v___x_1256_ = l_Lean_MessageData_ofConstName(v_constName_1248_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1254_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(v_ref_1247_, v___x_1259_, v_constName_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1261_, lean_object* v_constName_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(v_ref_1261_, v_constName_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v_ref_1261_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_ref_1275_; lean_object* v___x_1276_; 
v_ref_1275_ = lean_ctor_get(v___y_1272_, 5);
v___x_1276_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(v_ref_1275_, v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg___boxed(lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object* v_constName_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v_env_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_st_ref_get(v___y_1288_);
v_env_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_ref(v_env_1291_);
lean_dec(v___x_1290_);
v___x_1292_ = 0;
lean_inc(v_constName_1284_);
v___x_1293_ = l_Lean_Environment_find_x3f(v_env_1291_, v_constName_1284_, v___x_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1294_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_constName_1284_);
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1293_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 0);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object* v_constName_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_constName_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(size_t v_sz_1310_, size_t v_i_1311_, lean_object* v_bs_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1311_, v_sz_1310_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_bs_1312_);
return v___x_1319_;
}
else
{
lean_object* v_v_1320_; lean_object* v___x_1321_; 
v_v_1320_ = lean_array_uget_borrowed(v_bs_1312_, v_i_1311_);
lean_inc(v_v_1320_);
v___x_1321_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_v_1320_, v___y_1314_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v_bs_x27_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v_bs_x27_1324_ = lean_array_uset(v_bs_1312_, v_i_1311_, v___x_1323_);
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_add(v_i_1311_, v___x_1325_);
v___x_1327_ = lean_array_uset(v_bs_x27_1324_, v_i_1311_, v_a_1322_);
v_i_1311_ = v___x_1326_;
v_bs_1312_ = v___x_1327_;
goto _start;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_bs_1312_);
v_a_1329_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1321_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1321_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_bs_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_boxed_1345_, v_i_boxed_1346_, v_bs_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object* v_cls_1348_, lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_ref_1355_; lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1401_; 
v_ref_1355_ = lean_ctor_get(v___y_1352_, 5);
v___x_1356_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v_traceState_1362_; lean_object* v_env_1363_; lean_object* v_nextMacroScope_1364_; lean_object* v_ngen_1365_; lean_object* v_auxDeclNGen_1366_; lean_object* v_cache_1367_; lean_object* v_messages_1368_; lean_object* v_infoState_1369_; lean_object* v_snapshotTasks_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1400_; 
v___x_1361_ = lean_st_ref_take(v___y_1353_);
v_traceState_1362_ = lean_ctor_get(v___x_1361_, 4);
v_env_1363_ = lean_ctor_get(v___x_1361_, 0);
v_nextMacroScope_1364_ = lean_ctor_get(v___x_1361_, 1);
v_ngen_1365_ = lean_ctor_get(v___x_1361_, 2);
v_auxDeclNGen_1366_ = lean_ctor_get(v___x_1361_, 3);
v_cache_1367_ = lean_ctor_get(v___x_1361_, 5);
v_messages_1368_ = lean_ctor_get(v___x_1361_, 6);
v_infoState_1369_ = lean_ctor_get(v___x_1361_, 7);
v_snapshotTasks_1370_ = lean_ctor_get(v___x_1361_, 8);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1372_ = v___x_1361_;
v_isShared_1373_ = v_isSharedCheck_1400_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snapshotTasks_1370_);
lean_inc(v_infoState_1369_);
lean_inc(v_messages_1368_);
lean_inc(v_cache_1367_);
lean_inc(v_traceState_1362_);
lean_inc(v_auxDeclNGen_1366_);
lean_inc(v_ngen_1365_);
lean_inc(v_nextMacroScope_1364_);
lean_inc(v_env_1363_);
lean_dec(v___x_1361_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1400_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
uint64_t v_tid_1374_; lean_object* v_traces_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1399_; 
v_tid_1374_ = lean_ctor_get_uint64(v_traceState_1362_, sizeof(void*)*1);
v_traces_1375_ = lean_ctor_get(v_traceState_1362_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_traceState_1362_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1377_ = v_traceState_1362_;
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_traces_1375_);
lean_dec(v_traceState_1362_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; double v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
v___x_1381_ = 0;
v___x_1382_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_1383_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1383_, 0, v_cls_1348_);
lean_ctor_set(v___x_1383_, 1, v___x_1379_);
lean_ctor_set(v___x_1383_, 2, v___x_1382_);
lean_ctor_set_float(v___x_1383_, sizeof(void*)*3, v___x_1380_);
lean_ctor_set_float(v___x_1383_, sizeof(void*)*3 + 8, v___x_1380_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 16, v___x_1381_);
v___x_1384_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2));
v___x_1385_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v_a_1357_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
lean_inc(v_ref_1355_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_ref_1355_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = l_Lean_PersistentArray_push___redArg(v_traces_1375_, v___x_1386_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1387_);
v___x_1389_ = v___x_1377_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1387_);
lean_ctor_set_uint64(v_reuseFailAlloc_1398_, sizeof(void*)*1, v_tid_1374_);
v___x_1389_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___x_1389_);
v___x_1391_ = v___x_1372_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_env_1363_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_nextMacroScope_1364_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_ngen_1365_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_auxDeclNGen_1366_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v_cache_1367_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_messages_1368_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_infoState_1369_);
lean_ctor_set(v_reuseFailAlloc_1397_, 8, v_snapshotTasks_1370_);
v___x_1391_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = lean_st_ref_set(v___y_1353_, v___x_1391_);
v___x_1393_ = lean_box(0);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1393_);
v___x_1395_ = v___x_1359_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object* v_cls_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1402_, v_msg_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(lean_object* v_x_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v_ks_1414_; lean_object* v_vs_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1439_; 
v_ks_1414_ = lean_ctor_get(v_x_1410_, 0);
v_vs_1415_ = lean_ctor_get(v_x_1410_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1417_ = v_x_1410_;
v_isShared_1418_ = v_isSharedCheck_1439_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_vs_1415_);
lean_inc(v_ks_1414_);
lean_dec(v_x_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1439_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_array_get_size(v_ks_1414_);
v___x_1420_ = lean_nat_dec_lt(v_x_1411_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec(v_x_1411_);
v___x_1421_ = lean_array_push(v_ks_1414_, v_x_1412_);
v___x_1422_ = lean_array_push(v_vs_1415_, v_x_1413_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1422_);
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
lean_object* v_k_x27_1426_; uint8_t v___x_1427_; 
v_k_x27_1426_ = lean_array_fget_borrowed(v_ks_1414_, v_x_1411_);
v___x_1427_ = l_Lean_instBEqMVarId_beq(v_x_1412_, v_k_x27_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; 
if (v_isShared_1418_ == 0)
{
v___x_1429_ = v___x_1417_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_ks_1414_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_vs_1415_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_nat_add(v_x_1411_, v___x_1430_);
lean_dec(v_x_1411_);
v_x_1410_ = v___x_1429_;
v_x_1411_ = v___x_1431_;
goto _start;
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = lean_array_fset(v_ks_1414_, v_x_1411_, v_x_1412_);
v___x_1435_ = lean_array_fset(v_vs_1415_, v_x_1411_, v_x_1413_);
lean_dec(v_x_1411_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1435_);
lean_ctor_set(v___x_1417_, 0, v___x_1434_);
v___x_1437_ = v___x_1417_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(lean_object* v_n_1440_, lean_object* v_k_1441_, lean_object* v_v_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(v_n_1440_, v___x_1443_, v_k_1441_, v_v_1442_);
return v___x_1444_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; 
v___x_1445_ = ((size_t)5ULL);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_shift_left(v___x_1446_, v___x_1445_);
return v___x_1447_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; 
v___x_1448_ = ((size_t)1ULL);
v___x_1449_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0);
v___x_1450_ = lean_usize_sub(v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(lean_object* v_x_1452_, size_t v_x_1453_, size_t v_x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
if (lean_obj_tag(v_x_1452_) == 0)
{
lean_object* v_es_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; lean_object* v_j_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_es_1457_ = lean_ctor_get(v_x_1452_, 0);
v___x_1458_ = ((size_t)5ULL);
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1);
v___x_1461_ = lean_usize_land(v_x_1453_, v___x_1460_);
v_j_1462_ = lean_usize_to_nat(v___x_1461_);
v___x_1463_ = lean_array_get_size(v_es_1457_);
v___x_1464_ = lean_nat_dec_lt(v_j_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v_j_1462_);
lean_dec(v_x_1456_);
lean_dec(v_x_1455_);
return v_x_1452_;
}
else
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1501_; 
lean_inc_ref(v_es_1457_);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_x_1452_, 0);
lean_dec(v_unused_1502_);
v___x_1466_ = v_x_1452_;
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_x_1452_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_v_1468_; lean_object* v___x_1469_; lean_object* v_xs_x27_1470_; lean_object* v___y_1472_; 
v_v_1468_ = lean_array_fget(v_es_1457_, v_j_1462_);
v___x_1469_ = lean_box(0);
v_xs_x27_1470_ = lean_array_fset(v_es_1457_, v_j_1462_, v___x_1469_);
switch(lean_obj_tag(v_v_1468_))
{
case 0:
{
lean_object* v_key_1477_; lean_object* v_val_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1488_; 
v_key_1477_ = lean_ctor_get(v_v_1468_, 0);
v_val_1478_ = lean_ctor_get(v_v_1468_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_v_1468_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1480_ = v_v_1468_;
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_val_1478_);
lean_inc(v_key_1477_);
lean_dec(v_v_1468_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Lean_instBEqMVarId_beq(v_x_1455_, v_key_1477_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_del_object(v___x_1480_);
v___x_1483_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1477_, v_val_1478_, v_x_1455_, v_x_1456_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
v___y_1472_ = v___x_1484_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_val_1478_);
lean_dec(v_key_1477_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_x_1456_);
lean_ctor_set(v___x_1480_, 0, v_x_1455_);
v___x_1486_ = v___x_1480_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_x_1455_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_x_1456_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v___y_1472_ = v___x_1486_;
goto v___jp_1471_;
}
}
}
}
case 1:
{
lean_object* v_node_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1499_; 
v_node_1489_ = lean_ctor_get(v_v_1468_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_v_1468_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1491_ = v_v_1468_;
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_node_1489_);
lean_dec(v_v_1468_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1493_ = lean_usize_shift_right(v_x_1453_, v___x_1458_);
v___x_1494_ = lean_usize_add(v_x_1454_, v___x_1459_);
v___x_1495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_node_1489_, v___x_1493_, v___x_1494_, v_x_1455_, v_x_1456_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1495_);
v___x_1497_ = v___x_1491_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v___y_1472_ = v___x_1497_;
goto v___jp_1471_;
}
}
}
default: 
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_x_1455_);
lean_ctor_set(v___x_1500_, 1, v_x_1456_);
v___y_1472_ = v___x_1500_;
goto v___jp_1471_;
}
}
v___jp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_array_fset(v_xs_x27_1470_, v_j_1462_, v___y_1472_);
lean_dec(v_j_1462_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1473_);
v___x_1475_ = v___x_1466_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
else
{
lean_object* v_ks_1503_; lean_object* v_vs_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1524_; 
v_ks_1503_ = lean_ctor_get(v_x_1452_, 0);
v_vs_1504_ = lean_ctor_get(v_x_1452_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1506_ = v_x_1452_;
v_isShared_1507_ = v_isSharedCheck_1524_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_vs_1504_);
lean_inc(v_ks_1503_);
lean_dec(v_x_1452_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1524_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_ks_1503_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_vs_1504_);
v___x_1509_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v_newNode_1510_; uint8_t v___y_1512_; size_t v___x_1518_; uint8_t v___x_1519_; 
v_newNode_1510_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(v___x_1509_, v_x_1455_, v_x_1456_);
v___x_1518_ = ((size_t)7ULL);
v___x_1519_ = lean_usize_dec_le(v___x_1518_, v_x_1454_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1510_);
v___x_1521_ = lean_unsigned_to_nat(4u);
v___x_1522_ = lean_nat_dec_lt(v___x_1520_, v___x_1521_);
lean_dec(v___x_1520_);
v___y_1512_ = v___x_1522_;
goto v___jp_1511_;
}
else
{
v___y_1512_ = v___x_1519_;
goto v___jp_1511_;
}
v___jp_1511_:
{
if (v___y_1512_ == 0)
{
lean_object* v_ks_1513_; lean_object* v_vs_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_ks_1513_ = lean_ctor_get(v_newNode_1510_, 0);
lean_inc_ref(v_ks_1513_);
v_vs_1514_ = lean_ctor_get(v_newNode_1510_, 1);
lean_inc_ref(v_vs_1514_);
lean_dec_ref(v_newNode_1510_);
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2);
v___x_1517_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(v_x_1454_, v_ks_1513_, v_vs_1514_, v___x_1515_, v___x_1516_);
lean_dec_ref(v_vs_1514_);
lean_dec_ref(v_ks_1513_);
return v___x_1517_;
}
else
{
return v_newNode_1510_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(size_t v_depth_1525_, lean_object* v_keys_1526_, lean_object* v_vals_1527_, lean_object* v_i_1528_, lean_object* v_entries_1529_){
_start:
{
lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1530_ = lean_array_get_size(v_keys_1526_);
v___x_1531_ = lean_nat_dec_lt(v_i_1528_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_dec(v_i_1528_);
return v_entries_1529_;
}
else
{
lean_object* v_k_1532_; lean_object* v_v_1533_; uint64_t v___x_1534_; size_t v_h_1535_; size_t v___x_1536_; lean_object* v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; size_t v_h_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_k_1532_ = lean_array_fget_borrowed(v_keys_1526_, v_i_1528_);
v_v_1533_ = lean_array_fget_borrowed(v_vals_1527_, v_i_1528_);
v___x_1534_ = l_Lean_instHashableMVarId_hash(v_k_1532_);
v_h_1535_ = lean_uint64_to_usize(v___x_1534_);
v___x_1536_ = ((size_t)5ULL);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_sub(v_depth_1525_, v___x_1538_);
v___x_1540_ = lean_usize_mul(v___x_1536_, v___x_1539_);
v_h_1541_ = lean_usize_shift_right(v_h_1535_, v___x_1540_);
v___x_1542_ = lean_nat_add(v_i_1528_, v___x_1537_);
lean_dec(v_i_1528_);
lean_inc(v_v_1533_);
lean_inc(v_k_1532_);
v___x_1543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_entries_1529_, v_h_1541_, v_depth_1525_, v_k_1532_, v_v_1533_);
v_i_1528_ = v___x_1542_;
v_entries_1529_ = v___x_1543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg___boxed(lean_object* v_depth_1545_, lean_object* v_keys_1546_, lean_object* v_vals_1547_, lean_object* v_i_1548_, lean_object* v_entries_1549_){
_start:
{
size_t v_depth_boxed_1550_; lean_object* v_res_1551_; 
v_depth_boxed_1550_ = lean_unbox_usize(v_depth_1545_);
lean_dec(v_depth_1545_);
v_res_1551_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(v_depth_boxed_1550_, v_keys_1546_, v_vals_1547_, v_i_1548_, v_entries_1549_);
lean_dec_ref(v_vals_1547_);
lean_dec_ref(v_keys_1546_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_){
_start:
{
size_t v_x_158086__boxed_1557_; size_t v_x_158087__boxed_1558_; lean_object* v_res_1559_; 
v_x_158086__boxed_1557_ = lean_unbox_usize(v_x_1553_);
lean_dec(v_x_1553_);
v_x_158087__boxed_1558_ = lean_unbox_usize(v_x_1554_);
lean_dec(v_x_1554_);
v_res_1559_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_x_1552_, v_x_158086__boxed_1557_, v_x_158087__boxed_1558_, v_x_1555_, v_x_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_){
_start:
{
uint64_t v___x_1563_; size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1563_ = l_Lean_instHashableMVarId_hash(v_x_1561_);
v___x_1564_ = lean_uint64_to_usize(v___x_1563_);
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_x_1560_, v___x_1564_, v___x_1565_, v_x_1561_, v_x_1562_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object* v_mvarId_1567_, lean_object* v_val_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v_mctx_1572_; lean_object* v_cache_1573_; lean_object* v_zetaDeltaFVarIds_1574_; lean_object* v_postponed_1575_; lean_object* v_diag_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1604_; 
v___x_1571_ = lean_st_ref_take(v___y_1569_);
v_mctx_1572_ = lean_ctor_get(v___x_1571_, 0);
v_cache_1573_ = lean_ctor_get(v___x_1571_, 1);
v_zetaDeltaFVarIds_1574_ = lean_ctor_get(v___x_1571_, 2);
v_postponed_1575_ = lean_ctor_get(v___x_1571_, 3);
v_diag_1576_ = lean_ctor_get(v___x_1571_, 4);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1578_ = v___x_1571_;
v_isShared_1579_ = v_isSharedCheck_1604_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_diag_1576_);
lean_inc(v_postponed_1575_);
lean_inc(v_zetaDeltaFVarIds_1574_);
lean_inc(v_cache_1573_);
lean_inc(v_mctx_1572_);
lean_dec(v___x_1571_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1604_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_depth_1580_; lean_object* v_levelAssignDepth_1581_; lean_object* v_lmvarCounter_1582_; lean_object* v_mvarCounter_1583_; lean_object* v_lDecls_1584_; lean_object* v_decls_1585_; lean_object* v_userNames_1586_; lean_object* v_lAssignment_1587_; lean_object* v_eAssignment_1588_; lean_object* v_dAssignment_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1603_; 
v_depth_1580_ = lean_ctor_get(v_mctx_1572_, 0);
v_levelAssignDepth_1581_ = lean_ctor_get(v_mctx_1572_, 1);
v_lmvarCounter_1582_ = lean_ctor_get(v_mctx_1572_, 2);
v_mvarCounter_1583_ = lean_ctor_get(v_mctx_1572_, 3);
v_lDecls_1584_ = lean_ctor_get(v_mctx_1572_, 4);
v_decls_1585_ = lean_ctor_get(v_mctx_1572_, 5);
v_userNames_1586_ = lean_ctor_get(v_mctx_1572_, 6);
v_lAssignment_1587_ = lean_ctor_get(v_mctx_1572_, 7);
v_eAssignment_1588_ = lean_ctor_get(v_mctx_1572_, 8);
v_dAssignment_1589_ = lean_ctor_get(v_mctx_1572_, 9);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_mctx_1572_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1591_ = v_mctx_1572_;
v_isShared_1592_ = v_isSharedCheck_1603_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_dAssignment_1589_);
lean_inc(v_eAssignment_1588_);
lean_inc(v_lAssignment_1587_);
lean_inc(v_userNames_1586_);
lean_inc(v_decls_1585_);
lean_inc(v_lDecls_1584_);
lean_inc(v_mvarCounter_1583_);
lean_inc(v_lmvarCounter_1582_);
lean_inc(v_levelAssignDepth_1581_);
lean_inc(v_depth_1580_);
lean_dec(v_mctx_1572_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1603_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(v_eAssignment_1588_, v_mvarId_1567_, v_val_1568_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 8, v___x_1593_);
v___x_1595_ = v___x_1591_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_depth_1580_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_levelAssignDepth_1581_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_lmvarCounter_1582_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_mvarCounter_1583_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_lDecls_1584_);
lean_ctor_set(v_reuseFailAlloc_1602_, 5, v_decls_1585_);
lean_ctor_set(v_reuseFailAlloc_1602_, 6, v_userNames_1586_);
lean_ctor_set(v_reuseFailAlloc_1602_, 7, v_lAssignment_1587_);
lean_ctor_set(v_reuseFailAlloc_1602_, 8, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1602_, 9, v_dAssignment_1589_);
v___x_1595_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1595_);
v___x_1597_ = v___x_1578_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_cache_1573_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_zetaDeltaFVarIds_1574_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_postponed_1575_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_diag_1576_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_st_ref_set(v___y_1569_, v___x_1597_);
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object* v_mvarId_1605_, lean_object* v_val_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_mvarId_1605_, v_val_1606_, v___y_1607_);
lean_dec(v___y_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(lean_object* v_cls_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_options_1616_; uint8_t v_hasTrace_1617_; 
v_options_1616_ = lean_ctor_get(v___y_1613_, 2);
v_hasTrace_1617_ = lean_ctor_get_uint8(v_options_1616_, sizeof(void*)*1);
if (v_hasTrace_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_cls_1610_);
v___x_1618_ = lean_box(v_hasTrace_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
else
{
lean_object* v_inheritedTraceOptions_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_inheritedTraceOptions_1620_ = lean_ctor_get(v___y_1613_, 13);
v___x_1621_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
v___x_1622_ = l_Lean_Name_append(v___x_1621_, v_cls_1610_);
v___x_1623_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1620_, v_options_1616_, v___x_1622_);
lean_dec(v___x_1622_);
v___x_1624_ = lean_box(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0___boxed(lean_object* v_cls_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(lean_object* v_a_1633_, lean_object* v___x_1634_, uint8_t v___x_1635_, lean_object* v___x_1636_, lean_object* v___f_1637_, lean_object* v_____r_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_Meta_mkAuxTheorem(v_a_1633_, v___x_1634_, v___x_1635_, v___x_1644_, v___x_1635_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1636_, v_a_1646_, v___y_1640_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref(v___x_1647_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
v___x_1649_ = lean_apply_6(v___f_1637_, v_a_1648_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, lean_box(0));
return v___x_1649_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v___f_1637_);
v_a_1650_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1647_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1647_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v___f_1637_);
lean_dec(v___x_1636_);
v_a_1658_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1645_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1645_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7___boxed(lean_object* v_a_1666_, lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v___x_1669_, lean_object* v___f_1670_, lean_object* v_____r_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v___x_158343__boxed_1677_; lean_object* v_res_1678_; 
v___x_158343__boxed_1677_ = lean_unbox(v___x_1668_);
v_res_1678_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_1666_, v___x_1667_, v___x_158343__boxed_1677_, v___x_1669_, v___f_1670_, v_____r_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(lean_object* v___x_1679_, lean_object* v_____r_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1679_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6___boxed(lean_object* v___x_1688_, lean_object* v_____r_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_1688_, v_____r_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v___x_1701_, lean_object* v_a_1702_, uint8_t v___x_1703_, uint8_t v___x_1704_, uint8_t v_compile_1705_, uint8_t v_logCompileErrors_1706_, uint8_t v_isMeta_1707_, lean_object* v_____r_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_options_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_options_1714_ = lean_ctor_get(v___y_1711_, 2);
v___x_1715_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1716_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v_a_1702_);
v___x_1717_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1699_, v___x_1700_, v___y_1710_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v___x_1717_, 0);
lean_dec(v_unused_1726_);
v___x_1719_ = v___x_1717_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v___x_1717_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1701_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_a_1727_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1717_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1717_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v___x_1735_; 
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc_ref(v___x_1700_);
v___x_1735_ = lean_infer_type(v___x_1700_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
lean_inc_ref(v_a_1702_);
v___x_1737_ = l_Lean_Meta_isExprDefEq(v_a_1702_, v_a_1736_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; uint8_t v___x_1739_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
v___x_1739_ = lean_unbox(v_a_1738_);
lean_dec(v_a_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_1741_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_1740_, v___y_1712_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___x_1779_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc_n(v_a_1742_, 2);
lean_dec_ref(v___x_1741_);
v___x_1779_ = l_Lean_Meta_mkAuxDefinition(v_a_1742_, v_a_1702_, v___x_1700_, v___x_1703_, v___x_1703_, v___x_1704_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1699_, v_a_1780_, v___y_1710_);
if (lean_obj_tag(v___x_1781_) == 0)
{
uint8_t v___x_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v___x_1781_);
v___x_1782_ = 0;
lean_inc(v_a_1742_);
v___x_1783_ = l_Lean_Meta_setInlineAttribute(v_a_1742_, v___x_1782_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_dec_ref(v___x_1783_);
if (v_isMeta_1707_ == 0)
{
v___y_1765_ = v___y_1711_;
v___y_1766_ = v___y_1712_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1784_; lean_object* v_env_1785_; lean_object* v_nextMacroScope_1786_; lean_object* v_ngen_1787_; lean_object* v_auxDeclNGen_1788_; lean_object* v_traceState_1789_; lean_object* v_messages_1790_; lean_object* v_infoState_1791_; lean_object* v_snapshotTasks_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1817_; 
v___x_1784_ = lean_st_ref_take(v___y_1712_);
v_env_1785_ = lean_ctor_get(v___x_1784_, 0);
v_nextMacroScope_1786_ = lean_ctor_get(v___x_1784_, 1);
v_ngen_1787_ = lean_ctor_get(v___x_1784_, 2);
v_auxDeclNGen_1788_ = lean_ctor_get(v___x_1784_, 3);
v_traceState_1789_ = lean_ctor_get(v___x_1784_, 4);
v_messages_1790_ = lean_ctor_get(v___x_1784_, 6);
v_infoState_1791_ = lean_ctor_get(v___x_1784_, 7);
v_snapshotTasks_1792_ = lean_ctor_get(v___x_1784_, 8);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v___x_1784_, 5);
lean_dec(v_unused_1818_);
v___x_1794_ = v___x_1784_;
v_isShared_1795_ = v_isSharedCheck_1817_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_snapshotTasks_1792_);
lean_inc(v_infoState_1791_);
lean_inc(v_messages_1790_);
lean_inc(v_traceState_1789_);
lean_inc(v_auxDeclNGen_1788_);
lean_inc(v_ngen_1787_);
lean_inc(v_nextMacroScope_1786_);
lean_inc(v_env_1785_);
lean_dec(v___x_1784_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1817_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
lean_inc(v_a_1742_);
v___x_1796_ = l_Lean_markMeta(v_env_1785_, v_a_1742_);
v___x_1797_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 5, v___x_1797_);
lean_ctor_set(v___x_1794_, 0, v___x_1796_);
v___x_1799_ = v___x_1794_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_nextMacroScope_1786_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_ngen_1787_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v_auxDeclNGen_1788_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v_traceState_1789_);
lean_ctor_set(v_reuseFailAlloc_1816_, 5, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1816_, 6, v_messages_1790_);
lean_ctor_set(v_reuseFailAlloc_1816_, 7, v_infoState_1791_);
lean_ctor_set(v_reuseFailAlloc_1816_, 8, v_snapshotTasks_1792_);
v___x_1799_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v_mctx_1802_; lean_object* v_zetaDeltaFVarIds_1803_; lean_object* v_postponed_1804_; lean_object* v_diag_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1814_; 
v___x_1800_ = lean_st_ref_set(v___y_1712_, v___x_1799_);
v___x_1801_ = lean_st_ref_take(v___y_1710_);
v_mctx_1802_ = lean_ctor_get(v___x_1801_, 0);
v_zetaDeltaFVarIds_1803_ = lean_ctor_get(v___x_1801_, 2);
v_postponed_1804_ = lean_ctor_get(v___x_1801_, 3);
v_diag_1805_ = lean_ctor_get(v___x_1801_, 4);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v___x_1801_, 1);
lean_dec(v_unused_1815_);
v___x_1807_ = v___x_1801_;
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_diag_1805_);
lean_inc(v_postponed_1804_);
lean_inc(v_zetaDeltaFVarIds_1803_);
lean_inc(v_mctx_1802_);
lean_dec(v___x_1801_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_mctx_1802_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_zetaDeltaFVarIds_1803_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_postponed_1804_);
lean_ctor_set(v_reuseFailAlloc_1813_, 4, v_diag_1805_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_st_ref_set(v___y_1710_, v___x_1811_);
v___y_1765_ = v___y_1711_;
v___y_1766_ = v___y_1712_;
goto v___jp_1764_;
}
}
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_a_1742_);
v_a_1819_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1783_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1783_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_a_1742_);
v_a_1827_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1781_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1781_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_a_1742_);
lean_dec(v___x_1699_);
v_a_1835_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1779_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1779_);
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
v___jp_1743_:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_enableRealizationsForConst(v_a_1742_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1746_, 0);
lean_dec(v_unused_1755_);
v___x_1748_ = v___x_1746_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v___x_1746_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1701_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
v_a_1756_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1746_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1746_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
v___jp_1764_:
{
if (v_compile_1705_ == 0)
{
v___y_1744_ = v___y_1765_;
v___y_1745_ = v___y_1766_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_mk_empty_array_with_capacity(v___x_1767_);
lean_inc(v_a_1742_);
v___x_1769_ = lean_array_push(v___x_1768_, v_a_1742_);
v___x_1770_ = l_Lean_compileDecls(v___x_1769_, v_logCompileErrors_1706_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec_ref(v___x_1770_);
v___y_1744_ = v___y_1765_;
v___y_1745_ = v___y_1766_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_a_1742_);
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
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref(v_a_1702_);
lean_dec_ref(v___x_1700_);
lean_dec(v___x_1699_);
v_a_1843_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1741_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1741_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
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
lean_object* v___x_1851_; 
lean_dec_ref(v_a_1702_);
v___x_1851_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1699_, v___x_1700_, v___y_1710_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1860_);
v___x_1853_ = v___x_1851_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v___x_1851_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1701_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1851_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1851_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v_a_1702_);
lean_dec_ref(v___x_1700_);
lean_dec(v___x_1699_);
v_a_1869_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1737_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1737_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_a_1702_);
lean_dec_ref(v___x_1700_);
lean_dec(v___x_1699_);
v_a_1877_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1735_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1735_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed(lean_object* v___x_1885_, lean_object* v___x_1886_, lean_object* v___x_1887_, lean_object* v_a_1888_, lean_object* v___x_1889_, lean_object* v___x_1890_, lean_object* v_compile_1891_, lean_object* v_logCompileErrors_1892_, lean_object* v_isMeta_1893_, lean_object* v_____r_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
uint8_t v___x_158466__boxed_1900_; uint8_t v___x_158467__boxed_1901_; uint8_t v_compile_boxed_1902_; uint8_t v_logCompileErrors_boxed_1903_; uint8_t v_isMeta_boxed_1904_; lean_object* v_res_1905_; 
v___x_158466__boxed_1900_ = lean_unbox(v___x_1889_);
v___x_158467__boxed_1901_ = lean_unbox(v___x_1890_);
v_compile_boxed_1902_ = lean_unbox(v_compile_1891_);
v_logCompileErrors_boxed_1903_ = lean_unbox(v_logCompileErrors_1892_);
v_isMeta_boxed_1904_ = lean_unbox(v_isMeta_1893_);
v_res_1905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_1885_, v___x_1886_, v___x_1887_, v_a_1888_, v___x_158466__boxed_1900_, v___x_158467__boxed_1901_, v_compile_boxed_1902_, v_logCompileErrors_boxed_1903_, v_isMeta_boxed_1904_, v_____r_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(lean_object* v_snd_1906_, lean_object* v_a_1907_, lean_object* v___x_1908_, lean_object* v_____r_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_fieldName_1915_; lean_object* v___x_1916_; 
v_fieldName_1915_ = lean_ctor_get(v_snd_1906_, 0);
lean_inc(v_fieldName_1915_);
lean_dec_ref(v_snd_1906_);
v___x_1916_ = l_Lean_Meta_mkProjection(v_a_1907_, v_fieldName_1915_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1908_, v_a_1917_, v___y_1911_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1918_, 0);
lean_dec(v_unused_1927_);
v___x_1920_ = v___x_1918_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_dec(v___x_1918_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_box(0);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1918_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1918_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v___x_1908_);
v_a_1936_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1916_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1916_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2___boxed(lean_object* v_snd_1944_, lean_object* v_a_1945_, lean_object* v___x_1946_, lean_object* v_____r_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_1944_, v_a_1945_, v___x_1946_, v_____r_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1953_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__0));
v___x_1956_ = l_Lean_stringToMessageData(v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__2));
v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
return v___x_1959_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__4));
v___x_1962_ = l_Lean_stringToMessageData(v___x_1961_);
return v___x_1962_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__7(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__6));
v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(lean_object* v_val_1966_, lean_object* v_fst_1967_, lean_object* v_expectedType_1968_, lean_object* v___f_1969_, lean_object* v___f_1970_, lean_object* v___x_1971_, lean_object* v_cls_1972_, lean_object* v_snd_1973_, lean_object* v___x_1974_, lean_object* v_____r_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___y_1982_; uint8_t v___y_1983_; lean_object* v_a_2016_; lean_object* v___y_2020_; lean_object* v___x_2033_; 
v___x_2033_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_val_1966_, v_fst_1967_, v_expectedType_1968_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
if (lean_obj_tag(v_a_2034_) == 1)
{
lean_object* v_val_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_val_2035_ = lean_ctor_get(v_a_2034_, 0);
lean_inc(v_val_2035_);
lean_dec_ref(v_a_2034_);
v___x_2036_ = lean_box(0);
v___x_2037_ = l_Lean_Meta_trySynthInstance(v_val_2035_, v___x_2036_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2037_);
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_a_2039_ = lean_ctor_get(v_a_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_inc_ref(v___f_1969_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_2040_ = lean_apply_5(v___f_1969_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; uint8_t v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref(v___x_2040_);
v___x_2042_ = lean_unbox(v_a_2041_);
lean_dec(v_a_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
v___x_2043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_1973_, v_a_2039_, v___x_1974_, v___x_1971_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
v___y_2020_ = v___x_2043_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2044_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__5);
lean_inc(v_a_2039_);
v___x_2045_ = l_Lean_MessageData_ofExpr(v_a_2039_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_inc(v_cls_1972_);
v___x_2049_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1972_, v___x_2048_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_1973_, v_a_2039_, v___x_1974_, v_a_2050_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
v___y_2020_ = v___x_2051_;
goto v___jp_2019_;
}
else
{
lean_object* v_a_2052_; 
lean_dec(v_a_2039_);
lean_dec(v___x_1974_);
lean_dec_ref(v_snd_1973_);
v_a_2052_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2049_);
v_a_2016_ = v_a_2052_;
goto v___jp_2015_;
}
}
}
else
{
lean_object* v_a_2053_; 
lean_dec(v_a_2039_);
lean_dec(v___x_1974_);
lean_dec_ref(v_snd_1973_);
v_a_2053_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2040_);
v_a_2016_ = v_a_2053_;
goto v___jp_2015_;
}
}
else
{
lean_object* v_options_2054_; uint8_t v_hasTrace_2055_; 
lean_dec(v_a_2038_);
lean_dec(v___x_1974_);
lean_dec_ref(v_snd_1973_);
v_options_2054_ = lean_ctor_get(v___y_1978_, 2);
v_hasTrace_2055_ = lean_ctor_get_uint8(v_options_2054_, sizeof(void*)*1);
if (v_hasTrace_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1969_);
lean_dec(v_fst_1967_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_2056_ = lean_apply_6(v___f_1970_, v___x_1971_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_2056_;
}
else
{
lean_object* v_inheritedTraceOptions_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_inheritedTraceOptions_2057_ = lean_ctor_get(v___y_1978_, 13);
v___x_2058_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
lean_inc(v_cls_1972_);
v___x_2059_ = l_Lean_Name_append(v___x_2058_, v_cls_1972_);
v___x_2060_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2057_, v_options_2054_, v___x_2059_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1969_);
lean_dec(v_fst_1967_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_2061_ = lean_apply_6(v___f_1970_, v___x_1971_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2062_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__7);
lean_inc(v_fst_1967_);
v___x_2063_ = l_Lean_MessageData_ofName(v_fst_1967_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
lean_inc(v_cls_1972_);
v___x_2067_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1972_, v___x_2066_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; 
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1969_);
lean_dec(v_fst_1967_);
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_2069_ = lean_apply_6(v___f_1970_, v_a_2068_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_2069_;
}
else
{
lean_object* v_a_2070_; 
v_a_2070_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2067_);
v_a_2016_ = v_a_2070_;
goto v___jp_2015_;
}
}
}
}
}
else
{
lean_object* v_a_2071_; 
lean_dec(v___x_1974_);
lean_dec_ref(v_snd_1973_);
v_a_2071_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2037_);
v_a_2016_ = v_a_2071_;
goto v___jp_2015_;
}
}
else
{
lean_object* v___x_2072_; 
lean_dec(v_a_2034_);
lean_dec(v___x_1974_);
lean_dec_ref(v_snd_1973_);
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1969_);
lean_dec(v_fst_1967_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_2072_ = lean_apply_6(v___f_1970_, v___x_1971_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_2072_;
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v___x_1974_);
lean_dec_ref(v_snd_1973_);
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1970_);
lean_dec_ref(v___f_1969_);
lean_dec(v_fst_1967_);
v_a_2073_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2033_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2033_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
v___jp_1981_:
{
if (v___y_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_1984_ = lean_apply_5(v___f_1969_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; uint8_t v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
lean_dec_ref(v___y_1982_);
lean_dec(v_cls_1972_);
lean_dec(v_fst_1967_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_1987_ = lean_apply_6(v___f_1970_, v___x_1971_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1988_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__1);
v___x_1989_ = l_Lean_MessageData_ofName(v_fst_1967_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_Exception_toMessageData(v___y_1982_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1972_, v___x_1994_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v___x_1995_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_1997_ = lean_apply_6(v___f_1970_, v_a_1996_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_1997_;
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v___f_1970_);
v_a_1998_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1995_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1995_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref(v___y_1982_);
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1970_);
lean_dec(v_fst_1967_);
v_a_2006_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1984_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1984_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v___x_2014_; 
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1970_);
lean_dec_ref(v___f_1969_);
lean_dec(v_fst_1967_);
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___y_1982_);
return v___x_2014_;
}
}
v___jp_2015_:
{
uint8_t v___x_2017_; 
v___x_2017_ = l_Lean_Exception_isInterrupt(v_a_2016_);
if (v___x_2017_ == 0)
{
uint8_t v___x_2018_; 
lean_inc_ref(v_a_2016_);
v___x_2018_ = l_Lean_Exception_isRuntime(v_a_2016_);
v___y_1982_ = v_a_2016_;
v___y_1983_ = v___x_2018_;
goto v___jp_1981_;
}
else
{
v___y_1982_ = v_a_2016_;
v___y_1983_ = v___x_2017_;
goto v___jp_1981_;
}
}
v___jp_2019_:
{
if (lean_obj_tag(v___y_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_cls_1972_);
lean_dec_ref(v___f_1969_);
lean_dec(v_fst_1967_);
v_a_2021_ = lean_ctor_get(v___y_2020_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___y_2020_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2023_ = v___y_2020_;
v_isShared_2024_ = v_isSharedCheck_2031_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___y_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2031_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
if (lean_obj_tag(v_a_2021_) == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_dec_ref(v___f_1970_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_1971_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2025_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
lean_del_object(v___x_2023_);
v_a_2029_ = lean_ctor_get(v_a_2021_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v_a_2021_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_2030_ = lean_apply_6(v___f_1970_, v_a_2029_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_2030_;
}
}
}
else
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v___y_2020_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___y_2020_);
v_a_2016_ = v_a_2032_;
goto v___jp_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___boxed(lean_object* v_val_2081_, lean_object* v_fst_2082_, lean_object* v_expectedType_2083_, lean_object* v___f_2084_, lean_object* v___f_2085_, lean_object* v___x_2086_, lean_object* v_cls_2087_, lean_object* v_snd_2088_, lean_object* v___x_2089_, lean_object* v_____r_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_2081_, v_fst_2082_, v_expectedType_2083_, v___f_2084_, v___f_2085_, v___x_2086_, v_cls_2087_, v_snd_2088_, v___x_2089_, v_____r_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v_a_2100_, uint8_t v___x_2101_, uint8_t v_compile_2102_, uint8_t v_logCompileErrors_2103_, uint8_t v_isMeta_2104_, lean_object* v_____r_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_options_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_options_2111_ = lean_ctor_get(v___y_2108_, 2);
v___x_2112_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2113_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref(v_a_2100_);
v___x_2114_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2097_, v___x_2098_, v___y_2107_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2122_; 
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v___x_2114_, 0);
lean_dec(v_unused_2123_);
v___x_2116_ = v___x_2114_;
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
else
{
lean_dec(v___x_2114_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2099_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2118_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
v_a_2124_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2114_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2114_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
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
else
{
lean_object* v___x_2132_; 
lean_inc(v___y_2109_);
lean_inc_ref(v___y_2108_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc_ref(v___x_2098_);
v___x_2132_ = lean_infer_type(v___x_2098_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
lean_inc_ref(v_a_2100_);
v___x_2134_ = l_Lean_Meta_isExprDefEq(v_a_2100_, v_a_2133_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; uint8_t v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = lean_unbox(v_a_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_2138_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2137_, v___y_2109_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2162_; lean_object* v___y_2163_; uint8_t v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc_n(v_a_2139_, 2);
lean_dec_ref(v___x_2138_);
v___x_2176_ = lean_unbox(v_a_2135_);
v___x_2177_ = lean_unbox(v_a_2135_);
lean_dec(v_a_2135_);
v___x_2178_ = l_Lean_Meta_mkAuxDefinition(v_a_2139_, v_a_2100_, v___x_2098_, v___x_2176_, v___x_2177_, v___x_2101_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2097_, v_a_2179_, v___y_2107_);
if (lean_obj_tag(v___x_2180_) == 0)
{
uint8_t v___x_2181_; lean_object* v___x_2182_; 
lean_dec_ref(v___x_2180_);
v___x_2181_ = 0;
lean_inc(v_a_2139_);
v___x_2182_ = l_Lean_Meta_setInlineAttribute(v_a_2139_, v___x_2181_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_dec_ref(v___x_2182_);
if (v_isMeta_2104_ == 0)
{
v___y_2162_ = v___y_2108_;
v___y_2163_ = v___y_2109_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2183_; lean_object* v_env_2184_; lean_object* v_nextMacroScope_2185_; lean_object* v_ngen_2186_; lean_object* v_auxDeclNGen_2187_; lean_object* v_traceState_2188_; lean_object* v_messages_2189_; lean_object* v_infoState_2190_; lean_object* v_snapshotTasks_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2216_; 
v___x_2183_ = lean_st_ref_take(v___y_2109_);
v_env_2184_ = lean_ctor_get(v___x_2183_, 0);
v_nextMacroScope_2185_ = lean_ctor_get(v___x_2183_, 1);
v_ngen_2186_ = lean_ctor_get(v___x_2183_, 2);
v_auxDeclNGen_2187_ = lean_ctor_get(v___x_2183_, 3);
v_traceState_2188_ = lean_ctor_get(v___x_2183_, 4);
v_messages_2189_ = lean_ctor_get(v___x_2183_, 6);
v_infoState_2190_ = lean_ctor_get(v___x_2183_, 7);
v_snapshotTasks_2191_ = lean_ctor_get(v___x_2183_, 8);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2183_, 5);
lean_dec(v_unused_2217_);
v___x_2193_ = v___x_2183_;
v_isShared_2194_ = v_isSharedCheck_2216_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_snapshotTasks_2191_);
lean_inc(v_infoState_2190_);
lean_inc(v_messages_2189_);
lean_inc(v_traceState_2188_);
lean_inc(v_auxDeclNGen_2187_);
lean_inc(v_ngen_2186_);
lean_inc(v_nextMacroScope_2185_);
lean_inc(v_env_2184_);
lean_dec(v___x_2183_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2216_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
lean_inc(v_a_2139_);
v___x_2195_ = l_Lean_markMeta(v_env_2184_, v_a_2139_);
v___x_2196_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 5, v___x_2196_);
lean_ctor_set(v___x_2193_, 0, v___x_2195_);
v___x_2198_ = v___x_2193_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_nextMacroScope_2185_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_ngen_2186_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_auxDeclNGen_2187_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_traceState_2188_);
lean_ctor_set(v_reuseFailAlloc_2215_, 5, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2215_, 6, v_messages_2189_);
lean_ctor_set(v_reuseFailAlloc_2215_, 7, v_infoState_2190_);
lean_ctor_set(v_reuseFailAlloc_2215_, 8, v_snapshotTasks_2191_);
v___x_2198_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v_mctx_2201_; lean_object* v_zetaDeltaFVarIds_2202_; lean_object* v_postponed_2203_; lean_object* v_diag_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2213_; 
v___x_2199_ = lean_st_ref_set(v___y_2109_, v___x_2198_);
v___x_2200_ = lean_st_ref_take(v___y_2107_);
v_mctx_2201_ = lean_ctor_get(v___x_2200_, 0);
v_zetaDeltaFVarIds_2202_ = lean_ctor_get(v___x_2200_, 2);
v_postponed_2203_ = lean_ctor_get(v___x_2200_, 3);
v_diag_2204_ = lean_ctor_get(v___x_2200_, 4);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v___x_2200_, 1);
lean_dec(v_unused_2214_);
v___x_2206_ = v___x_2200_;
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_diag_2204_);
lean_inc(v_postponed_2203_);
lean_inc(v_zetaDeltaFVarIds_2202_);
lean_inc(v_mctx_2201_);
lean_dec(v___x_2200_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 1, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_mctx_2201_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_zetaDeltaFVarIds_2202_);
lean_ctor_set(v_reuseFailAlloc_2212_, 3, v_postponed_2203_);
lean_ctor_set(v_reuseFailAlloc_2212_, 4, v_diag_2204_);
v___x_2210_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_st_ref_set(v___y_2107_, v___x_2210_);
v___y_2162_ = v___y_2108_;
v___y_2163_ = v___y_2109_;
goto v___jp_2161_;
}
}
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_a_2139_);
v_a_2218_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2182_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2182_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_a_2139_);
v_a_2226_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2180_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2180_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_a_2139_);
lean_dec(v___x_2097_);
v_a_2234_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2178_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2178_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
v___jp_2140_:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_enableRealizationsForConst(v_a_2139_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2151_; 
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2143_, 0);
lean_dec(v_unused_2152_);
v___x_2145_ = v___x_2143_;
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
else
{
lean_dec(v___x_2143_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2099_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2147_);
v___x_2149_ = v___x_2145_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_a_2153_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2143_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2143_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
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
v___jp_2161_:
{
if (v_compile_2102_ == 0)
{
v___y_2141_ = v___y_2162_;
v___y_2142_ = v___y_2163_;
goto v___jp_2140_;
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_mk_empty_array_with_capacity(v___x_2164_);
lean_inc(v_a_2139_);
v___x_2166_ = lean_array_push(v___x_2165_, v_a_2139_);
v___x_2167_ = l_Lean_compileDecls(v___x_2166_, v_logCompileErrors_2103_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_dec_ref(v___x_2167_);
v___y_2141_ = v___y_2162_;
v___y_2142_ = v___y_2163_;
goto v___jp_2140_;
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_a_2139_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2100_);
lean_dec_ref(v___x_2098_);
lean_dec(v___x_2097_);
v_a_2242_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2138_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2138_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v___x_2250_; 
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2100_);
v___x_2250_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2097_, v___x_2098_, v___y_2107_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2258_; 
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; 
v_unused_2259_ = lean_ctor_get(v___x_2250_, 0);
lean_dec(v_unused_2259_);
v___x_2252_ = v___x_2250_;
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
else
{
lean_dec(v___x_2250_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2099_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2250_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2250_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_a_2100_);
lean_dec_ref(v___x_2098_);
lean_dec(v___x_2097_);
v_a_2268_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2134_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2134_);
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
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_a_2100_);
lean_dec_ref(v___x_2098_);
lean_dec(v___x_2097_);
v_a_2276_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2132_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2132_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1___boxed(lean_object* v___x_2284_, lean_object* v___x_2285_, lean_object* v___x_2286_, lean_object* v_a_2287_, lean_object* v___x_2288_, lean_object* v_compile_2289_, lean_object* v_logCompileErrors_2290_, lean_object* v_isMeta_2291_, lean_object* v_____r_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v___x_159205__boxed_2298_; uint8_t v_compile_boxed_2299_; uint8_t v_logCompileErrors_boxed_2300_; uint8_t v_isMeta_boxed_2301_; lean_object* v_res_2302_; 
v___x_159205__boxed_2298_ = lean_unbox(v___x_2288_);
v_compile_boxed_2299_ = lean_unbox(v_compile_2289_);
v_logCompileErrors_boxed_2300_ = lean_unbox(v_logCompileErrors_2290_);
v_isMeta_boxed_2301_ = lean_unbox(v_isMeta_2291_);
v_res_2302_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(v___x_2284_, v___x_2285_, v___x_2286_, v_a_2287_, v___x_159205__boxed_2298_, v_compile_boxed_2299_, v_logCompileErrors_boxed_2300_, v_isMeta_boxed_2301_, v_____r_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(lean_object* v___x_2303_, lean_object* v_a_2304_, lean_object* v_____r_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2303_, v_a_2304_, v___y_2307_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2319_; 
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v___x_2311_, 0);
lean_dec(v_unused_2320_);
v___x_2313_ = v___x_2311_;
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
else
{
lean_dec(v___x_2311_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_box(0);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2315_);
v___x_2317_ = v___x_2313_;
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
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
v_a_2321_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2311_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2311_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5___boxed(lean_object* v___x_2329_, lean_object* v_a_2330_, lean_object* v_____r_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_2329_, v_a_2330_, v_____r_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(lean_object* v_opts_2338_, lean_object* v_opt_2339_){
_start:
{
lean_object* v_name_2340_; lean_object* v_defValue_2341_; lean_object* v_map_2342_; lean_object* v___x_2343_; 
v_name_2340_ = lean_ctor_get(v_opt_2339_, 0);
v_defValue_2341_ = lean_ctor_get(v_opt_2339_, 1);
v_map_2342_ = lean_ctor_get(v_opts_2338_, 0);
v___x_2343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2342_, v_name_2340_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_inc(v_defValue_2341_);
return v_defValue_2341_;
}
else
{
lean_object* v_val_2344_; 
v_val_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_val_2344_);
lean_dec_ref(v___x_2343_);
if (lean_obj_tag(v_val_2344_) == 3)
{
lean_object* v_v_2345_; 
v_v_2345_ = lean_ctor_get(v_val_2344_, 0);
lean_inc(v_v_2345_);
lean_dec_ref(v_val_2344_);
return v_v_2345_;
}
else
{
lean_dec(v_val_2344_);
lean_inc(v_defValue_2341_);
return v_defValue_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18___boxed(lean_object* v_opts_2346_, lean_object* v_opt_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(v_opts_2346_, v_opt_2347_);
lean_dec_ref(v_opt_2347_);
lean_dec_ref(v_opts_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(lean_object* v_x_2349_){
_start:
{
if (lean_obj_tag(v_x_2349_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_a_2351_ = lean_ctor_get(v_x_2349_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_x_2349_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v_x_2349_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v_x_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 1);
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
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
v_a_2359_ = lean_ctor_get(v_x_2349_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_x_2349_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v_x_2349_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v_x_2349_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set_tag(v___x_2361_, 0);
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg___boxed(lean_object* v_x_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_x_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(size_t v_sz_2370_, size_t v_i_2371_, lean_object* v_bs_2372_){
_start:
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_usize_dec_lt(v_i_2371_, v_sz_2370_);
if (v___x_2373_ == 0)
{
return v_bs_2372_;
}
else
{
lean_object* v_v_2374_; lean_object* v_msg_2375_; lean_object* v___x_2376_; lean_object* v_bs_x27_2377_; size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
v_v_2374_ = lean_array_uget_borrowed(v_bs_2372_, v_i_2371_);
v_msg_2375_ = lean_ctor_get(v_v_2374_, 1);
lean_inc_ref(v_msg_2375_);
v___x_2376_ = lean_unsigned_to_nat(0u);
v_bs_x27_2377_ = lean_array_uset(v_bs_2372_, v_i_2371_, v___x_2376_);
v___x_2378_ = ((size_t)1ULL);
v___x_2379_ = lean_usize_add(v_i_2371_, v___x_2378_);
v___x_2380_ = lean_array_uset(v_bs_x27_2377_, v_i_2371_, v_msg_2375_);
v_i_2371_ = v___x_2379_;
v_bs_2372_ = v___x_2380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19___boxed(lean_object* v_sz_2382_, lean_object* v_i_2383_, lean_object* v_bs_2384_){
_start:
{
size_t v_sz_boxed_2385_; size_t v_i_boxed_2386_; lean_object* v_res_2387_; 
v_sz_boxed_2385_ = lean_unbox_usize(v_sz_2382_);
lean_dec(v_sz_2382_);
v_i_boxed_2386_ = lean_unbox_usize(v_i_2383_);
lean_dec(v_i_2383_);
v_res_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(v_sz_boxed_2385_, v_i_boxed_2386_, v_bs_2384_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(lean_object* v_oldTraces_2388_, lean_object* v_data_2389_, lean_object* v_ref_2390_, lean_object* v_msg_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_fileName_2397_; lean_object* v_fileMap_2398_; lean_object* v_options_2399_; lean_object* v_currRecDepth_2400_; lean_object* v_maxRecDepth_2401_; lean_object* v_ref_2402_; lean_object* v_currNamespace_2403_; lean_object* v_openDecls_2404_; lean_object* v_initHeartbeats_2405_; lean_object* v_maxHeartbeats_2406_; lean_object* v_quotContext_2407_; lean_object* v_currMacroScope_2408_; uint8_t v_diag_2409_; lean_object* v_cancelTk_x3f_2410_; uint8_t v_suppressElabErrors_2411_; lean_object* v_inheritedTraceOptions_2412_; lean_object* v___x_2413_; lean_object* v_traceState_2414_; lean_object* v_traces_2415_; lean_object* v_ref_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; size_t v_sz_2419_; size_t v___x_2420_; lean_object* v___x_2421_; lean_object* v_msg_2422_; lean_object* v___x_2423_; lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2461_; 
v_fileName_2397_ = lean_ctor_get(v___y_2394_, 0);
v_fileMap_2398_ = lean_ctor_get(v___y_2394_, 1);
v_options_2399_ = lean_ctor_get(v___y_2394_, 2);
v_currRecDepth_2400_ = lean_ctor_get(v___y_2394_, 3);
v_maxRecDepth_2401_ = lean_ctor_get(v___y_2394_, 4);
v_ref_2402_ = lean_ctor_get(v___y_2394_, 5);
v_currNamespace_2403_ = lean_ctor_get(v___y_2394_, 6);
v_openDecls_2404_ = lean_ctor_get(v___y_2394_, 7);
v_initHeartbeats_2405_ = lean_ctor_get(v___y_2394_, 8);
v_maxHeartbeats_2406_ = lean_ctor_get(v___y_2394_, 9);
v_quotContext_2407_ = lean_ctor_get(v___y_2394_, 10);
v_currMacroScope_2408_ = lean_ctor_get(v___y_2394_, 11);
v_diag_2409_ = lean_ctor_get_uint8(v___y_2394_, sizeof(void*)*14);
v_cancelTk_x3f_2410_ = lean_ctor_get(v___y_2394_, 12);
v_suppressElabErrors_2411_ = lean_ctor_get_uint8(v___y_2394_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2412_ = lean_ctor_get(v___y_2394_, 13);
v___x_2413_ = lean_st_ref_get(v___y_2395_);
v_traceState_2414_ = lean_ctor_get(v___x_2413_, 4);
lean_inc_ref(v_traceState_2414_);
lean_dec(v___x_2413_);
v_traces_2415_ = lean_ctor_get(v_traceState_2414_, 0);
lean_inc_ref(v_traces_2415_);
lean_dec_ref(v_traceState_2414_);
v_ref_2416_ = l_Lean_replaceRef(v_ref_2390_, v_ref_2402_);
lean_inc_ref(v_inheritedTraceOptions_2412_);
lean_inc(v_cancelTk_x3f_2410_);
lean_inc(v_currMacroScope_2408_);
lean_inc(v_quotContext_2407_);
lean_inc(v_maxHeartbeats_2406_);
lean_inc(v_initHeartbeats_2405_);
lean_inc(v_openDecls_2404_);
lean_inc(v_currNamespace_2403_);
lean_inc(v_maxRecDepth_2401_);
lean_inc(v_currRecDepth_2400_);
lean_inc_ref(v_options_2399_);
lean_inc_ref(v_fileMap_2398_);
lean_inc_ref(v_fileName_2397_);
v___x_2417_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2417_, 0, v_fileName_2397_);
lean_ctor_set(v___x_2417_, 1, v_fileMap_2398_);
lean_ctor_set(v___x_2417_, 2, v_options_2399_);
lean_ctor_set(v___x_2417_, 3, v_currRecDepth_2400_);
lean_ctor_set(v___x_2417_, 4, v_maxRecDepth_2401_);
lean_ctor_set(v___x_2417_, 5, v_ref_2416_);
lean_ctor_set(v___x_2417_, 6, v_currNamespace_2403_);
lean_ctor_set(v___x_2417_, 7, v_openDecls_2404_);
lean_ctor_set(v___x_2417_, 8, v_initHeartbeats_2405_);
lean_ctor_set(v___x_2417_, 9, v_maxHeartbeats_2406_);
lean_ctor_set(v___x_2417_, 10, v_quotContext_2407_);
lean_ctor_set(v___x_2417_, 11, v_currMacroScope_2408_);
lean_ctor_set(v___x_2417_, 12, v_cancelTk_x3f_2410_);
lean_ctor_set(v___x_2417_, 13, v_inheritedTraceOptions_2412_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*14, v_diag_2409_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*14 + 1, v_suppressElabErrors_2411_);
v___x_2418_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2415_);
lean_dec_ref(v_traces_2415_);
v_sz_2419_ = lean_array_size(v___x_2418_);
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(v_sz_2419_, v___x_2420_, v___x_2418_);
v_msg_2422_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2422_, 0, v_data_2389_);
lean_ctor_set(v_msg_2422_, 1, v_msg_2391_);
lean_ctor_set(v_msg_2422_, 2, v___x_2421_);
v___x_2423_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_2422_, v___y_2392_, v___y_2393_, v___x_2417_, v___y_2395_);
lean_dec_ref(v___x_2417_);
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2461_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2461_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v_traceState_2429_; lean_object* v_env_2430_; lean_object* v_nextMacroScope_2431_; lean_object* v_ngen_2432_; lean_object* v_auxDeclNGen_2433_; lean_object* v_cache_2434_; lean_object* v_messages_2435_; lean_object* v_infoState_2436_; lean_object* v_snapshotTasks_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2460_; 
v___x_2428_ = lean_st_ref_take(v___y_2395_);
v_traceState_2429_ = lean_ctor_get(v___x_2428_, 4);
v_env_2430_ = lean_ctor_get(v___x_2428_, 0);
v_nextMacroScope_2431_ = lean_ctor_get(v___x_2428_, 1);
v_ngen_2432_ = lean_ctor_get(v___x_2428_, 2);
v_auxDeclNGen_2433_ = lean_ctor_get(v___x_2428_, 3);
v_cache_2434_ = lean_ctor_get(v___x_2428_, 5);
v_messages_2435_ = lean_ctor_get(v___x_2428_, 6);
v_infoState_2436_ = lean_ctor_get(v___x_2428_, 7);
v_snapshotTasks_2437_ = lean_ctor_get(v___x_2428_, 8);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2439_ = v___x_2428_;
v_isShared_2440_ = v_isSharedCheck_2460_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_snapshotTasks_2437_);
lean_inc(v_infoState_2436_);
lean_inc(v_messages_2435_);
lean_inc(v_cache_2434_);
lean_inc(v_traceState_2429_);
lean_inc(v_auxDeclNGen_2433_);
lean_inc(v_ngen_2432_);
lean_inc(v_nextMacroScope_2431_);
lean_inc(v_env_2430_);
lean_dec(v___x_2428_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2460_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
uint64_t v_tid_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2458_; 
v_tid_2441_ = lean_ctor_get_uint64(v_traceState_2429_, sizeof(void*)*1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_traceState_2429_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v_traceState_2429_, 0);
lean_dec(v_unused_2459_);
v___x_2443_ = v_traceState_2429_;
v_isShared_2444_ = v_isSharedCheck_2458_;
goto v_resetjp_2442_;
}
else
{
lean_dec(v_traceState_2429_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2458_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v_ref_2390_);
lean_ctor_set(v___x_2445_, 1, v_a_2424_);
v___x_2446_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2388_, v___x_2445_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2446_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2446_);
lean_ctor_set_uint64(v_reuseFailAlloc_2457_, sizeof(void*)*1, v_tid_2441_);
v___x_2448_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 4, v___x_2448_);
v___x_2450_ = v___x_2439_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_env_2430_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_nextMacroScope_2431_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_ngen_2432_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_auxDeclNGen_2433_);
lean_ctor_set(v_reuseFailAlloc_2456_, 4, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2456_, 5, v_cache_2434_);
lean_ctor_set(v_reuseFailAlloc_2456_, 6, v_messages_2435_);
lean_ctor_set(v_reuseFailAlloc_2456_, 7, v_infoState_2436_);
lean_ctor_set(v_reuseFailAlloc_2456_, 8, v_snapshotTasks_2437_);
v___x_2450_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2451_ = lean_st_ref_set(v___y_2395_, v___x_2450_);
v___x_2452_ = lean_box(0);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2452_);
v___x_2454_ = v___x_2426_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16___boxed(lean_object* v_oldTraces_2462_, lean_object* v_data_2463_, lean_object* v_ref_2464_, lean_object* v_msg_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(v_oldTraces_2462_, v_data_2463_, v_ref_2464_, v_msg_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
return v_res_2471_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(lean_object* v_e_2472_){
_start:
{
if (lean_obj_tag(v_e_2472_) == 0)
{
uint8_t v___x_2473_; 
v___x_2473_ = 2;
return v___x_2473_;
}
else
{
uint8_t v___x_2474_; 
v___x_2474_ = 0;
return v___x_2474_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15___boxed(lean_object* v_e_2475_){
_start:
{
uint8_t v_res_2476_; lean_object* v_r_2477_; 
v_res_2476_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(v_e_2475_);
lean_dec_ref(v_e_2475_);
v_r_2477_ = lean_box(v_res_2476_);
return v_r_2477_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4(void){
_start:
{
lean_object* v___x_2484_; double v___x_2485_; 
v___x_2484_ = lean_unsigned_to_nat(1000u);
v___x_2485_ = lean_float_of_nat(v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(lean_object* v_cls_2486_, uint8_t v_collapsed_2487_, lean_object* v_tag_2488_, lean_object* v_opts_2489_, uint8_t v_clsEnabled_2490_, lean_object* v_oldTraces_2491_, lean_object* v_msg_2492_, lean_object* v_resStartStop_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_fst_2499_; lean_object* v_snd_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2598_; 
v_fst_2499_ = lean_ctor_get(v_resStartStop_2493_, 0);
v_snd_2500_ = lean_ctor_get(v_resStartStop_2493_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_resStartStop_2493_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2502_ = v_resStartStop_2493_;
v_isShared_2503_ = v_isSharedCheck_2598_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_snd_2500_);
lean_inc(v_fst_2499_);
lean_dec(v_resStartStop_2493_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2598_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v_data_2507_; lean_object* v_fst_2518_; lean_object* v_snd_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2597_; 
v_fst_2518_ = lean_ctor_get(v_snd_2500_, 0);
v_snd_2519_ = lean_ctor_get(v_snd_2500_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_snd_2500_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2521_ = v_snd_2500_;
v_isShared_2522_ = v_isSharedCheck_2597_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_snd_2519_);
lean_inc(v_fst_2518_);
lean_dec(v_snd_2500_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2597_;
goto v_resetjp_2520_;
}
v___jp_2504_:
{
lean_object* v___x_2508_; 
lean_inc(v___y_2506_);
v___x_2508_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(v_oldTraces_2491_, v_data_2507_, v___y_2506_, v___y_2505_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2509_; 
lean_dec_ref(v___x_2508_);
v___x_2509_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_fst_2499_);
return v___x_2509_;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v_fst_2499_);
v_a_2510_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2508_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; uint8_t v___x_2524_; lean_object* v___y_2526_; lean_object* v_a_2527_; uint8_t v___y_2551_; double v___y_2582_; 
v___x_2523_ = l_Lean_trace_profiler;
v___x_2524_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2489_, v___x_2523_);
if (v___x_2524_ == 0)
{
v___y_2551_ = v___x_2524_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2588_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2489_, v___x_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; double v___x_2591_; double v___x_2592_; double v___x_2593_; 
v___x_2589_ = l_Lean_trace_profiler_threshold;
v___x_2590_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(v_opts_2489_, v___x_2589_);
v___x_2591_ = lean_float_of_nat(v___x_2590_);
v___x_2592_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4);
v___x_2593_ = lean_float_div(v___x_2591_, v___x_2592_);
v___y_2582_ = v___x_2593_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; double v___x_2596_; 
v___x_2594_ = l_Lean_trace_profiler_threshold;
v___x_2595_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(v_opts_2489_, v___x_2594_);
v___x_2596_ = lean_float_of_nat(v___x_2595_);
v___y_2582_ = v___x_2596_;
goto v___jp_2581_;
}
}
v___jp_2525_:
{
uint8_t v_result_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v_result_2528_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(v_fst_2499_);
v___x_2529_ = l_Lean_TraceResult_toEmoji(v_result_2528_);
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
v___x_2531_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1);
if (v_isShared_2522_ == 0)
{
lean_ctor_set_tag(v___x_2521_, 7);
lean_ctor_set(v___x_2521_, 1, v___x_2531_);
lean_ctor_set(v___x_2521_, 0, v___x_2530_);
v___x_2533_ = v___x_2521_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v_m_2535_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 7);
lean_ctor_set(v___x_2502_, 1, v_a_2527_);
lean_ctor_set(v___x_2502_, 0, v___x_2533_);
v_m_2535_ = v___x_2502_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_a_2527_);
v_m_2535_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; double v___x_2538_; lean_object* v_data_2539_; 
v___x_2536_ = lean_box(v_result_2528_);
v___x_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
v___x_2538_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
lean_inc_ref(v_tag_2488_);
lean_inc_ref(v___x_2537_);
lean_inc(v_cls_2486_);
v_data_2539_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2539_, 0, v_cls_2486_);
lean_ctor_set(v_data_2539_, 1, v___x_2537_);
lean_ctor_set(v_data_2539_, 2, v_tag_2488_);
lean_ctor_set_float(v_data_2539_, sizeof(void*)*3, v___x_2538_);
lean_ctor_set_float(v_data_2539_, sizeof(void*)*3 + 8, v___x_2538_);
lean_ctor_set_uint8(v_data_2539_, sizeof(void*)*3 + 16, v_collapsed_2487_);
if (v___x_2524_ == 0)
{
lean_dec_ref(v___x_2537_);
lean_dec(v_snd_2519_);
lean_dec(v_fst_2518_);
lean_dec_ref(v_tag_2488_);
lean_dec(v_cls_2486_);
v___y_2505_ = v_m_2535_;
v___y_2506_ = v___y_2526_;
v_data_2507_ = v_data_2539_;
goto v___jp_2504_;
}
else
{
lean_object* v_data_2540_; double v___x_2541_; double v___x_2542_; 
lean_dec_ref(v_data_2539_);
v_data_2540_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2540_, 0, v_cls_2486_);
lean_ctor_set(v_data_2540_, 1, v___x_2537_);
lean_ctor_set(v_data_2540_, 2, v_tag_2488_);
v___x_2541_ = lean_unbox_float(v_fst_2518_);
lean_dec(v_fst_2518_);
lean_ctor_set_float(v_data_2540_, sizeof(void*)*3, v___x_2541_);
v___x_2542_ = lean_unbox_float(v_snd_2519_);
lean_dec(v_snd_2519_);
lean_ctor_set_float(v_data_2540_, sizeof(void*)*3 + 8, v___x_2542_);
lean_ctor_set_uint8(v_data_2540_, sizeof(void*)*3 + 16, v_collapsed_2487_);
v___y_2505_ = v_m_2535_;
v___y_2506_ = v___y_2526_;
v_data_2507_ = v_data_2540_;
goto v___jp_2504_;
}
}
}
}
v___jp_2545_:
{
lean_object* v_ref_2546_; lean_object* v___x_2547_; 
v_ref_2546_ = lean_ctor_get(v___y_2496_, 5);
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v_fst_2499_);
v___x_2547_ = lean_apply_6(v_msg_2492_, v_fst_2499_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, lean_box(0));
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2547_);
v___y_2526_ = v_ref_2546_;
v_a_2527_ = v_a_2548_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2549_; 
lean_dec_ref(v___x_2547_);
v___x_2549_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3);
v___y_2526_ = v_ref_2546_;
v_a_2527_ = v___x_2549_;
goto v___jp_2525_;
}
}
v___jp_2550_:
{
if (v_clsEnabled_2490_ == 0)
{
if (v___y_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v_traceState_2553_; lean_object* v_env_2554_; lean_object* v_nextMacroScope_2555_; lean_object* v_ngen_2556_; lean_object* v_auxDeclNGen_2557_; lean_object* v_cache_2558_; lean_object* v_messages_2559_; lean_object* v_infoState_2560_; lean_object* v_snapshotTasks_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2580_; 
lean_del_object(v___x_2521_);
lean_dec(v_snd_2519_);
lean_dec(v_fst_2518_);
lean_del_object(v___x_2502_);
lean_dec_ref(v_msg_2492_);
lean_dec_ref(v_tag_2488_);
lean_dec(v_cls_2486_);
v___x_2552_ = lean_st_ref_take(v___y_2497_);
v_traceState_2553_ = lean_ctor_get(v___x_2552_, 4);
v_env_2554_ = lean_ctor_get(v___x_2552_, 0);
v_nextMacroScope_2555_ = lean_ctor_get(v___x_2552_, 1);
v_ngen_2556_ = lean_ctor_get(v___x_2552_, 2);
v_auxDeclNGen_2557_ = lean_ctor_get(v___x_2552_, 3);
v_cache_2558_ = lean_ctor_get(v___x_2552_, 5);
v_messages_2559_ = lean_ctor_get(v___x_2552_, 6);
v_infoState_2560_ = lean_ctor_get(v___x_2552_, 7);
v_snapshotTasks_2561_ = lean_ctor_get(v___x_2552_, 8);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2563_ = v___x_2552_;
v_isShared_2564_ = v_isSharedCheck_2580_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_snapshotTasks_2561_);
lean_inc(v_infoState_2560_);
lean_inc(v_messages_2559_);
lean_inc(v_cache_2558_);
lean_inc(v_traceState_2553_);
lean_inc(v_auxDeclNGen_2557_);
lean_inc(v_ngen_2556_);
lean_inc(v_nextMacroScope_2555_);
lean_inc(v_env_2554_);
lean_dec(v___x_2552_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2580_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
uint64_t v_tid_2565_; lean_object* v_traces_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2579_; 
v_tid_2565_ = lean_ctor_get_uint64(v_traceState_2553_, sizeof(void*)*1);
v_traces_2566_ = lean_ctor_get(v_traceState_2553_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_traceState_2553_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2568_ = v_traceState_2553_;
v_isShared_2569_ = v_isSharedCheck_2579_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_traces_2566_);
lean_dec(v_traceState_2553_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2579_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2491_, v_traces_2566_);
lean_dec_ref(v_traces_2566_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2570_);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2570_);
lean_ctor_set_uint64(v_reuseFailAlloc_2578_, sizeof(void*)*1, v_tid_2565_);
v___x_2572_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2574_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 4, v___x_2572_);
v___x_2574_ = v___x_2563_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_env_2554_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_nextMacroScope_2555_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_ngen_2556_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_auxDeclNGen_2557_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2577_, 5, v_cache_2558_);
lean_ctor_set(v_reuseFailAlloc_2577_, 6, v_messages_2559_);
lean_ctor_set(v_reuseFailAlloc_2577_, 7, v_infoState_2560_);
lean_ctor_set(v_reuseFailAlloc_2577_, 8, v_snapshotTasks_2561_);
v___x_2574_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = lean_st_ref_set(v___y_2497_, v___x_2574_);
v___x_2576_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_fst_2499_);
return v___x_2576_;
}
}
}
}
}
else
{
goto v___jp_2545_;
}
}
else
{
goto v___jp_2545_;
}
}
v___jp_2581_:
{
double v___x_2583_; double v___x_2584_; double v___x_2585_; uint8_t v___x_2586_; 
v___x_2583_ = lean_unbox_float(v_snd_2519_);
v___x_2584_ = lean_unbox_float(v_fst_2518_);
v___x_2585_ = lean_float_sub(v___x_2583_, v___x_2584_);
v___x_2586_ = lean_float_decLt(v___y_2582_, v___x_2585_);
v___y_2551_ = v___x_2586_;
goto v___jp_2550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object* v_cls_2599_, lean_object* v_collapsed_2600_, lean_object* v_tag_2601_, lean_object* v_opts_2602_, lean_object* v_clsEnabled_2603_, lean_object* v_oldTraces_2604_, lean_object* v_msg_2605_, lean_object* v_resStartStop_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
uint8_t v_collapsed_boxed_2612_; uint8_t v_clsEnabled_boxed_2613_; lean_object* v_res_2614_; 
v_collapsed_boxed_2612_ = lean_unbox(v_collapsed_2600_);
v_clsEnabled_boxed_2613_ = lean_unbox(v_clsEnabled_2603_);
v_res_2614_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(v_cls_2599_, v_collapsed_boxed_2612_, v_tag_2601_, v_opts_2602_, v_clsEnabled_boxed_2613_, v_oldTraces_2604_, v_msg_2605_, v_resStartStop_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_opts_2602_);
return v_res_2614_;
}
}
static uint64_t _init_l_Lean_Meta_wrapInstance___closed__0(void){
_start:
{
uint8_t v___x_2615_; uint64_t v___x_2616_; 
v___x_2615_ = 3;
v___x_2616_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0));
v___x_2619_ = l_Lean_stringToMessageData(v___x_2618_);
return v___x_2619_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3));
v___x_2624_ = l_Lean_stringToMessageData(v___x_2623_);
return v___x_2624_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5));
v___x_2627_ = l_Lean_stringToMessageData(v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1));
v___x_2630_ = l_Lean_stringToMessageData(v___x_2629_);
return v___x_2630_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8));
v___x_2635_ = l_Lean_stringToMessageData(v___x_2634_);
return v___x_2635_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10));
v___x_2638_ = l_Lean_stringToMessageData(v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14));
v___x_2644_ = l_Lean_stringToMessageData(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(lean_object* v_upperBound_2645_, lean_object* v_fst_2646_, lean_object* v_args_2647_, uint8_t v_compile_2648_, uint8_t v_logCompileErrors_2649_, uint8_t v___x_2650_, uint8_t v_isMeta_2651_, lean_object* v_val_2652_, lean_object* v_expectedType_2653_, lean_object* v_a_2654_, lean_object* v_b_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_a_2662_; lean_object* v___y_2667_; uint8_t v___x_2686_; 
v___x_2686_ = lean_nat_dec_lt(v_a_2654_, v_upperBound_2645_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; 
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_b_2655_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = lean_array_fget_borrowed(v_fst_2646_, v_a_2654_);
v___x_2689_ = l_Lean_Expr_mvarId_x21(v___x_2688_);
lean_inc(v___x_2689_);
v___x_2690_ = l_Lean_MVarId_getDecl(v___x_2689_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v_userName_2692_; lean_object* v_type_2693_; lean_object* v___x_2694_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
v_userName_2692_ = lean_ctor_get(v_a_2691_, 0);
lean_inc(v_userName_2692_);
v_type_2693_ = lean_ctor_get(v_a_2691_, 2);
lean_inc_ref(v_type_2693_);
lean_dec(v_a_2691_);
v___x_2694_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_2693_, v___y_2657_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc_n(v_a_2695_, 2);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_Lean_Meta_isProp(v_a_2695_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; lean_object* v_cls_2699_; lean_object* v___f_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = lean_box(0);
v_cls_2699_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_2700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_2701_ = lean_array_fget_borrowed(v_args_2647_, v_a_2654_);
v___x_2702_ = lean_unbox(v_a_2697_);
lean_dec(v_a_2697_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_inc(v_a_2695_);
v___x_2703_ = l_Lean_Meta_isClass_x3f(v_a_2695_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2802_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2802_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2802_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
if (lean_obj_tag(v_a_2704_) == 0)
{
lean_object* v_options_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
lean_del_object(v___x_2706_);
v_options_2708_ = lean_ctor_get(v___y_2658_, 2);
v___x_2709_ = lean_box(v___x_2650_);
v___x_2710_ = lean_box(v___x_2686_);
v___x_2711_ = lean_box(v_compile_2648_);
v___x_2712_ = lean_box(v_logCompileErrors_2649_);
v___x_2713_ = lean_box(v_isMeta_2651_);
lean_inc(v_a_2695_);
lean_inc(v___x_2701_);
lean_inc(v___x_2689_);
v___f_2714_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_2714_, 0, v___x_2689_);
lean_closure_set(v___f_2714_, 1, v___x_2701_);
lean_closure_set(v___f_2714_, 2, v___x_2698_);
lean_closure_set(v___f_2714_, 3, v_a_2695_);
lean_closure_set(v___f_2714_, 4, v___x_2709_);
lean_closure_set(v___f_2714_, 5, v___x_2710_);
lean_closure_set(v___f_2714_, 6, v___x_2711_);
lean_closure_set(v___f_2714_, 7, v___x_2712_);
lean_closure_set(v___f_2714_, 8, v___x_2713_);
v___x_2715_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2716_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2708_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; 
lean_dec_ref(v___f_2714_);
lean_dec(v_userName_2692_);
lean_inc(v___x_2701_);
v___x_2717_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_2689_, v___x_2701_, v___x_2698_, v_a_2695_, v___x_2650_, v___x_2686_, v_compile_2648_, v_logCompileErrors_2649_, v_isMeta_2651_, v___x_2698_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2717_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2718_; 
lean_inc(v_userName_2692_);
lean_inc(v_val_2652_);
v___x_2718_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_2652_, v_userName_2692_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v_fst_2722_; lean_object* v_snd_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2754_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref(v___x_2718_);
v_fst_2722_ = lean_ctor_get(v_a_2719_, 0);
v_snd_2723_ = lean_ctor_get(v_a_2719_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2725_ = v_a_2719_;
v_isShared_2726_ = v_isSharedCheck_2754_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snd_2723_);
lean_inc(v_fst_2722_);
lean_dec(v_a_2719_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2754_;
goto v_resetjp_2724_;
}
v___jp_2720_:
{
lean_object* v___x_2721_; 
lean_inc(v___x_2701_);
v___x_2721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_2689_, v___x_2701_, v___x_2698_, v_a_2695_, v___x_2650_, v___x_2686_, v_compile_2648_, v_logCompileErrors_2649_, v_isMeta_2651_, v___x_2698_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2721_;
goto v___jp_2666_;
}
v_resetjp_2724_:
{
uint8_t v___x_2727_; 
v___x_2727_ = lean_name_eq(v_fst_2722_, v_val_2652_);
if (v___x_2727_ == 0)
{
if (v___x_2716_ == 0)
{
lean_del_object(v___x_2725_);
lean_dec(v_snd_2723_);
lean_dec(v_fst_2722_);
lean_dec_ref(v___f_2714_);
lean_dec(v_userName_2692_);
goto v___jp_2720_;
}
else
{
lean_object* v___x_2728_; 
lean_dec(v_a_2695_);
v___x_2728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_2699_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; uint8_t v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref(v___x_2728_);
v___x_2730_ = lean_unbox(v_a_2729_);
lean_dec(v_a_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_del_object(v___x_2725_);
lean_dec(v_userName_2692_);
lean_inc_ref(v_expectedType_2653_);
lean_inc(v_val_2652_);
v___x_2731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_2652_, v_fst_2722_, v_expectedType_2653_, v___f_2700_, v___f_2714_, v___x_2698_, v_cls_2699_, v_snd_2723_, v___x_2689_, v___x_2698_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2731_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_2733_ = l_Lean_MessageData_ofName(v_userName_2692_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 7);
lean_ctor_set(v___x_2725_, 1, v___x_2733_);
lean_ctor_set(v___x_2725_, 0, v___x_2732_);
v___x_2735_ = v___x_2725_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2736_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
lean_inc(v_fst_2722_);
v___x_2738_ = l_Lean_MessageData_ofName(v_fst_2722_);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2699_, v___x_2741_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
lean_inc_ref(v_expectedType_2653_);
lean_inc(v_val_2652_);
v___x_2744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_2652_, v_fst_2722_, v_expectedType_2653_, v___f_2700_, v___f_2714_, v___x_2698_, v_cls_2699_, v_snd_2723_, v___x_2689_, v_a_2743_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2744_;
goto v___jp_2666_;
}
else
{
lean_dec(v_snd_2723_);
lean_dec(v_fst_2722_);
lean_dec_ref(v___f_2714_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
return v___x_2742_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_del_object(v___x_2725_);
lean_dec(v_snd_2723_);
lean_dec(v_fst_2722_);
lean_dec_ref(v___f_2714_);
lean_dec(v_userName_2692_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2746_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2728_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2728_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
else
{
lean_del_object(v___x_2725_);
lean_dec(v_snd_2723_);
lean_dec(v_fst_2722_);
lean_dec_ref(v___f_2714_);
lean_dec(v_userName_2692_);
goto v___jp_2720_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v___f_2714_);
lean_dec(v_a_2695_);
lean_dec(v_userName_2692_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2755_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2718_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2718_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
lean_object* v_options_2763_; lean_object* v_a_2765_; lean_object* v___y_2768_; uint8_t v___y_2769_; lean_object* v_a_2774_; lean_object* v___y_2778_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
lean_dec_ref(v_a_2704_);
lean_dec(v_userName_2692_);
v_options_2763_ = lean_ctor_get(v___y_2658_, 2);
v___x_2782_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2783_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2763_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_del_object(v___x_2706_);
lean_inc(v___x_2701_);
v___x_2784_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_2701_, v_a_2695_, v_compile_2648_, v_logCompileErrors_2649_, v_isMeta_2651_, v___x_2689_, v___x_2698_, v___x_2698_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2784_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_box(0);
lean_inc(v_a_2695_);
v___x_2786_ = l_Lean_Meta_trySynthInstance(v_a_2695_, v___x_2785_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
if (lean_obj_tag(v_a_2787_) == 1)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v_a_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v_a_2787_);
v___x_2789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_2699_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
lean_inc(v___x_2689_);
v___x_2792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_2689_, v_a_2788_, v___x_2698_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2778_ = v___x_2792_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2793_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_2788_);
v___x_2794_ = l_Lean_MessageData_ofExpr(v_a_2788_);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2699_, v___x_2795_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
lean_inc(v___x_2689_);
v___x_2798_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_2689_, v_a_2788_, v_a_2797_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2778_ = v___x_2798_;
goto v___jp_2777_;
}
else
{
lean_object* v_a_2799_; 
lean_dec(v_a_2788_);
v_a_2799_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___x_2796_);
v_a_2774_ = v_a_2799_;
goto v___jp_2773_;
}
}
}
else
{
lean_object* v_a_2800_; 
lean_dec(v_a_2788_);
v_a_2800_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2789_);
v_a_2774_ = v_a_2800_;
goto v___jp_2773_;
}
}
else
{
lean_dec(v_a_2787_);
lean_del_object(v___x_2706_);
v_a_2765_ = v___x_2698_;
goto v___jp_2764_;
}
}
else
{
lean_object* v_a_2801_; 
v_a_2801_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2801_);
lean_dec_ref(v___x_2786_);
v_a_2774_ = v_a_2801_;
goto v___jp_2773_;
}
}
v___jp_2764_:
{
lean_object* v___x_2766_; 
lean_inc(v___x_2701_);
v___x_2766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_2701_, v_a_2695_, v_compile_2648_, v_logCompileErrors_2649_, v_isMeta_2651_, v___x_2689_, v___x_2698_, v_a_2765_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2766_;
goto v___jp_2666_;
}
v___jp_2767_:
{
if (v___y_2769_ == 0)
{
lean_dec_ref(v___y_2768_);
lean_del_object(v___x_2706_);
v_a_2765_ = v___x_2698_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2771_; 
lean_dec(v_a_2695_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 1);
lean_ctor_set(v___x_2706_, 0, v___y_2768_);
v___x_2771_ = v___x_2706_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___y_2768_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
v___jp_2773_:
{
uint8_t v___x_2775_; 
v___x_2775_ = l_Lean_Exception_isInterrupt(v_a_2774_);
if (v___x_2775_ == 0)
{
uint8_t v___x_2776_; 
lean_inc_ref(v_a_2774_);
v___x_2776_ = l_Lean_Exception_isRuntime(v_a_2774_);
v___y_2768_ = v_a_2774_;
v___y_2769_ = v___x_2776_;
goto v___jp_2767_;
}
else
{
v___y_2768_ = v_a_2774_;
v___y_2769_ = v___x_2775_;
goto v___jp_2767_;
}
}
v___jp_2777_:
{
if (lean_obj_tag(v___y_2778_) == 0)
{
lean_object* v_a_2779_; 
lean_del_object(v___x_2706_);
v_a_2779_ = lean_ctor_get(v___y_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___y_2778_);
if (lean_obj_tag(v_a_2779_) == 0)
{
lean_dec(v_a_2695_);
lean_dec(v___x_2689_);
v_a_2662_ = v___x_2698_;
goto v___jp_2661_;
}
else
{
lean_object* v_a_2780_; 
v_a_2780_ = lean_ctor_get(v_a_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v_a_2779_);
v_a_2765_ = v_a_2780_;
goto v___jp_2764_;
}
}
else
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___y_2778_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___y_2778_);
v_a_2774_ = v_a_2781_;
goto v___jp_2773_;
}
}
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2695_);
lean_dec(v_userName_2692_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2803_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2703_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2703_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v___x_2811_; 
lean_dec(v_userName_2692_);
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v___x_2701_);
v___x_2811_ = lean_infer_type(v___x_2701_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc_n(v_a_2812_, 2);
lean_dec_ref(v___x_2811_);
lean_inc(v_a_2695_);
v___x_2813_ = l_Lean_Meta_isExprDefEq(v_a_2695_, v_a_2812_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___f_2815_; uint8_t v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2813_);
v___f_2815_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_2816_ = lean_unbox(v_a_2814_);
lean_dec(v_a_2814_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
v___x_2817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_2699_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; uint8_t v___x_2819_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
v___x_2819_ = lean_unbox(v_a_2818_);
lean_dec(v_a_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec(v_a_2812_);
lean_inc(v___x_2701_);
v___x_2820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_2695_, v___x_2701_, v___x_2686_, v___x_2689_, v___f_2815_, v___x_2698_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2820_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2821_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_2654_);
v___x_2822_ = l_Nat_reprFast(v_a_2654_);
v___x_2823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
v___x_2824_ = l_Lean_MessageData_ofFormat(v___x_2823_);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2821_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
lean_inc(v_a_2695_);
v___x_2828_ = l_Lean_MessageData_ofExpr(v_a_2695_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_MessageData_ofExpr(v_a_2812_);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
lean_inc(v___x_2701_);
v___x_2836_ = l_Lean_MessageData_ofExpr(v___x_2701_);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2699_, v___x_2837_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref(v___x_2838_);
lean_inc(v___x_2701_);
v___x_2840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_2695_, v___x_2701_, v___x_2686_, v___x_2689_, v___f_2815_, v_a_2839_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2840_;
goto v___jp_2666_;
}
else
{
lean_dec(v_a_2695_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
return v___x_2838_;
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2812_);
lean_dec(v_a_2695_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2841_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2817_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2817_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v___x_2849_; 
lean_dec(v_a_2812_);
lean_dec(v_a_2695_);
lean_inc(v___x_2701_);
v___x_2849_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2689_, v___x_2701_, v___y_2657_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_2698_, v_a_2850_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v___y_2667_ = v___x_2851_;
goto v___jp_2666_;
}
else
{
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_a_2812_);
lean_dec(v_a_2695_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2852_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2813_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2813_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_a_2695_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2860_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2811_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2811_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_a_2695_);
lean_dec(v_userName_2692_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2868_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2696_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2696_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_userName_2692_);
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2876_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2694_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2694_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v___x_2689_);
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2884_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2690_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2690_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
v___jp_2661_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = lean_nat_add(v_a_2654_, v___x_2663_);
lean_dec(v_a_2654_);
v_a_2654_ = v___x_2664_;
v_b_2655_ = v_a_2662_;
goto _start;
}
v___jp_2666_:
{
if (lean_obj_tag(v___y_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2677_; 
v_a_2668_ = lean_ctor_get(v___y_2667_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___y_2667_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2670_ = v___y_2667_;
v_isShared_2671_ = v_isSharedCheck_2677_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___y_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2677_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
if (lean_obj_tag(v_a_2668_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; 
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2672_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_a_2672_);
lean_dec_ref(v_a_2668_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v_a_2672_);
v___x_2674_ = v___x_2670_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
else
{
lean_object* v_a_2676_; 
lean_del_object(v___x_2670_);
v_a_2676_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v_a_2668_);
v_a_2662_ = v_a_2676_;
goto v___jp_2661_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_a_2654_);
lean_dec_ref(v_expectedType_2653_);
lean_dec(v_val_2652_);
v_a_2678_ = lean_ctor_get(v___y_2667_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___y_2667_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___y_2667_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___y_2667_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2));
v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
return v___x_2894_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4));
v___x_2897_ = l_Lean_stringToMessageData(v___x_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6));
v___x_2900_ = l_Lean_stringToMessageData(v___x_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(lean_object* v_inst_2901_, lean_object* v_expectedType_2902_, uint8_t v___x_2903_, uint8_t v_compile_2904_, uint8_t v_logCompileErrors_2905_, uint8_t v_isMeta_2906_, lean_object* v_val_2907_, lean_object* v_x_2908_, lean_object* v_x_2909_, lean_object* v_x_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; 
if (lean_obj_tag(v_x_2908_) == 5)
{
lean_object* v_fn_2955_; lean_object* v_arg_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_fn_2955_ = lean_ctor_get(v_x_2908_, 0);
lean_inc_ref(v_fn_2955_);
v_arg_2956_ = lean_ctor_get(v_x_2908_, 1);
lean_inc_ref(v_arg_2956_);
lean_dec_ref(v_x_2908_);
v___x_2957_ = lean_array_set(v_x_2909_, v_x_2910_, v_arg_2956_);
v___x_2958_ = lean_unsigned_to_nat(1u);
v___x_2959_ = lean_nat_sub(v_x_2910_, v___x_2958_);
lean_dec(v_x_2910_);
v_x_2908_ = v_fn_2955_;
v_x_2909_ = v___x_2957_;
v_x_2910_ = v___x_2959_;
goto _start;
}
else
{
uint8_t v___x_2961_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v_options_2966_; lean_object* v___y_2967_; lean_object* v_cls_3033_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___x_3056_; 
lean_dec(v_x_2910_);
v___x_2961_ = 1;
v_cls_3033_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3056_ = l_Lean_Expr_constName_x3f(v_x_2908_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_dec_ref(v_x_2909_);
lean_dec_ref(v_x_2908_);
lean_dec(v_val_2907_);
v___y_3035_ = v___y_2911_;
v___y_3036_ = v___y_2912_;
v___y_3037_ = v___y_2913_;
v___y_3038_ = v___y_2914_;
goto v___jp_3034_;
}
else
{
lean_object* v_val_3057_; lean_object* v___x_3058_; 
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref(v___x_3056_);
v___x_3058_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3057_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
if (lean_obj_tag(v_a_3059_) == 6)
{
lean_object* v_val_3060_; lean_object* v___x_3061_; 
lean_dec_ref(v_inst_2901_);
v_val_3060_ = lean_ctor_get(v_a_3059_, 0);
lean_inc_ref(v_val_3060_);
lean_dec_ref(v_a_3059_);
lean_inc(v___y_2914_);
lean_inc_ref(v___y_2913_);
lean_inc(v___y_2912_);
lean_inc_ref(v___y_2911_);
lean_inc_ref(v_x_2908_);
v___x_3061_ = lean_infer_type(v_x_2908_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref(v___x_3061_);
v___x_3063_ = 0;
v___x_3064_ = l_Lean_Meta_forallMetaTelescope(v_a_3062_, v___x_3063_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v_snd_3066_; lean_object* v_fst_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3166_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref(v___x_3064_);
v_snd_3066_ = lean_ctor_get(v_a_3065_, 1);
v_fst_3067_ = lean_ctor_get(v_a_3065_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_a_3065_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3069_ = v_a_3065_;
v_isShared_3070_ = v_isSharedCheck_3166_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_snd_3066_);
lean_inc(v_fst_3067_);
lean_dec(v_a_3065_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3166_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_snd_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3164_; 
v_snd_3071_ = lean_ctor_get(v_snd_3066_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_snd_3066_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; 
v_unused_3165_ = lean_ctor_get(v_snd_3066_, 0);
lean_dec(v_unused_3165_);
v___x_3073_ = v_snd_3066_;
v_isShared_3074_ = v_isSharedCheck_3164_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_snd_3071_);
lean_dec(v_snd_3066_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3164_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3075_ = lean_array_get_size(v_x_2909_);
v___x_3112_ = lean_array_get_size(v_fst_3067_);
v___x_3113_ = lean_nat_dec_eq(v___x_3075_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
lean_dec(v_snd_3071_);
lean_dec(v_fst_3067_);
lean_dec_ref(v_val_3060_);
lean_dec(v_val_2907_);
lean_dec_ref(v_expectedType_2902_);
v___x_3114_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_3115_ = l_Lean_MessageData_ofExpr(v_x_2908_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set_tag(v___x_3073_, 7);
lean_ctor_set(v___x_3073_, 1, v___x_3115_);
lean_ctor_set(v___x_3073_, 0, v___x_3114_);
v___x_3117_ = v___x_3073_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3);
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 7);
lean_ctor_set(v___x_3069_, 1, v___x_3118_);
lean_ctor_set(v___x_3069_, 0, v___x_3117_);
v___x_3120_ = v___x_3069_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3121_ = lean_array_to_list(v_x_2909_);
v___x_3122_ = lean_box(0);
v___x_3123_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_3121_, v___x_3122_);
v___x_3124_ = l_Lean_MessageData_ofList(v___x_3123_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3120_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3125_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_3126_;
}
}
}
else
{
lean_object* v___x_3129_; 
lean_inc_ref(v_expectedType_2902_);
v___x_3129_ = l_Lean_Meta_isExprDefEq(v_expectedType_2902_, v_snd_3071_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; uint8_t v___x_3131_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref(v___x_3129_);
v___x_3131_ = lean_unbox(v_a_3130_);
lean_dec(v_a_3130_);
if (v___x_3131_ == 0)
{
lean_object* v_toConstantVal_3132_; lean_object* v_name_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
lean_dec(v_fst_3067_);
lean_dec_ref(v_x_2909_);
lean_dec_ref(v_x_2908_);
lean_dec(v_val_2907_);
v_toConstantVal_3132_ = lean_ctor_get(v_val_3060_, 0);
lean_inc_ref(v_toConstantVal_3132_);
lean_dec_ref(v_val_3060_);
v_name_3133_ = lean_ctor_get(v_toConstantVal_3132_, 0);
lean_inc(v_name_3133_);
lean_dec_ref(v_toConstantVal_3132_);
v___x_3134_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_3135_ = l_Lean_MessageData_ofExpr(v_expectedType_2902_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set_tag(v___x_3073_, 7);
lean_ctor_set(v___x_3073_, 1, v___x_3135_);
lean_ctor_set(v___x_3073_, 0, v___x_3134_);
v___x_3137_ = v___x_3073_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3138_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 7);
lean_ctor_set(v___x_3069_, 1, v___x_3138_);
lean_ctor_set(v___x_3069_, 0, v___x_3137_);
v___x_3140_ = v___x_3069_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v___x_3141_ = l_Lean_MessageData_ofConstName(v_name_3133_, v___x_2903_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3144_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
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
else
{
lean_del_object(v___x_3073_);
lean_del_object(v___x_3069_);
v___y_3077_ = v___y_2911_;
v___y_3078_ = v___y_2912_;
v___y_3079_ = v___y_2913_;
v___y_3080_ = v___y_2914_;
goto v___jp_3076_;
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_del_object(v___x_3073_);
lean_del_object(v___x_3069_);
lean_dec(v_fst_3067_);
lean_dec_ref(v_val_3060_);
lean_dec_ref(v_x_2909_);
lean_dec_ref(v_x_2908_);
lean_dec(v_val_2907_);
lean_dec_ref(v_expectedType_2902_);
v_a_3156_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3129_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3129_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
v___jp_3076_:
{
lean_object* v_numParams_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_numParams_3081_ = lean_ctor_get(v_val_3060_, 3);
lean_inc(v_numParams_3081_);
lean_dec_ref(v_val_3060_);
v___x_3082_ = lean_box(0);
v___x_3083_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v___x_3075_, v_fst_3067_, v_x_2909_, v_compile_2904_, v_logCompileErrors_2905_, v___x_2903_, v_isMeta_2906_, v_val_2907_, v_expectedType_2902_, v_numParams_3081_, v___x_3082_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec_ref(v_x_2909_);
if (lean_obj_tag(v___x_3083_) == 0)
{
size_t v_sz_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
lean_dec_ref(v___x_3083_);
v_sz_3084_ = lean_array_size(v_fst_3067_);
v___x_3085_ = ((size_t)0ULL);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_3084_, v___x_3085_, v_fst_3067_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3095_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = l_Lean_mkAppN(v_x_2908_, v_a_3087_);
lean_dec(v_a_3087_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3093_ = v___x_3089_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v_x_2908_);
v_a_3096_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3086_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3086_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_fst_3067_);
lean_dec_ref(v_x_2908_);
v_a_3104_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3083_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3083_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v_val_3060_);
lean_dec_ref(v_x_2909_);
lean_dec_ref(v_x_2908_);
lean_dec(v_val_2907_);
lean_dec_ref(v_expectedType_2902_);
v_a_3167_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3064_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3064_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_dec_ref(v_val_3060_);
lean_dec_ref(v_x_2909_);
lean_dec_ref(v_x_2908_);
lean_dec(v_val_2907_);
lean_dec_ref(v_expectedType_2902_);
return v___x_3061_;
}
}
else
{
lean_dec(v_a_3059_);
lean_dec_ref(v_x_2909_);
lean_dec_ref(v_x_2908_);
lean_dec(v_val_2907_);
v___y_3035_ = v___y_2911_;
v___y_3036_ = v___y_2912_;
v___y_3037_ = v___y_2913_;
v___y_3038_ = v___y_2914_;
goto v___jp_3034_;
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v_x_2909_);
lean_dec_ref(v_x_2908_);
lean_dec(v_val_2907_);
lean_dec_ref(v_expectedType_2902_);
lean_dec_ref(v_inst_2901_);
v_a_3175_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3058_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3058_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
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
v___jp_2962_:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2969_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2966_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; 
lean_dec_ref(v_expectedType_2902_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_inst_2901_);
return v___x_2970_;
}
else
{
lean_object* v___x_2971_; 
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc_ref(v_inst_2901_);
v___x_2971_ = lean_infer_type(v_inst_2901_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2967_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref(v___x_2971_);
lean_inc_ref(v_expectedType_2902_);
v___x_2973_ = l_Lean_Meta_isExprDefEq(v_expectedType_2902_, v_a_2972_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2967_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3024_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_3024_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3024_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_unbox(v_a_2974_);
lean_dec(v_a_2974_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_a_2981_; lean_object* v___x_2982_; 
lean_del_object(v___x_2976_);
v___x_2979_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_2980_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2979_, v___y_2967_);
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc_n(v_a_2981_, 2);
lean_dec_ref(v___x_2980_);
v___x_2982_ = l_Lean_Meta_mkAuxDefinition(v_a_2981_, v_expectedType_2902_, v_inst_2901_, v___x_2903_, v___x_2903_, v___x_2961_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2967_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = 3;
lean_inc(v_a_2981_);
v___x_2985_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_2981_, v___x_2984_, v___y_2964_, v___y_2967_);
lean_dec_ref(v___x_2985_);
if (v_isMeta_2906_ == 0)
{
v___y_2939_ = v_a_2981_;
v___y_2940_ = v_a_2983_;
v___y_2941_ = v___y_2965_;
v___y_2942_ = v___y_2967_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2986_; lean_object* v_env_2987_; lean_object* v_nextMacroScope_2988_; lean_object* v_ngen_2989_; lean_object* v_auxDeclNGen_2990_; lean_object* v_traceState_2991_; lean_object* v_messages_2992_; lean_object* v_infoState_2993_; lean_object* v_snapshotTasks_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3019_; 
v___x_2986_ = lean_st_ref_take(v___y_2967_);
v_env_2987_ = lean_ctor_get(v___x_2986_, 0);
v_nextMacroScope_2988_ = lean_ctor_get(v___x_2986_, 1);
v_ngen_2989_ = lean_ctor_get(v___x_2986_, 2);
v_auxDeclNGen_2990_ = lean_ctor_get(v___x_2986_, 3);
v_traceState_2991_ = lean_ctor_get(v___x_2986_, 4);
v_messages_2992_ = lean_ctor_get(v___x_2986_, 6);
v_infoState_2993_ = lean_ctor_get(v___x_2986_, 7);
v_snapshotTasks_2994_ = lean_ctor_get(v___x_2986_, 8);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v___x_2986_, 5);
lean_dec(v_unused_3020_);
v___x_2996_ = v___x_2986_;
v_isShared_2997_ = v_isSharedCheck_3019_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_snapshotTasks_2994_);
lean_inc(v_infoState_2993_);
lean_inc(v_messages_2992_);
lean_inc(v_traceState_2991_);
lean_inc(v_auxDeclNGen_2990_);
lean_inc(v_ngen_2989_);
lean_inc(v_nextMacroScope_2988_);
lean_inc(v_env_2987_);
lean_dec(v___x_2986_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3019_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
lean_inc(v_a_2981_);
v___x_2998_ = l_Lean_markMeta(v_env_2987_, v_a_2981_);
v___x_2999_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 5, v___x_2999_);
lean_ctor_set(v___x_2996_, 0, v___x_2998_);
v___x_3001_ = v___x_2996_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_nextMacroScope_2988_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_ngen_2989_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_auxDeclNGen_2990_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_traceState_2991_);
lean_ctor_set(v_reuseFailAlloc_3018_, 5, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3018_, 6, v_messages_2992_);
lean_ctor_set(v_reuseFailAlloc_3018_, 7, v_infoState_2993_);
lean_ctor_set(v_reuseFailAlloc_3018_, 8, v_snapshotTasks_2994_);
v___x_3001_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v_mctx_3004_; lean_object* v_zetaDeltaFVarIds_3005_; lean_object* v_postponed_3006_; lean_object* v_diag_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3016_; 
v___x_3002_ = lean_st_ref_set(v___y_2967_, v___x_3001_);
v___x_3003_ = lean_st_ref_take(v___y_2964_);
v_mctx_3004_ = lean_ctor_get(v___x_3003_, 0);
v_zetaDeltaFVarIds_3005_ = lean_ctor_get(v___x_3003_, 2);
v_postponed_3006_ = lean_ctor_get(v___x_3003_, 3);
v_diag_3007_ = lean_ctor_get(v___x_3003_, 4);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_3003_, 1);
lean_dec(v_unused_3017_);
v___x_3009_ = v___x_3003_;
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_diag_3007_);
lean_inc(v_postponed_3006_);
lean_inc(v_zetaDeltaFVarIds_3005_);
lean_inc(v_mctx_3004_);
lean_dec(v___x_3003_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___x_3011_);
v___x_3013_ = v___x_3009_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_mctx_3004_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3015_, 2, v_zetaDeltaFVarIds_3005_);
lean_ctor_set(v_reuseFailAlloc_3015_, 3, v_postponed_3006_);
lean_ctor_set(v_reuseFailAlloc_3015_, 4, v_diag_3007_);
v___x_3013_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_st_ref_set(v___y_2964_, v___x_3013_);
v___y_2939_ = v_a_2981_;
v___y_2940_ = v_a_2983_;
v___y_2941_ = v___y_2965_;
v___y_2942_ = v___y_2967_;
goto v___jp_2938_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2981_);
return v___x_2982_;
}
}
else
{
lean_object* v___x_3022_; 
lean_dec_ref(v_expectedType_2902_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v_inst_2901_);
v___x_3022_ = v___x_2976_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_inst_2901_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_expectedType_2902_);
lean_dec_ref(v_inst_2901_);
v_a_3025_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2973_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2973_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2902_);
lean_dec_ref(v_inst_2901_);
return v___x_2971_;
}
}
}
v___jp_3034_:
{
lean_object* v_options_3039_; uint8_t v_hasTrace_3040_; 
v_options_3039_ = lean_ctor_get(v___y_3037_, 2);
v_hasTrace_3040_ = lean_ctor_get_uint8(v_options_3039_, sizeof(void*)*1);
if (v_hasTrace_3040_ == 0)
{
v___y_2963_ = v___y_3035_;
v___y_2964_ = v___y_3036_;
v___y_2965_ = v___y_3037_;
v_options_2966_ = v_options_3039_;
v___y_2967_ = v___y_3038_;
goto v___jp_2962_;
}
else
{
lean_object* v_inheritedTraceOptions_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v_inheritedTraceOptions_3041_ = lean_ctor_get(v___y_3037_, 13);
v___x_3042_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_3043_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3041_, v_options_3039_, v___x_3042_);
if (v___x_3043_ == 0)
{
v___y_2963_ = v___y_3035_;
v___y_2964_ = v___y_3036_;
v___y_2965_ = v___y_3037_;
v_options_2966_ = v_options_3039_;
v___y_2967_ = v___y_3038_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3044_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_2901_);
v___x_3045_ = l_Lean_MessageData_ofExpr(v_inst_2901_);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3033_, v___x_3046_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_dec_ref(v___x_3047_);
v___y_2963_ = v___y_3035_;
v___y_2964_ = v___y_3036_;
v___y_2965_ = v___y_3037_;
v_options_2966_ = v_options_3039_;
v___y_2967_ = v___y_3038_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v_expectedType_2902_);
lean_dec_ref(v_inst_2901_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
}
}
v___jp_2916_:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_enableRealizationsForConst(v___y_2917_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v___x_2921_, 0);
lean_dec(v_unused_2929_);
v___x_2923_ = v___x_2921_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_dec(v___x_2921_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v___y_2918_);
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___y_2918_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v___y_2918_);
v_a_2930_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2921_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2921_);
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
v___jp_2938_:
{
if (v_compile_2904_ == 0)
{
v___y_2917_ = v___y_2939_;
v___y_2918_ = v___y_2940_;
v___y_2919_ = v___y_2941_;
v___y_2920_ = v___y_2942_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_mk_empty_array_with_capacity(v___x_2943_);
lean_inc(v___y_2939_);
v___x_2945_ = lean_array_push(v___x_2944_, v___y_2939_);
v___x_2946_ = l_Lean_compileDecls(v___x_2945_, v_logCompileErrors_2905_, v___y_2941_, v___y_2942_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_dec_ref(v___x_2946_);
v___y_2917_ = v___y_2939_;
v___y_2918_ = v___y_2940_;
v___y_2919_ = v___y_2941_;
v___y_2920_ = v___y_2942_;
goto v___jp_2916_;
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(lean_object* v_inst_3183_, lean_object* v_expectedType_3184_, uint8_t v___x_3185_, uint8_t v_compile_3186_, uint8_t v_logCompileErrors_3187_, uint8_t v_isMeta_3188_, lean_object* v_val_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_, lean_object* v_x_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; 
if (lean_obj_tag(v_x_3190_) == 5)
{
lean_object* v_fn_3237_; lean_object* v_arg_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_fn_3237_ = lean_ctor_get(v_x_3190_, 0);
lean_inc_ref(v_fn_3237_);
v_arg_3238_ = lean_ctor_get(v_x_3190_, 1);
lean_inc_ref(v_arg_3238_);
lean_dec_ref(v_x_3190_);
v___x_3239_ = lean_array_set(v_x_3191_, v_x_3192_, v_arg_3238_);
v___x_3240_ = lean_unsigned_to_nat(1u);
v___x_3241_ = lean_nat_sub(v_x_3192_, v___x_3240_);
v___x_3242_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(v_inst_3183_, v_expectedType_3184_, v___x_3185_, v_compile_3186_, v_logCompileErrors_3187_, v_isMeta_3188_, v_val_3189_, v_fn_3237_, v___x_3239_, v___x_3241_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
return v___x_3242_;
}
else
{
uint8_t v___x_3243_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v_options_3248_; lean_object* v___y_3249_; lean_object* v_cls_3315_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___x_3338_; 
v___x_3243_ = 1;
v_cls_3315_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3338_ = l_Lean_Expr_constName_x3f(v_x_3190_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3190_);
lean_dec(v_val_3189_);
v___y_3317_ = v___y_3193_;
v___y_3318_ = v___y_3194_;
v___y_3319_ = v___y_3195_;
v___y_3320_ = v___y_3196_;
goto v___jp_3316_;
}
else
{
lean_object* v_val_3339_; lean_object* v___x_3340_; 
v_val_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3339_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3339_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3340_);
if (lean_obj_tag(v_a_3341_) == 6)
{
lean_object* v_val_3342_; lean_object* v___x_3343_; 
lean_dec_ref(v_inst_3183_);
v_val_3342_ = lean_ctor_get(v_a_3341_, 0);
lean_inc_ref(v_val_3342_);
lean_dec_ref(v_a_3341_);
lean_inc(v___y_3196_);
lean_inc_ref(v___y_3195_);
lean_inc(v___y_3194_);
lean_inc_ref(v___y_3193_);
lean_inc_ref(v_x_3190_);
v___x_3343_ = lean_infer_type(v_x_3190_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = 0;
v___x_3346_ = l_Lean_Meta_forallMetaTelescope(v_a_3344_, v___x_3345_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v_snd_3348_; lean_object* v_fst_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3448_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref(v___x_3346_);
v_snd_3348_ = lean_ctor_get(v_a_3347_, 1);
v_fst_3349_ = lean_ctor_get(v_a_3347_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_a_3347_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3351_ = v_a_3347_;
v_isShared_3352_ = v_isSharedCheck_3448_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_snd_3348_);
lean_inc(v_fst_3349_);
lean_dec(v_a_3347_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3448_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_snd_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3446_; 
v_snd_3353_ = lean_ctor_get(v_snd_3348_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_snd_3348_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; 
v_unused_3447_ = lean_ctor_get(v_snd_3348_, 0);
lean_dec(v_unused_3447_);
v___x_3355_ = v_snd_3348_;
v_isShared_3356_ = v_isSharedCheck_3446_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_snd_3353_);
lean_dec(v_snd_3348_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3446_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3357_ = lean_array_get_size(v_x_3191_);
v___x_3394_ = lean_array_get_size(v_fst_3349_);
v___x_3395_ = lean_nat_dec_eq(v___x_3357_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
lean_dec(v_snd_3353_);
lean_dec(v_fst_3349_);
lean_dec_ref(v_val_3342_);
lean_dec(v_val_3189_);
lean_dec_ref(v_expectedType_3184_);
v___x_3396_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_3397_ = l_Lean_MessageData_ofExpr(v_x_3190_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set_tag(v___x_3355_, 7);
lean_ctor_set(v___x_3355_, 1, v___x_3397_);
lean_ctor_set(v___x_3355_, 0, v___x_3396_);
v___x_3399_ = v___x_3355_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3400_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3);
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 7);
lean_ctor_set(v___x_3351_, 1, v___x_3400_);
lean_ctor_set(v___x_3351_, 0, v___x_3399_);
v___x_3402_ = v___x_3351_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3403_ = lean_array_to_list(v_x_3191_);
v___x_3404_ = lean_box(0);
v___x_3405_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_3403_, v___x_3404_);
v___x_3406_ = l_Lean_MessageData_ofList(v___x_3405_);
v___x_3407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3402_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3407_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
return v___x_3408_;
}
}
}
else
{
lean_object* v___x_3411_; 
lean_inc_ref(v_expectedType_3184_);
v___x_3411_ = l_Lean_Meta_isExprDefEq(v_expectedType_3184_, v_snd_3353_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; uint8_t v___x_3413_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = lean_unbox(v_a_3412_);
lean_dec(v_a_3412_);
if (v___x_3413_ == 0)
{
lean_object* v_toConstantVal_3414_; lean_object* v_name_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
lean_dec(v_fst_3349_);
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3190_);
lean_dec(v_val_3189_);
v_toConstantVal_3414_ = lean_ctor_get(v_val_3342_, 0);
lean_inc_ref(v_toConstantVal_3414_);
lean_dec_ref(v_val_3342_);
v_name_3415_ = lean_ctor_get(v_toConstantVal_3414_, 0);
lean_inc(v_name_3415_);
lean_dec_ref(v_toConstantVal_3414_);
v___x_3416_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_3417_ = l_Lean_MessageData_ofExpr(v_expectedType_3184_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set_tag(v___x_3355_, 7);
lean_ctor_set(v___x_3355_, 1, v___x_3417_);
lean_ctor_set(v___x_3355_, 0, v___x_3416_);
v___x_3419_ = v___x_3355_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 7);
lean_ctor_set(v___x_3351_, 1, v___x_3420_);
lean_ctor_set(v___x_3351_, 0, v___x_3419_);
v___x_3422_ = v___x_3351_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v___x_3423_ = l_Lean_MessageData_ofConstName(v_name_3415_, v___x_3185_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3426_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_del_object(v___x_3355_);
lean_del_object(v___x_3351_);
v___y_3359_ = v___y_3193_;
v___y_3360_ = v___y_3194_;
v___y_3361_ = v___y_3195_;
v___y_3362_ = v___y_3196_;
goto v___jp_3358_;
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_del_object(v___x_3355_);
lean_del_object(v___x_3351_);
lean_dec(v_fst_3349_);
lean_dec_ref(v_val_3342_);
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3190_);
lean_dec(v_val_3189_);
lean_dec_ref(v_expectedType_3184_);
v_a_3438_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3411_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3411_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
v___jp_3358_:
{
lean_object* v_numParams_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_numParams_3363_ = lean_ctor_get(v_val_3342_, 3);
lean_inc(v_numParams_3363_);
lean_dec_ref(v_val_3342_);
v___x_3364_ = lean_box(0);
v___x_3365_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v___x_3357_, v_fst_3349_, v_x_3191_, v_compile_3186_, v_logCompileErrors_3187_, v___x_3185_, v_isMeta_3188_, v_val_3189_, v_expectedType_3184_, v_numParams_3363_, v___x_3364_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec_ref(v_x_3191_);
if (lean_obj_tag(v___x_3365_) == 0)
{
size_t v_sz_3366_; size_t v___x_3367_; lean_object* v___x_3368_; 
lean_dec_ref(v___x_3365_);
v_sz_3366_ = lean_array_size(v_fst_3349_);
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_3366_, v___x_3367_, v_fst_3349_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = l_Lean_mkAppN(v_x_3190_, v_a_3369_);
lean_dec(v_a_3369_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec_ref(v_x_3190_);
v_a_3378_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3368_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3368_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec(v_fst_3349_);
lean_dec_ref(v_x_3190_);
v_a_3386_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3365_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3365_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v_val_3342_);
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3190_);
lean_dec(v_val_3189_);
lean_dec_ref(v_expectedType_3184_);
v_a_3449_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3346_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3346_);
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
else
{
lean_dec_ref(v_val_3342_);
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3190_);
lean_dec(v_val_3189_);
lean_dec_ref(v_expectedType_3184_);
return v___x_3343_;
}
}
else
{
lean_dec(v_a_3341_);
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3190_);
lean_dec(v_val_3189_);
v___y_3317_ = v___y_3193_;
v___y_3318_ = v___y_3194_;
v___y_3319_ = v___y_3195_;
v___y_3320_ = v___y_3196_;
goto v___jp_3316_;
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3190_);
lean_dec(v_val_3189_);
lean_dec_ref(v_expectedType_3184_);
lean_dec_ref(v_inst_3183_);
v_a_3457_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3340_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3340_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
v___jp_3244_:
{
lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3251_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3248_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; 
lean_dec_ref(v_expectedType_3184_);
v___x_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3252_, 0, v_inst_3183_);
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; 
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
lean_inc_ref(v_inst_3183_);
v___x_3253_ = lean_infer_type(v_inst_3183_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3249_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
lean_inc_ref(v_expectedType_3184_);
v___x_3255_ = l_Lean_Meta_isExprDefEq(v_expectedType_3184_, v_a_3254_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3249_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3306_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3306_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3306_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_unbox(v_a_3256_);
lean_dec(v_a_3256_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v_a_3263_; lean_object* v___x_3264_; 
lean_del_object(v___x_3258_);
v___x_3261_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_3262_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3261_, v___y_3249_);
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc_n(v_a_3263_, 2);
lean_dec_ref(v___x_3262_);
v___x_3264_ = l_Lean_Meta_mkAuxDefinition(v_a_3263_, v_expectedType_3184_, v_inst_3183_, v___x_3185_, v___x_3185_, v___x_3243_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3249_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v___x_3266_ = 3;
lean_inc(v_a_3263_);
v___x_3267_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3263_, v___x_3266_, v___y_3246_, v___y_3249_);
lean_dec_ref(v___x_3267_);
if (v_isMeta_3188_ == 0)
{
v___y_3221_ = v_a_3263_;
v___y_3222_ = v_a_3265_;
v___y_3223_ = v___y_3247_;
v___y_3224_ = v___y_3249_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3268_; lean_object* v_env_3269_; lean_object* v_nextMacroScope_3270_; lean_object* v_ngen_3271_; lean_object* v_auxDeclNGen_3272_; lean_object* v_traceState_3273_; lean_object* v_messages_3274_; lean_object* v_infoState_3275_; lean_object* v_snapshotTasks_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3301_; 
v___x_3268_ = lean_st_ref_take(v___y_3249_);
v_env_3269_ = lean_ctor_get(v___x_3268_, 0);
v_nextMacroScope_3270_ = lean_ctor_get(v___x_3268_, 1);
v_ngen_3271_ = lean_ctor_get(v___x_3268_, 2);
v_auxDeclNGen_3272_ = lean_ctor_get(v___x_3268_, 3);
v_traceState_3273_ = lean_ctor_get(v___x_3268_, 4);
v_messages_3274_ = lean_ctor_get(v___x_3268_, 6);
v_infoState_3275_ = lean_ctor_get(v___x_3268_, 7);
v_snapshotTasks_3276_ = lean_ctor_get(v___x_3268_, 8);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; 
v_unused_3302_ = lean_ctor_get(v___x_3268_, 5);
lean_dec(v_unused_3302_);
v___x_3278_ = v___x_3268_;
v_isShared_3279_ = v_isSharedCheck_3301_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_snapshotTasks_3276_);
lean_inc(v_infoState_3275_);
lean_inc(v_messages_3274_);
lean_inc(v_traceState_3273_);
lean_inc(v_auxDeclNGen_3272_);
lean_inc(v_ngen_3271_);
lean_inc(v_nextMacroScope_3270_);
lean_inc(v_env_3269_);
lean_dec(v___x_3268_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3301_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_inc(v_a_3263_);
v___x_3280_ = l_Lean_markMeta(v_env_3269_, v_a_3263_);
v___x_3281_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 5, v___x_3281_);
lean_ctor_set(v___x_3278_, 0, v___x_3280_);
v___x_3283_ = v___x_3278_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_nextMacroScope_3270_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_ngen_3271_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v_auxDeclNGen_3272_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_traceState_3273_);
lean_ctor_set(v_reuseFailAlloc_3300_, 5, v___x_3281_);
lean_ctor_set(v_reuseFailAlloc_3300_, 6, v_messages_3274_);
lean_ctor_set(v_reuseFailAlloc_3300_, 7, v_infoState_3275_);
lean_ctor_set(v_reuseFailAlloc_3300_, 8, v_snapshotTasks_3276_);
v___x_3283_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_mctx_3286_; lean_object* v_zetaDeltaFVarIds_3287_; lean_object* v_postponed_3288_; lean_object* v_diag_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3298_; 
v___x_3284_ = lean_st_ref_set(v___y_3249_, v___x_3283_);
v___x_3285_ = lean_st_ref_take(v___y_3246_);
v_mctx_3286_ = lean_ctor_get(v___x_3285_, 0);
v_zetaDeltaFVarIds_3287_ = lean_ctor_get(v___x_3285_, 2);
v_postponed_3288_ = lean_ctor_get(v___x_3285_, 3);
v_diag_3289_ = lean_ctor_get(v___x_3285_, 4);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; 
v_unused_3299_ = lean_ctor_get(v___x_3285_, 1);
lean_dec(v_unused_3299_);
v___x_3291_ = v___x_3285_;
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_diag_3289_);
lean_inc(v_postponed_3288_);
lean_inc(v_zetaDeltaFVarIds_3287_);
lean_inc(v_mctx_3286_);
lean_dec(v___x_3285_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v___x_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_mctx_3286_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_zetaDeltaFVarIds_3287_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v_postponed_3288_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v_diag_3289_);
v___x_3295_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_st_ref_set(v___y_3246_, v___x_3295_);
v___y_3221_ = v_a_3263_;
v___y_3222_ = v_a_3265_;
v___y_3223_ = v___y_3247_;
v___y_3224_ = v___y_3249_;
goto v___jp_3220_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3263_);
return v___x_3264_;
}
}
else
{
lean_object* v___x_3304_; 
lean_dec_ref(v_expectedType_3184_);
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 0, v_inst_3183_);
v___x_3304_ = v___x_3258_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_inst_3183_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec_ref(v_expectedType_3184_);
lean_dec_ref(v_inst_3183_);
v_a_3307_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3255_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3255_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3184_);
lean_dec_ref(v_inst_3183_);
return v___x_3253_;
}
}
}
v___jp_3316_:
{
lean_object* v_options_3321_; uint8_t v_hasTrace_3322_; 
v_options_3321_ = lean_ctor_get(v___y_3319_, 2);
v_hasTrace_3322_ = lean_ctor_get_uint8(v_options_3321_, sizeof(void*)*1);
if (v_hasTrace_3322_ == 0)
{
v___y_3245_ = v___y_3317_;
v___y_3246_ = v___y_3318_;
v___y_3247_ = v___y_3319_;
v_options_3248_ = v_options_3321_;
v___y_3249_ = v___y_3320_;
goto v___jp_3244_;
}
else
{
lean_object* v_inheritedTraceOptions_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v_inheritedTraceOptions_3323_ = lean_ctor_get(v___y_3319_, 13);
v___x_3324_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_3325_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3323_, v_options_3321_, v___x_3324_);
if (v___x_3325_ == 0)
{
v___y_3245_ = v___y_3317_;
v___y_3246_ = v___y_3318_;
v___y_3247_ = v___y_3319_;
v_options_3248_ = v_options_3321_;
v___y_3249_ = v___y_3320_;
goto v___jp_3244_;
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3326_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_3183_);
v___x_3327_ = l_Lean_MessageData_ofExpr(v_inst_3183_);
v___x_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3315_, v___x_3328_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_dec_ref(v___x_3329_);
v___y_3245_ = v___y_3317_;
v___y_3246_ = v___y_3318_;
v___y_3247_ = v___y_3319_;
v_options_3248_ = v_options_3321_;
v___y_3249_ = v___y_3320_;
goto v___jp_3244_;
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v_expectedType_3184_);
lean_dec_ref(v_inst_3183_);
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
}
}
v___jp_3198_:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_enableRealizationsForConst(v___y_3199_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v___x_3203_, 0);
lean_dec(v_unused_3211_);
v___x_3205_ = v___x_3203_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_dec(v___x_3203_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___y_3200_);
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___y_3200_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec_ref(v___y_3200_);
v_a_3212_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3203_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3203_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
v___jp_3220_:
{
if (v_compile_3186_ == 0)
{
v___y_3199_ = v___y_3221_;
v___y_3200_ = v___y_3222_;
v___y_3201_ = v___y_3223_;
v___y_3202_ = v___y_3224_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_mk_empty_array_with_capacity(v___x_3225_);
lean_inc(v___y_3221_);
v___x_3227_ = lean_array_push(v___x_3226_, v___y_3221_);
v___x_3228_ = l_Lean_compileDecls(v___x_3227_, v_logCompileErrors_3187_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_dec_ref(v___x_3228_);
v___y_3199_ = v___y_3221_;
v___y_3200_ = v___y_3222_;
v___y_3201_ = v___y_3223_;
v___y_3202_ = v___y_3224_;
goto v___jp_3198_;
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
}
}
static double _init_l_Lean_Meta_wrapInstance___closed__1(void){
_start:
{
lean_object* v___x_3465_; double v___x_3466_; 
v___x_3465_ = lean_unsigned_to_nat(1000000000u);
v___x_3466_ = lean_float_of_nat(v___x_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(lean_object* v_upperBound_3467_, lean_object* v_fst_3468_, lean_object* v_args_3469_, uint8_t v___x_3470_, uint8_t v_compile_3471_, uint8_t v_logCompileErrors_3472_, uint8_t v___x_3473_, uint8_t v_isMeta_3474_, lean_object* v_val_3475_, lean_object* v_expectedType_3476_, lean_object* v_a_3477_, lean_object* v_b_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_a_3485_; lean_object* v___y_3490_; uint8_t v___x_3509_; 
v___x_3509_ = lean_nat_dec_lt(v_a_3477_, v_upperBound_3467_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_b_3478_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = lean_array_fget_borrowed(v_fst_3468_, v_a_3477_);
v___x_3512_ = l_Lean_Expr_mvarId_x21(v___x_3511_);
lean_inc(v___x_3512_);
v___x_3513_ = l_Lean_MVarId_getDecl(v___x_3512_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v_userName_3515_; lean_object* v_type_3516_; lean_object* v___x_3517_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref(v___x_3513_);
v_userName_3515_ = lean_ctor_get(v_a_3514_, 0);
lean_inc(v_userName_3515_);
v_type_3516_ = lean_ctor_get(v_a_3514_, 2);
lean_inc_ref(v_type_3516_);
lean_dec(v_a_3514_);
v___x_3517_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_3516_, v___y_3480_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc_n(v_a_3518_, 2);
lean_dec_ref(v___x_3517_);
v___x_3519_ = l_Lean_Meta_isProp(v_a_3518_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; lean_object* v_cls_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = lean_box(0);
v_cls_3522_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_3524_ = lean_array_fget_borrowed(v_args_3469_, v_a_3477_);
v___x_3525_ = lean_unbox(v_a_3520_);
lean_dec(v_a_3520_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_inc(v_a_3518_);
v___x_3526_ = l_Lean_Meta_isClass_x3f(v_a_3518_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3625_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3625_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3625_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_a_3532_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v_a_3541_; lean_object* v___y_3545_; 
if (lean_obj_tag(v_a_3527_) == 0)
{
if (v___x_3473_ == 0)
{
lean_object* v_options_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___f_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
lean_del_object(v___x_3529_);
v_options_3571_ = lean_ctor_get(v___y_3481_, 2);
v___x_3572_ = lean_box(v___x_3473_);
v___x_3573_ = lean_box(v___x_3470_);
v___x_3574_ = lean_box(v_compile_3471_);
v___x_3575_ = lean_box(v_logCompileErrors_3472_);
v___x_3576_ = lean_box(v_isMeta_3474_);
lean_inc(v_a_3518_);
lean_inc(v___x_3524_);
lean_inc(v___x_3512_);
v___f_3577_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3577_, 0, v___x_3512_);
lean_closure_set(v___f_3577_, 1, v___x_3524_);
lean_closure_set(v___f_3577_, 2, v___x_3521_);
lean_closure_set(v___f_3577_, 3, v_a_3518_);
lean_closure_set(v___f_3577_, 4, v___x_3572_);
lean_closure_set(v___f_3577_, 5, v___x_3573_);
lean_closure_set(v___f_3577_, 6, v___x_3574_);
lean_closure_set(v___f_3577_, 7, v___x_3575_);
lean_closure_set(v___f_3577_, 8, v___x_3576_);
v___x_3578_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3579_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3571_, v___x_3578_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; 
lean_dec_ref(v___f_3577_);
lean_dec(v_userName_3515_);
lean_inc(v___x_3524_);
v___x_3580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3512_, v___x_3524_, v___x_3521_, v_a_3518_, v___x_3473_, v___x_3470_, v_compile_3471_, v_logCompileErrors_3472_, v_isMeta_3474_, v___x_3521_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3580_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3581_; 
lean_inc(v_userName_3515_);
lean_inc(v_val_3475_);
v___x_3581_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_3475_, v_userName_3515_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3616_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref(v___x_3581_);
v_fst_3583_ = lean_ctor_get(v_a_3582_, 0);
v_snd_3584_ = lean_ctor_get(v_a_3582_, 1);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_a_3582_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3586_ = v_a_3582_;
v_isShared_3587_ = v_isSharedCheck_3616_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_snd_3584_);
lean_inc(v_fst_3583_);
lean_dec(v_a_3582_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3616_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
uint8_t v___x_3588_; 
v___x_3588_ = lean_name_eq(v_fst_3583_, v_val_3475_);
if (v___x_3588_ == 0)
{
lean_object* v___x_3589_; 
lean_dec(v_a_3518_);
v___x_3589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3522_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; uint8_t v___x_3591_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref(v___x_3589_);
v___x_3591_ = lean_unbox(v_a_3590_);
lean_dec(v_a_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; 
lean_del_object(v___x_3586_);
lean_dec(v_userName_3515_);
lean_inc_ref(v_expectedType_3476_);
lean_inc(v_val_3475_);
v___x_3592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_3475_, v_fst_3583_, v_expectedType_3476_, v___f_3523_, v___f_3577_, v___x_3521_, v_cls_3522_, v_snd_3584_, v___x_3512_, v___x_3521_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3592_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3593_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_3594_ = l_Lean_MessageData_ofName(v_userName_3515_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 7);
lean_ctor_set(v___x_3586_, 1, v___x_3594_);
lean_ctor_set(v___x_3586_, 0, v___x_3593_);
v___x_3596_ = v___x_3586_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3597_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_3598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
lean_inc(v_fst_3583_);
v___x_3599_ = l_Lean_MessageData_ofName(v_fst_3583_);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3522_, v___x_3602_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
lean_inc_ref(v_expectedType_3476_);
lean_inc(v_val_3475_);
v___x_3605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_3475_, v_fst_3583_, v_expectedType_3476_, v___f_3523_, v___f_3577_, v___x_3521_, v_cls_3522_, v_snd_3584_, v___x_3512_, v_a_3604_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3605_;
goto v___jp_3489_;
}
else
{
lean_dec(v_snd_3584_);
lean_dec(v_fst_3583_);
lean_dec_ref(v___f_3577_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
return v___x_3603_;
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_del_object(v___x_3586_);
lean_dec(v_snd_3584_);
lean_dec(v_fst_3583_);
lean_dec_ref(v___f_3577_);
lean_dec(v_userName_3515_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3607_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3589_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3589_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v___x_3615_; 
lean_del_object(v___x_3586_);
lean_dec(v_snd_3584_);
lean_dec(v_fst_3583_);
lean_dec_ref(v___f_3577_);
lean_dec(v_userName_3515_);
lean_inc(v___x_3524_);
v___x_3615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3512_, v___x_3524_, v___x_3521_, v_a_3518_, v___x_3473_, v___x_3470_, v_compile_3471_, v_logCompileErrors_3472_, v_isMeta_3474_, v___x_3521_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3615_;
goto v___jp_3489_;
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v___f_3577_);
lean_dec(v_a_3518_);
lean_dec(v_userName_3515_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3617_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3581_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3581_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
else
{
lean_dec(v_userName_3515_);
goto v___jp_3549_;
}
}
else
{
lean_dec_ref(v_a_3527_);
lean_dec(v_userName_3515_);
goto v___jp_3549_;
}
v___jp_3531_:
{
lean_object* v___x_3533_; 
lean_inc(v___x_3524_);
v___x_3533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3524_, v_a_3518_, v_compile_3471_, v_logCompileErrors_3472_, v_isMeta_3474_, v___x_3512_, v___x_3521_, v_a_3532_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3533_;
goto v___jp_3489_;
}
v___jp_3534_:
{
if (v___y_3536_ == 0)
{
lean_dec_ref(v___y_3535_);
lean_del_object(v___x_3529_);
v_a_3532_ = v___x_3521_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3538_; 
lean_dec(v_a_3518_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set_tag(v___x_3529_, 1);
lean_ctor_set(v___x_3529_, 0, v___y_3535_);
v___x_3538_ = v___x_3529_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___y_3535_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
v___jp_3540_:
{
uint8_t v___x_3542_; 
v___x_3542_ = l_Lean_Exception_isInterrupt(v_a_3541_);
if (v___x_3542_ == 0)
{
uint8_t v___x_3543_; 
lean_inc_ref(v_a_3541_);
v___x_3543_ = l_Lean_Exception_isRuntime(v_a_3541_);
v___y_3535_ = v_a_3541_;
v___y_3536_ = v___x_3543_;
goto v___jp_3534_;
}
else
{
v___y_3535_ = v_a_3541_;
v___y_3536_ = v___x_3542_;
goto v___jp_3534_;
}
}
v___jp_3544_:
{
if (lean_obj_tag(v___y_3545_) == 0)
{
lean_object* v_a_3546_; 
lean_del_object(v___x_3529_);
v_a_3546_ = lean_ctor_get(v___y_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref(v___y_3545_);
if (lean_obj_tag(v_a_3546_) == 0)
{
lean_dec(v_a_3518_);
lean_dec(v___x_3512_);
v_a_3485_ = v___x_3521_;
goto v___jp_3484_;
}
else
{
lean_object* v_a_3547_; 
v_a_3547_ = lean_ctor_get(v_a_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref(v_a_3546_);
v_a_3532_ = v_a_3547_;
goto v___jp_3531_;
}
}
else
{
lean_object* v_a_3548_; 
v_a_3548_ = lean_ctor_get(v___y_3545_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___y_3545_);
v_a_3541_ = v_a_3548_;
goto v___jp_3540_;
}
}
v___jp_3549_:
{
lean_object* v_options_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_options_3550_ = lean_ctor_get(v___y_3481_, 2);
v___x_3551_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3552_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3550_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; 
lean_del_object(v___x_3529_);
lean_inc(v___x_3524_);
v___x_3553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3524_, v_a_3518_, v_compile_3471_, v_logCompileErrors_3472_, v_isMeta_3474_, v___x_3512_, v___x_3521_, v___x_3521_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3553_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_box(0);
lean_inc(v_a_3518_);
v___x_3555_ = l_Lean_Meta_trySynthInstance(v_a_3518_, v___x_3554_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
if (lean_obj_tag(v_a_3556_) == 1)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; 
v_a_3557_ = lean_ctor_get(v_a_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref(v_a_3556_);
v___x_3558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3522_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; uint8_t v___x_3560_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = lean_unbox(v_a_3559_);
lean_dec(v_a_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_inc(v___x_3512_);
v___x_3561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3512_, v_a_3557_, v___x_3521_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3545_ = v___x_3561_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3562_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_3557_);
v___x_3563_ = l_Lean_MessageData_ofExpr(v_a_3557_);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3522_, v___x_3564_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref(v___x_3565_);
lean_inc(v___x_3512_);
v___x_3567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3512_, v_a_3557_, v_a_3566_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3545_ = v___x_3567_;
goto v___jp_3544_;
}
else
{
lean_object* v_a_3568_; 
lean_dec(v_a_3557_);
v_a_3568_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3568_);
lean_dec_ref(v___x_3565_);
v_a_3541_ = v_a_3568_;
goto v___jp_3540_;
}
}
}
else
{
lean_object* v_a_3569_; 
lean_dec(v_a_3557_);
v_a_3569_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3558_);
v_a_3541_ = v_a_3569_;
goto v___jp_3540_;
}
}
else
{
lean_dec(v_a_3556_);
lean_del_object(v___x_3529_);
v_a_3532_ = v___x_3521_;
goto v___jp_3531_;
}
}
else
{
lean_object* v_a_3570_; 
v_a_3570_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3570_);
lean_dec_ref(v___x_3555_);
v_a_3541_ = v_a_3570_;
goto v___jp_3540_;
}
}
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_a_3518_);
lean_dec(v_userName_3515_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3626_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3526_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3526_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_object* v___x_3634_; 
lean_dec(v_userName_3515_);
lean_inc(v___y_3482_);
lean_inc_ref(v___y_3481_);
lean_inc(v___y_3480_);
lean_inc_ref(v___y_3479_);
lean_inc(v___x_3524_);
v___x_3634_ = lean_infer_type(v___x_3524_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3636_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc_n(v_a_3635_, 2);
lean_dec_ref(v___x_3634_);
lean_inc(v_a_3518_);
v___x_3636_ = l_Lean_Meta_isExprDefEq(v_a_3518_, v_a_3635_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___f_3638_; uint8_t v___x_3639_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref(v___x_3636_);
v___f_3638_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_3639_ = lean_unbox(v_a_3637_);
lean_dec(v_a_3637_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3522_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; uint8_t v___x_3642_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3640_);
v___x_3642_ = lean_unbox(v_a_3641_);
lean_dec(v_a_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; 
lean_dec(v_a_3635_);
lean_inc(v___x_3524_);
v___x_3643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3518_, v___x_3524_, v___x_3470_, v___x_3512_, v___f_3638_, v___x_3521_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3643_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3644_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_3477_);
v___x_3645_ = l_Nat_reprFast(v_a_3477_);
v___x_3646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
v___x_3647_ = l_Lean_MessageData_ofFormat(v___x_3646_);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3644_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
lean_inc(v_a_3518_);
v___x_3651_ = l_Lean_MessageData_ofExpr(v_a_3518_);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3650_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = l_Lean_MessageData_ofExpr(v_a_3635_);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
lean_inc(v___x_3524_);
v___x_3659_ = l_Lean_MessageData_ofExpr(v___x_3524_);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3522_, v___x_3660_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
lean_inc(v___x_3524_);
v___x_3663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3518_, v___x_3524_, v___x_3470_, v___x_3512_, v___f_3638_, v_a_3662_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3663_;
goto v___jp_3489_;
}
else
{
lean_dec(v_a_3518_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
return v___x_3661_;
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_a_3635_);
lean_dec(v_a_3518_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3664_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3640_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3640_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v___x_3672_; 
lean_dec(v_a_3635_);
lean_dec(v_a_3518_);
lean_inc(v___x_3524_);
v___x_3672_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3512_, v___x_3524_, v___y_3480_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3674_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref(v___x_3672_);
v___x_3674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_3521_, v_a_3673_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
v___y_3490_ = v___x_3674_;
goto v___jp_3489_;
}
else
{
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
return v___x_3672_;
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_a_3635_);
lean_dec(v_a_3518_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3675_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3636_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3636_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_a_3518_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3683_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3634_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3634_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_a_3518_);
lean_dec(v_userName_3515_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3691_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3519_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3519_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_userName_3515_);
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3699_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3517_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3517_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec(v___x_3512_);
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3707_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3513_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3513_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
v___jp_3484_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_unsigned_to_nat(1u);
v___x_3487_ = lean_nat_add(v_a_3477_, v___x_3486_);
lean_dec(v_a_3477_);
v_a_3477_ = v___x_3487_;
v_b_3478_ = v_a_3485_;
goto _start;
}
v___jp_3489_:
{
if (lean_obj_tag(v___y_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3500_; 
v_a_3491_ = lean_ctor_get(v___y_3490_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___y_3490_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3493_ = v___y_3490_;
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___y_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
if (lean_obj_tag(v_a_3491_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; 
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3495_ = lean_ctor_get(v_a_3491_, 0);
lean_inc(v_a_3495_);
lean_dec_ref(v_a_3491_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_a_3495_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3495_);
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
lean_object* v_a_3499_; 
lean_del_object(v___x_3493_);
v_a_3499_ = lean_ctor_get(v_a_3491_, 0);
lean_inc(v_a_3499_);
lean_dec_ref(v_a_3491_);
v_a_3485_ = v_a_3499_;
goto v___jp_3484_;
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec(v_a_3477_);
lean_dec_ref(v_expectedType_3476_);
lean_dec(v_val_3475_);
v_a_3501_ = lean_ctor_get(v___y_3490_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___y_3490_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___y_3490_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___y_3490_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object* v_upperBound_3715_, lean_object* v_fst_3716_, lean_object* v_args_3717_, uint8_t v___x_3718_, uint8_t v_compile_3719_, uint8_t v_logCompileErrors_3720_, uint8_t v___x_3721_, uint8_t v_isMeta_3722_, lean_object* v_val_3723_, lean_object* v_expectedType_3724_, lean_object* v_a_3725_, lean_object* v_b_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_a_3733_; lean_object* v___y_3738_; uint8_t v___x_3757_; 
v___x_3757_ = lean_nat_dec_lt(v_a_3725_, v_upperBound_3715_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; 
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v_b_3726_);
return v___x_3758_;
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = lean_array_fget_borrowed(v_fst_3716_, v_a_3725_);
v___x_3760_ = l_Lean_Expr_mvarId_x21(v___x_3759_);
lean_inc(v___x_3760_);
v___x_3761_ = l_Lean_MVarId_getDecl(v___x_3760_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v_userName_3763_; lean_object* v_type_3764_; lean_object* v___x_3765_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref(v___x_3761_);
v_userName_3763_ = lean_ctor_get(v_a_3762_, 0);
lean_inc(v_userName_3763_);
v_type_3764_ = lean_ctor_get(v_a_3762_, 2);
lean_inc_ref(v_type_3764_);
lean_dec(v_a_3762_);
v___x_3765_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_3764_, v___y_3728_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3767_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc_n(v_a_3766_, 2);
lean_dec_ref(v___x_3765_);
v___x_3767_ = l_Lean_Meta_isProp(v_a_3766_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; lean_object* v_cls_3770_; lean_object* v___f_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = lean_box(0);
v_cls_3770_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_3772_ = lean_array_fget_borrowed(v_args_3717_, v_a_3725_);
v___x_3773_ = lean_unbox(v_a_3768_);
lean_dec(v_a_3768_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; 
lean_inc(v_a_3766_);
v___x_3774_ = l_Lean_Meta_isClass_x3f(v_a_3766_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3873_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3777_ = v___x_3774_;
v_isShared_3778_ = v_isSharedCheck_3873_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3774_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3873_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v_a_3780_; lean_object* v___y_3783_; uint8_t v___y_3784_; lean_object* v_a_3789_; lean_object* v___y_3793_; 
if (lean_obj_tag(v_a_3775_) == 0)
{
if (v___x_3721_ == 0)
{
lean_object* v_options_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___f_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
lean_del_object(v___x_3777_);
v_options_3819_ = lean_ctor_get(v___y_3729_, 2);
v___x_3820_ = lean_box(v___x_3721_);
v___x_3821_ = lean_box(v___x_3718_);
v___x_3822_ = lean_box(v_compile_3719_);
v___x_3823_ = lean_box(v_logCompileErrors_3720_);
v___x_3824_ = lean_box(v_isMeta_3722_);
lean_inc(v_a_3766_);
lean_inc(v___x_3772_);
lean_inc(v___x_3760_);
v___f_3825_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3825_, 0, v___x_3760_);
lean_closure_set(v___f_3825_, 1, v___x_3772_);
lean_closure_set(v___f_3825_, 2, v___x_3769_);
lean_closure_set(v___f_3825_, 3, v_a_3766_);
lean_closure_set(v___f_3825_, 4, v___x_3820_);
lean_closure_set(v___f_3825_, 5, v___x_3821_);
lean_closure_set(v___f_3825_, 6, v___x_3822_);
lean_closure_set(v___f_3825_, 7, v___x_3823_);
lean_closure_set(v___f_3825_, 8, v___x_3824_);
v___x_3826_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3827_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3819_, v___x_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec_ref(v___f_3825_);
lean_dec(v_userName_3763_);
lean_inc(v___x_3772_);
v___x_3828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3760_, v___x_3772_, v___x_3769_, v_a_3766_, v___x_3721_, v___x_3718_, v_compile_3719_, v_logCompileErrors_3720_, v_isMeta_3722_, v___x_3769_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3828_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3829_; 
lean_inc(v_userName_3763_);
lean_inc(v_val_3723_);
v___x_3829_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_3723_, v_userName_3763_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v_fst_3831_; lean_object* v_snd_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3864_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v_fst_3831_ = lean_ctor_get(v_a_3830_, 0);
v_snd_3832_ = lean_ctor_get(v_a_3830_, 1);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_a_3830_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3834_ = v_a_3830_;
v_isShared_3835_ = v_isSharedCheck_3864_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_snd_3832_);
lean_inc(v_fst_3831_);
lean_dec(v_a_3830_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3864_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_name_eq(v_fst_3831_, v_val_3723_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; 
lean_dec(v_a_3766_);
v___x_3837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3770_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; uint8_t v___x_3839_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref(v___x_3837_);
v___x_3839_ = lean_unbox(v_a_3838_);
lean_dec(v_a_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_del_object(v___x_3834_);
lean_dec(v_userName_3763_);
lean_inc_ref(v_expectedType_3724_);
lean_inc(v_val_3723_);
v___x_3840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_3723_, v_fst_3831_, v_expectedType_3724_, v___f_3771_, v___f_3825_, v___x_3769_, v_cls_3770_, v_snd_3832_, v___x_3760_, v___x_3769_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3840_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3841_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_3842_ = l_Lean_MessageData_ofName(v_userName_3763_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set_tag(v___x_3834_, 7);
lean_ctor_set(v___x_3834_, 1, v___x_3842_);
lean_ctor_set(v___x_3834_, 0, v___x_3841_);
v___x_3844_ = v___x_3834_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3845_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_3846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
lean_inc(v_fst_3831_);
v___x_3847_ = l_Lean_MessageData_ofName(v_fst_3831_);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3770_, v___x_3850_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref(v___x_3851_);
lean_inc_ref(v_expectedType_3724_);
lean_inc(v_val_3723_);
v___x_3853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_3723_, v_fst_3831_, v_expectedType_3724_, v___f_3771_, v___f_3825_, v___x_3769_, v_cls_3770_, v_snd_3832_, v___x_3760_, v_a_3852_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3853_;
goto v___jp_3737_;
}
else
{
lean_dec(v_snd_3832_);
lean_dec(v_fst_3831_);
lean_dec_ref(v___f_3825_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
return v___x_3851_;
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_del_object(v___x_3834_);
lean_dec(v_snd_3832_);
lean_dec(v_fst_3831_);
lean_dec_ref(v___f_3825_);
lean_dec(v_userName_3763_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3855_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3837_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3837_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
lean_object* v___x_3863_; 
lean_del_object(v___x_3834_);
lean_dec(v_snd_3832_);
lean_dec(v_fst_3831_);
lean_dec_ref(v___f_3825_);
lean_dec(v_userName_3763_);
lean_inc(v___x_3772_);
v___x_3863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3760_, v___x_3772_, v___x_3769_, v_a_3766_, v___x_3721_, v___x_3718_, v_compile_3719_, v_logCompileErrors_3720_, v_isMeta_3722_, v___x_3769_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3863_;
goto v___jp_3737_;
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v___f_3825_);
lean_dec(v_a_3766_);
lean_dec(v_userName_3763_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3865_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3829_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3829_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
else
{
lean_dec(v_userName_3763_);
goto v___jp_3797_;
}
}
else
{
lean_dec_ref(v_a_3775_);
lean_dec(v_userName_3763_);
goto v___jp_3797_;
}
v___jp_3779_:
{
lean_object* v___x_3781_; 
lean_inc(v___x_3772_);
v___x_3781_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3772_, v_a_3766_, v_compile_3719_, v_logCompileErrors_3720_, v_isMeta_3722_, v___x_3760_, v___x_3769_, v_a_3780_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3781_;
goto v___jp_3737_;
}
v___jp_3782_:
{
if (v___y_3784_ == 0)
{
lean_dec_ref(v___y_3783_);
lean_del_object(v___x_3777_);
v_a_3780_ = v___x_3769_;
goto v___jp_3779_;
}
else
{
lean_object* v___x_3786_; 
lean_dec(v_a_3766_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set_tag(v___x_3777_, 1);
lean_ctor_set(v___x_3777_, 0, v___y_3783_);
v___x_3786_ = v___x_3777_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___y_3783_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
v___jp_3788_:
{
uint8_t v___x_3790_; 
v___x_3790_ = l_Lean_Exception_isInterrupt(v_a_3789_);
if (v___x_3790_ == 0)
{
uint8_t v___x_3791_; 
lean_inc_ref(v_a_3789_);
v___x_3791_ = l_Lean_Exception_isRuntime(v_a_3789_);
v___y_3783_ = v_a_3789_;
v___y_3784_ = v___x_3791_;
goto v___jp_3782_;
}
else
{
v___y_3783_ = v_a_3789_;
v___y_3784_ = v___x_3790_;
goto v___jp_3782_;
}
}
v___jp_3792_:
{
if (lean_obj_tag(v___y_3793_) == 0)
{
lean_object* v_a_3794_; 
lean_del_object(v___x_3777_);
v_a_3794_ = lean_ctor_get(v___y_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___y_3793_);
if (lean_obj_tag(v_a_3794_) == 0)
{
lean_dec(v_a_3766_);
lean_dec(v___x_3760_);
v_a_3733_ = v___x_3769_;
goto v___jp_3732_;
}
else
{
lean_object* v_a_3795_; 
v_a_3795_ = lean_ctor_get(v_a_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v_a_3794_);
v_a_3780_ = v_a_3795_;
goto v___jp_3779_;
}
}
else
{
lean_object* v_a_3796_; 
v_a_3796_ = lean_ctor_get(v___y_3793_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___y_3793_);
v_a_3789_ = v_a_3796_;
goto v___jp_3788_;
}
}
v___jp_3797_:
{
lean_object* v_options_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
v_options_3798_ = lean_ctor_get(v___y_3729_, 2);
v___x_3799_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3800_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3798_, v___x_3799_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; 
lean_del_object(v___x_3777_);
lean_inc(v___x_3772_);
v___x_3801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3772_, v_a_3766_, v_compile_3719_, v_logCompileErrors_3720_, v_isMeta_3722_, v___x_3760_, v___x_3769_, v___x_3769_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3801_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_box(0);
lean_inc(v_a_3766_);
v___x_3803_ = l_Lean_Meta_trySynthInstance(v_a_3766_, v___x_3802_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v___x_3803_);
if (lean_obj_tag(v_a_3804_) == 1)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_ctor_get(v_a_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref(v_a_3804_);
v___x_3806_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3770_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; uint8_t v___x_3808_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3806_);
v___x_3808_ = lean_unbox(v_a_3807_);
lean_dec(v_a_3807_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
lean_inc(v___x_3760_);
v___x_3809_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3760_, v_a_3805_, v___x_3769_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3793_ = v___x_3809_;
goto v___jp_3792_;
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3810_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_3805_);
v___x_3811_ = l_Lean_MessageData_ofExpr(v_a_3805_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3770_, v___x_3812_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3815_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref(v___x_3813_);
lean_inc(v___x_3760_);
v___x_3815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3760_, v_a_3805_, v_a_3814_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3793_ = v___x_3815_;
goto v___jp_3792_;
}
else
{
lean_object* v_a_3816_; 
lean_dec(v_a_3805_);
v_a_3816_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3816_);
lean_dec_ref(v___x_3813_);
v_a_3789_ = v_a_3816_;
goto v___jp_3788_;
}
}
}
else
{
lean_object* v_a_3817_; 
lean_dec(v_a_3805_);
v_a_3817_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3817_);
lean_dec_ref(v___x_3806_);
v_a_3789_ = v_a_3817_;
goto v___jp_3788_;
}
}
else
{
lean_dec(v_a_3804_);
lean_del_object(v___x_3777_);
v_a_3780_ = v___x_3769_;
goto v___jp_3779_;
}
}
else
{
lean_object* v_a_3818_; 
v_a_3818_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3803_);
v_a_3789_ = v_a_3818_;
goto v___jp_3788_;
}
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_a_3766_);
lean_dec(v_userName_3763_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3874_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3774_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3774_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_object* v___x_3882_; 
lean_dec(v_userName_3763_);
lean_inc(v___y_3730_);
lean_inc_ref(v___y_3729_);
lean_inc(v___y_3728_);
lean_inc_ref(v___y_3727_);
lean_inc(v___x_3772_);
v___x_3882_ = lean_infer_type(v___x_3772_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc_n(v_a_3883_, 2);
lean_dec_ref(v___x_3882_);
lean_inc(v_a_3766_);
v___x_3884_ = l_Lean_Meta_isExprDefEq(v_a_3766_, v_a_3883_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___f_3886_; uint8_t v___x_3887_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref(v___x_3884_);
v___f_3886_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_3887_ = lean_unbox(v_a_3885_);
lean_dec(v_a_3885_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; 
v___x_3888_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3770_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; uint8_t v___x_3890_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref(v___x_3888_);
v___x_3890_ = lean_unbox(v_a_3889_);
lean_dec(v_a_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; 
lean_dec(v_a_3883_);
lean_inc(v___x_3772_);
v___x_3891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3766_, v___x_3772_, v___x_3718_, v___x_3760_, v___f_3886_, v___x_3769_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3891_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3892_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_3725_);
v___x_3893_ = l_Nat_reprFast(v_a_3725_);
v___x_3894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
v___x_3895_ = l_Lean_MessageData_ofFormat(v___x_3894_);
v___x_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3892_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
lean_inc(v_a_3766_);
v___x_3899_ = l_Lean_MessageData_ofExpr(v_a_3766_);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3898_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
v___x_3901_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = l_Lean_MessageData_ofExpr(v_a_3883_);
v___x_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3902_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_3906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3904_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
lean_inc(v___x_3772_);
v___x_3907_ = l_Lean_MessageData_ofExpr(v___x_3772_);
v___x_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3906_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3770_, v___x_3908_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3909_);
lean_inc(v___x_3772_);
v___x_3911_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3766_, v___x_3772_, v___x_3718_, v___x_3760_, v___f_3886_, v_a_3910_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3911_;
goto v___jp_3737_;
}
else
{
lean_dec(v_a_3766_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
return v___x_3909_;
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec(v_a_3883_);
lean_dec(v_a_3766_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3912_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3888_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3888_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v___x_3920_; 
lean_dec(v_a_3883_);
lean_dec(v_a_3766_);
lean_inc(v___x_3772_);
v___x_3920_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3760_, v___x_3772_, v___y_3728_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3922_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref(v___x_3920_);
v___x_3922_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_3769_, v_a_3921_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
v___y_3738_ = v___x_3922_;
goto v___jp_3737_;
}
else
{
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
return v___x_3920_;
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_a_3883_);
lean_dec(v_a_3766_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3923_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3884_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3884_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_a_3766_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3931_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3882_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3882_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec(v_a_3766_);
lean_dec(v_userName_3763_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3939_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3767_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3767_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec(v_userName_3763_);
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3947_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3765_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3765_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v___x_3760_);
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3955_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3761_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3761_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
v___jp_3732_:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = lean_unsigned_to_nat(1u);
v___x_3735_ = lean_nat_add(v_a_3725_, v___x_3734_);
lean_dec(v_a_3725_);
v___x_3736_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(v_upperBound_3715_, v_fst_3716_, v_args_3717_, v___x_3718_, v_compile_3719_, v_logCompileErrors_3720_, v___x_3721_, v_isMeta_3722_, v_val_3723_, v_expectedType_3724_, v___x_3735_, v_a_3733_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
return v___x_3736_;
}
v___jp_3737_:
{
if (lean_obj_tag(v___y_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3748_; 
v_a_3739_ = lean_ctor_get(v___y_3738_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___y_3738_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3741_ = v___y_3738_;
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___y_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
if (lean_obj_tag(v_a_3739_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; 
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3743_ = lean_ctor_get(v_a_3739_, 0);
lean_inc(v_a_3743_);
lean_dec_ref(v_a_3739_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v_a_3743_);
v___x_3745_ = v___x_3741_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
else
{
lean_object* v_a_3747_; 
lean_del_object(v___x_3741_);
v_a_3747_ = lean_ctor_get(v_a_3739_, 0);
lean_inc(v_a_3747_);
lean_dec_ref(v_a_3739_);
v_a_3733_ = v_a_3747_;
goto v___jp_3732_;
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3724_);
lean_dec(v_val_3723_);
v_a_3749_ = lean_ctor_get(v___y_3738_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___y_3738_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___y_3738_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___y_3738_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(lean_object* v_inst_3963_, lean_object* v_expectedType_3964_, uint8_t v___x_3965_, uint8_t v___x_3966_, uint8_t v_compile_3967_, uint8_t v_logCompileErrors_3968_, uint8_t v_isMeta_3969_, lean_object* v_val_3970_, lean_object* v_x_3971_, lean_object* v_x_3972_, lean_object* v_x_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v_options_4022_; lean_object* v___y_4023_; 
if (lean_obj_tag(v_x_3971_) == 5)
{
lean_object* v_fn_4089_; lean_object* v_arg_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v_fn_4089_ = lean_ctor_get(v_x_3971_, 0);
lean_inc_ref(v_fn_4089_);
v_arg_4090_ = lean_ctor_get(v_x_3971_, 1);
lean_inc_ref(v_arg_4090_);
lean_dec_ref(v_x_3971_);
v___x_4091_ = lean_array_set(v_x_3972_, v_x_3973_, v_arg_4090_);
v___x_4092_ = lean_unsigned_to_nat(1u);
v___x_4093_ = lean_nat_sub(v_x_3973_, v___x_4092_);
lean_dec(v_x_3973_);
v_x_3971_ = v_fn_4089_;
v_x_3972_ = v___x_4091_;
v_x_3973_ = v___x_4093_;
goto _start;
}
else
{
lean_object* v_cls_4095_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___x_4118_; 
lean_dec(v_x_3973_);
v_cls_4095_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4118_ = l_Lean_Expr_constName_x3f(v_x_3971_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_dec_ref(v_x_3972_);
lean_dec_ref(v_x_3971_);
lean_dec(v_val_3970_);
v___y_4097_ = v___y_3974_;
v___y_4098_ = v___y_3975_;
v___y_4099_ = v___y_3976_;
v___y_4100_ = v___y_3977_;
goto v___jp_4096_;
}
else
{
lean_object* v_val_4119_; lean_object* v___x_4120_; 
v_val_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_val_4119_);
lean_dec_ref(v___x_4118_);
v___x_4120_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4119_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref(v___x_4120_);
if (lean_obj_tag(v_a_4121_) == 6)
{
lean_object* v_val_4122_; lean_object* v___x_4123_; 
lean_dec_ref(v_inst_3963_);
v_val_4122_ = lean_ctor_get(v_a_4121_, 0);
lean_inc_ref(v_val_4122_);
lean_dec_ref(v_a_4121_);
lean_inc(v___y_3977_);
lean_inc_ref(v___y_3976_);
lean_inc(v___y_3975_);
lean_inc_ref(v___y_3974_);
lean_inc_ref(v_x_3971_);
v___x_4123_ = lean_infer_type(v_x_3971_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; uint8_t v___x_4125_; lean_object* v___x_4126_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref(v___x_4123_);
v___x_4125_ = 0;
v___x_4126_ = l_Lean_Meta_forallMetaTelescope(v_a_4124_, v___x_4125_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v_snd_4128_; lean_object* v_fst_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4228_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref(v___x_4126_);
v_snd_4128_ = lean_ctor_get(v_a_4127_, 1);
v_fst_4129_ = lean_ctor_get(v_a_4127_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_a_4127_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4131_ = v_a_4127_;
v_isShared_4132_ = v_isSharedCheck_4228_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_snd_4128_);
lean_inc(v_fst_4129_);
lean_dec(v_a_4127_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4228_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v_snd_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4226_; 
v_snd_4133_ = lean_ctor_get(v_snd_4128_, 1);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_snd_4128_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; 
v_unused_4227_ = lean_ctor_get(v_snd_4128_, 0);
lean_dec(v_unused_4227_);
v___x_4135_ = v_snd_4128_;
v_isShared_4136_ = v_isSharedCheck_4226_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_snd_4133_);
lean_dec(v_snd_4128_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4226_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
v___x_4137_ = lean_array_get_size(v_x_3972_);
v___x_4174_ = lean_array_get_size(v_fst_4129_);
v___x_4175_ = lean_nat_dec_eq(v___x_4137_, v___x_4174_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
lean_dec(v_snd_4133_);
lean_dec(v_fst_4129_);
lean_dec_ref(v_val_4122_);
lean_dec(v_val_3970_);
lean_dec_ref(v_expectedType_3964_);
v___x_4176_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_4177_ = l_Lean_MessageData_ofExpr(v_x_3971_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set_tag(v___x_4135_, 7);
lean_ctor_set(v___x_4135_, 1, v___x_4177_);
lean_ctor_set(v___x_4135_, 0, v___x_4176_);
v___x_4179_ = v___x_4135_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; lean_object* v___x_4182_; 
v___x_4180_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3);
if (v_isShared_4132_ == 0)
{
lean_ctor_set_tag(v___x_4131_, 7);
lean_ctor_set(v___x_4131_, 1, v___x_4180_);
lean_ctor_set(v___x_4131_, 0, v___x_4179_);
v___x_4182_ = v___x_4131_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4183_ = lean_array_to_list(v_x_3972_);
v___x_4184_ = lean_box(0);
v___x_4185_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_4183_, v___x_4184_);
v___x_4186_ = l_Lean_MessageData_ofList(v___x_4185_);
v___x_4187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4182_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4187_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
return v___x_4188_;
}
}
}
else
{
lean_object* v___x_4191_; 
lean_inc_ref(v_expectedType_3964_);
v___x_4191_ = l_Lean_Meta_isExprDefEq(v_expectedType_3964_, v_snd_4133_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; uint8_t v___x_4193_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref(v___x_4191_);
v___x_4193_ = lean_unbox(v_a_4192_);
lean_dec(v_a_4192_);
if (v___x_4193_ == 0)
{
lean_object* v_toConstantVal_4194_; lean_object* v_name_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
lean_dec(v_fst_4129_);
lean_dec_ref(v_x_3972_);
lean_dec_ref(v_x_3971_);
lean_dec(v_val_3970_);
v_toConstantVal_4194_ = lean_ctor_get(v_val_4122_, 0);
lean_inc_ref(v_toConstantVal_4194_);
lean_dec_ref(v_val_4122_);
v_name_4195_ = lean_ctor_get(v_toConstantVal_4194_, 0);
lean_inc(v_name_4195_);
lean_dec_ref(v_toConstantVal_4194_);
v___x_4196_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_4197_ = l_Lean_MessageData_ofExpr(v_expectedType_3964_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set_tag(v___x_4135_, 7);
lean_ctor_set(v___x_4135_, 1, v___x_4197_);
lean_ctor_set(v___x_4135_, 0, v___x_4196_);
v___x_4199_ = v___x_4135_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4200_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_4132_ == 0)
{
lean_ctor_set_tag(v___x_4131_, 7);
lean_ctor_set(v___x_4131_, 1, v___x_4200_);
lean_ctor_set(v___x_4131_, 0, v___x_4199_);
v___x_4202_ = v___x_4131_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4199_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v___x_4200_);
v___x_4202_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
v___x_4203_ = l_Lean_MessageData_ofConstName(v_name_4195_, v___x_3965_);
v___x_4204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4204_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4206_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4207_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
else
{
lean_del_object(v___x_4135_);
lean_del_object(v___x_4131_);
v___y_4139_ = v___y_3974_;
v___y_4140_ = v___y_3975_;
v___y_4141_ = v___y_3976_;
v___y_4142_ = v___y_3977_;
goto v___jp_4138_;
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_del_object(v___x_4135_);
lean_del_object(v___x_4131_);
lean_dec(v_fst_4129_);
lean_dec_ref(v_val_4122_);
lean_dec_ref(v_x_3972_);
lean_dec_ref(v_x_3971_);
lean_dec(v_val_3970_);
lean_dec_ref(v_expectedType_3964_);
v_a_4218_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4191_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4191_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
v___jp_4138_:
{
lean_object* v_numParams_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v_numParams_4143_ = lean_ctor_get(v_val_4122_, 3);
lean_inc(v_numParams_4143_);
lean_dec_ref(v_val_4122_);
v___x_4144_ = lean_box(0);
v___x_4145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4137_, v_fst_4129_, v_x_3972_, v___x_3966_, v_compile_3967_, v_logCompileErrors_3968_, v___x_3965_, v_isMeta_3969_, v_val_3970_, v_expectedType_3964_, v_numParams_4143_, v___x_4144_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec_ref(v_x_3972_);
if (lean_obj_tag(v___x_4145_) == 0)
{
size_t v_sz_4146_; size_t v___x_4147_; lean_object* v___x_4148_; 
lean_dec_ref(v___x_4145_);
v_sz_4146_ = lean_array_size(v_fst_4129_);
v___x_4147_ = ((size_t)0ULL);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_4146_, v___x_4147_, v_fst_4129_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4157_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4153_ = l_Lean_mkAppN(v_x_3971_, v_a_4149_);
lean_dec(v_a_4149_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4153_);
v___x_4155_ = v___x_4151_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v_x_3971_);
v_a_4158_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4148_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4148_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v_fst_4129_);
lean_dec_ref(v_x_3971_);
v_a_4166_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4145_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4145_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v_val_4122_);
lean_dec_ref(v_x_3972_);
lean_dec_ref(v_x_3971_);
lean_dec(v_val_3970_);
lean_dec_ref(v_expectedType_3964_);
v_a_4229_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4126_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4126_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_dec_ref(v_val_4122_);
lean_dec_ref(v_x_3972_);
lean_dec_ref(v_x_3971_);
lean_dec(v_val_3970_);
lean_dec_ref(v_expectedType_3964_);
return v___x_4123_;
}
}
else
{
lean_dec(v_a_4121_);
lean_dec_ref(v_x_3972_);
lean_dec_ref(v_x_3971_);
lean_dec(v_val_3970_);
v___y_4097_ = v___y_3974_;
v___y_4098_ = v___y_3975_;
v___y_4099_ = v___y_3976_;
v___y_4100_ = v___y_3977_;
goto v___jp_4096_;
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v_x_3972_);
lean_dec_ref(v_x_3971_);
lean_dec(v_val_3970_);
lean_dec_ref(v_expectedType_3964_);
lean_dec_ref(v_inst_3963_);
v_a_4237_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4120_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4120_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
v___jp_4096_:
{
lean_object* v_options_4101_; uint8_t v_hasTrace_4102_; 
v_options_4101_ = lean_ctor_get(v___y_4099_, 2);
v_hasTrace_4102_ = lean_ctor_get_uint8(v_options_4101_, sizeof(void*)*1);
if (v_hasTrace_4102_ == 0)
{
v___y_4019_ = v___y_4097_;
v___y_4020_ = v___y_4098_;
v___y_4021_ = v___y_4099_;
v_options_4022_ = v_options_4101_;
v___y_4023_ = v___y_4100_;
goto v___jp_4018_;
}
else
{
lean_object* v_inheritedTraceOptions_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_inheritedTraceOptions_4103_ = lean_ctor_get(v___y_4099_, 13);
v___x_4104_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_4105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4103_, v_options_4101_, v___x_4104_);
if (v___x_4105_ == 0)
{
v___y_4019_ = v___y_4097_;
v___y_4020_ = v___y_4098_;
v___y_4021_ = v___y_4099_;
v_options_4022_ = v_options_4101_;
v___y_4023_ = v___y_4100_;
goto v___jp_4018_;
}
else
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4106_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_3963_);
v___x_4107_ = l_Lean_MessageData_ofExpr(v_inst_3963_);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4095_, v___x_4108_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_dec_ref(v___x_4109_);
v___y_4019_ = v___y_4097_;
v___y_4020_ = v___y_4098_;
v___y_4021_ = v___y_4099_;
v_options_4022_ = v_options_4101_;
v___y_4023_ = v___y_4100_;
goto v___jp_4018_;
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_dec_ref(v_expectedType_3964_);
lean_dec_ref(v_inst_3963_);
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4109_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4109_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
}
v___jp_3979_:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_enableRealizationsForConst(v___y_3980_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3991_ == 0)
{
lean_object* v_unused_3992_; 
v_unused_3992_ = lean_ctor_get(v___x_3984_, 0);
lean_dec(v_unused_3992_);
v___x_3986_ = v___x_3984_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_dec(v___x_3984_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___y_3981_);
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___y_3981_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v___y_3981_);
v_a_3993_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3984_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3984_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
v___jp_4001_:
{
if (v_compile_3967_ == 0)
{
v___y_3980_ = v___y_4002_;
v___y_3981_ = v___y_4003_;
v___y_3982_ = v___y_4004_;
v___y_3983_ = v___y_4005_;
goto v___jp_3979_;
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4006_ = lean_unsigned_to_nat(1u);
v___x_4007_ = lean_mk_empty_array_with_capacity(v___x_4006_);
lean_inc(v___y_4002_);
v___x_4008_ = lean_array_push(v___x_4007_, v___y_4002_);
v___x_4009_ = l_Lean_compileDecls(v___x_4008_, v_logCompileErrors_3968_, v___y_4004_, v___y_4005_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_dec_ref(v___x_4009_);
v___y_3980_ = v___y_4002_;
v___y_3981_ = v___y_4003_;
v___y_3982_ = v___y_4004_;
v___y_3983_ = v___y_4005_;
goto v___jp_3979_;
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
v___jp_4018_:
{
lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4025_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4022_, v___x_4024_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; 
lean_dec_ref(v_expectedType_3964_);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v_inst_3963_);
return v___x_4026_;
}
else
{
lean_object* v___x_4027_; 
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4021_);
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
lean_inc_ref(v_inst_3963_);
v___x_4027_ = lean_infer_type(v_inst_3963_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4023_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4029_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref(v___x_4027_);
lean_inc_ref(v_expectedType_3964_);
v___x_4029_ = l_Lean_Meta_isExprDefEq(v_expectedType_3964_, v_a_4028_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4023_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4080_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4080_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4080_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
uint8_t v___x_4034_; 
v___x_4034_ = lean_unbox(v_a_4030_);
lean_dec(v_a_4030_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v_a_4037_; lean_object* v___x_4038_; 
lean_del_object(v___x_4032_);
v___x_4035_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_4036_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4035_, v___y_4023_);
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc_n(v_a_4037_, 2);
lean_dec_ref(v___x_4036_);
v___x_4038_ = l_Lean_Meta_mkAuxDefinition(v_a_4037_, v_expectedType_3964_, v_inst_3963_, v___x_3965_, v___x_3965_, v___x_3966_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4023_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; uint8_t v___x_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref(v___x_4038_);
v___x_4040_ = 3;
lean_inc(v_a_4037_);
v___x_4041_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4037_, v___x_4040_, v___y_4020_, v___y_4023_);
lean_dec_ref(v___x_4041_);
if (v_isMeta_3969_ == 0)
{
v___y_4002_ = v_a_4037_;
v___y_4003_ = v_a_4039_;
v___y_4004_ = v___y_4021_;
v___y_4005_ = v___y_4023_;
goto v___jp_4001_;
}
else
{
lean_object* v___x_4042_; lean_object* v_env_4043_; lean_object* v_nextMacroScope_4044_; lean_object* v_ngen_4045_; lean_object* v_auxDeclNGen_4046_; lean_object* v_traceState_4047_; lean_object* v_messages_4048_; lean_object* v_infoState_4049_; lean_object* v_snapshotTasks_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4075_; 
v___x_4042_ = lean_st_ref_take(v___y_4023_);
v_env_4043_ = lean_ctor_get(v___x_4042_, 0);
v_nextMacroScope_4044_ = lean_ctor_get(v___x_4042_, 1);
v_ngen_4045_ = lean_ctor_get(v___x_4042_, 2);
v_auxDeclNGen_4046_ = lean_ctor_get(v___x_4042_, 3);
v_traceState_4047_ = lean_ctor_get(v___x_4042_, 4);
v_messages_4048_ = lean_ctor_get(v___x_4042_, 6);
v_infoState_4049_ = lean_ctor_get(v___x_4042_, 7);
v_snapshotTasks_4050_ = lean_ctor_get(v___x_4042_, 8);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v___x_4042_, 5);
lean_dec(v_unused_4076_);
v___x_4052_ = v___x_4042_;
v_isShared_4053_ = v_isSharedCheck_4075_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_snapshotTasks_4050_);
lean_inc(v_infoState_4049_);
lean_inc(v_messages_4048_);
lean_inc(v_traceState_4047_);
lean_inc(v_auxDeclNGen_4046_);
lean_inc(v_ngen_4045_);
lean_inc(v_nextMacroScope_4044_);
lean_inc(v_env_4043_);
lean_dec(v___x_4042_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4075_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
lean_inc(v_a_4037_);
v___x_4054_ = l_Lean_markMeta(v_env_4043_, v_a_4037_);
v___x_4055_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 5, v___x_4055_);
lean_ctor_set(v___x_4052_, 0, v___x_4054_);
v___x_4057_ = v___x_4052_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_nextMacroScope_4044_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_ngen_4045_);
lean_ctor_set(v_reuseFailAlloc_4074_, 3, v_auxDeclNGen_4046_);
lean_ctor_set(v_reuseFailAlloc_4074_, 4, v_traceState_4047_);
lean_ctor_set(v_reuseFailAlloc_4074_, 5, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4074_, 6, v_messages_4048_);
lean_ctor_set(v_reuseFailAlloc_4074_, 7, v_infoState_4049_);
lean_ctor_set(v_reuseFailAlloc_4074_, 8, v_snapshotTasks_4050_);
v___x_4057_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v_mctx_4060_; lean_object* v_zetaDeltaFVarIds_4061_; lean_object* v_postponed_4062_; lean_object* v_diag_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4072_; 
v___x_4058_ = lean_st_ref_set(v___y_4023_, v___x_4057_);
v___x_4059_ = lean_st_ref_take(v___y_4020_);
v_mctx_4060_ = lean_ctor_get(v___x_4059_, 0);
v_zetaDeltaFVarIds_4061_ = lean_ctor_get(v___x_4059_, 2);
v_postponed_4062_ = lean_ctor_get(v___x_4059_, 3);
v_diag_4063_ = lean_ctor_get(v___x_4059_, 4);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4072_ == 0)
{
lean_object* v_unused_4073_; 
v_unused_4073_ = lean_ctor_get(v___x_4059_, 1);
lean_dec(v_unused_4073_);
v___x_4065_ = v___x_4059_;
v_isShared_4066_ = v_isSharedCheck_4072_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_diag_4063_);
lean_inc(v_postponed_4062_);
lean_inc(v_zetaDeltaFVarIds_4061_);
lean_inc(v_mctx_4060_);
lean_dec(v___x_4059_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4072_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4067_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 1, v___x_4067_);
v___x_4069_ = v___x_4065_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_mctx_4060_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4071_, 2, v_zetaDeltaFVarIds_4061_);
lean_ctor_set(v_reuseFailAlloc_4071_, 3, v_postponed_4062_);
lean_ctor_set(v_reuseFailAlloc_4071_, 4, v_diag_4063_);
v___x_4069_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; 
v___x_4070_ = lean_st_ref_set(v___y_4020_, v___x_4069_);
v___y_4002_ = v_a_4037_;
v___y_4003_ = v_a_4039_;
v___y_4004_ = v___y_4021_;
v___y_4005_ = v___y_4023_;
goto v___jp_4001_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4037_);
return v___x_4038_;
}
}
else
{
lean_object* v___x_4078_; 
lean_dec_ref(v_expectedType_3964_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v_inst_3963_);
v___x_4078_ = v___x_4032_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_inst_3963_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec_ref(v_expectedType_3964_);
lean_dec_ref(v_inst_3963_);
v_a_4081_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4029_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4029_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3964_);
lean_dec_ref(v_inst_3963_);
return v___x_4027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object* v_inst_4245_, lean_object* v_expectedType_4246_, uint8_t v___x_4247_, uint8_t v___x_4248_, uint8_t v_compile_4249_, uint8_t v_logCompileErrors_4250_, uint8_t v_isMeta_4251_, lean_object* v_val_4252_, lean_object* v_x_4253_, lean_object* v_x_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v_options_4304_; lean_object* v___y_4305_; 
if (lean_obj_tag(v_x_4253_) == 5)
{
lean_object* v_fn_4371_; lean_object* v_arg_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v_fn_4371_ = lean_ctor_get(v_x_4253_, 0);
lean_inc_ref(v_fn_4371_);
v_arg_4372_ = lean_ctor_get(v_x_4253_, 1);
lean_inc_ref(v_arg_4372_);
lean_dec_ref(v_x_4253_);
v___x_4373_ = lean_array_set(v_x_4254_, v_x_4255_, v_arg_4372_);
v___x_4374_ = lean_unsigned_to_nat(1u);
v___x_4375_ = lean_nat_sub(v_x_4255_, v___x_4374_);
v___x_4376_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(v_inst_4245_, v_expectedType_4246_, v___x_4247_, v___x_4248_, v_compile_4249_, v_logCompileErrors_4250_, v_isMeta_4251_, v_val_4252_, v_fn_4371_, v___x_4373_, v___x_4375_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
return v___x_4376_;
}
else
{
lean_object* v_cls_4377_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___x_4400_; 
v_cls_4377_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4400_ = l_Lean_Expr_constName_x3f(v_x_4253_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_dec_ref(v_x_4254_);
lean_dec_ref(v_x_4253_);
lean_dec(v_val_4252_);
v___y_4379_ = v___y_4256_;
v___y_4380_ = v___y_4257_;
v___y_4381_ = v___y_4258_;
v___y_4382_ = v___y_4259_;
goto v___jp_4378_;
}
else
{
lean_object* v_val_4401_; lean_object* v___x_4402_; 
v_val_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_val_4401_);
lean_dec_ref(v___x_4400_);
v___x_4402_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4401_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref(v___x_4402_);
if (lean_obj_tag(v_a_4403_) == 6)
{
lean_object* v_val_4404_; lean_object* v___x_4405_; 
lean_dec_ref(v_inst_4245_);
v_val_4404_ = lean_ctor_get(v_a_4403_, 0);
lean_inc_ref(v_val_4404_);
lean_dec_ref(v_a_4403_);
lean_inc(v___y_4259_);
lean_inc_ref(v___y_4258_);
lean_inc(v___y_4257_);
lean_inc_ref(v___y_4256_);
lean_inc_ref(v_x_4253_);
v___x_4405_ = lean_infer_type(v_x_4253_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; uint8_t v___x_4407_; lean_object* v___x_4408_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = 0;
v___x_4408_ = l_Lean_Meta_forallMetaTelescope(v_a_4406_, v___x_4407_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_snd_4410_; lean_object* v_fst_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4510_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref(v___x_4408_);
v_snd_4410_ = lean_ctor_get(v_a_4409_, 1);
v_fst_4411_ = lean_ctor_get(v_a_4409_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v_a_4409_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4413_ = v_a_4409_;
v_isShared_4414_ = v_isSharedCheck_4510_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_snd_4410_);
lean_inc(v_fst_4411_);
lean_dec(v_a_4409_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4510_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v_snd_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4508_; 
v_snd_4415_ = lean_ctor_get(v_snd_4410_, 1);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_snd_4410_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v_snd_4410_, 0);
lean_dec(v_unused_4509_);
v___x_4417_ = v_snd_4410_;
v_isShared_4418_ = v_isSharedCheck_4508_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_snd_4415_);
lean_dec(v_snd_4410_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4508_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4419_ = lean_array_get_size(v_x_4254_);
v___x_4456_ = lean_array_get_size(v_fst_4411_);
v___x_4457_ = lean_nat_dec_eq(v___x_4419_, v___x_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4461_; 
lean_dec(v_snd_4415_);
lean_dec(v_fst_4411_);
lean_dec_ref(v_val_4404_);
lean_dec(v_val_4252_);
lean_dec_ref(v_expectedType_4246_);
v___x_4458_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_4459_ = l_Lean_MessageData_ofExpr(v_x_4253_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set_tag(v___x_4417_, 7);
lean_ctor_set(v___x_4417_, 1, v___x_4459_);
lean_ctor_set(v___x_4417_, 0, v___x_4458_);
v___x_4461_ = v___x_4417_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4458_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4462_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3);
if (v_isShared_4414_ == 0)
{
lean_ctor_set_tag(v___x_4413_, 7);
lean_ctor_set(v___x_4413_, 1, v___x_4462_);
lean_ctor_set(v___x_4413_, 0, v___x_4461_);
v___x_4464_ = v___x_4413_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4461_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v___x_4462_);
v___x_4464_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4465_ = lean_array_to_list(v_x_4254_);
v___x_4466_ = lean_box(0);
v___x_4467_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_4465_, v___x_4466_);
v___x_4468_ = l_Lean_MessageData_ofList(v___x_4467_);
v___x_4469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4464_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
v___x_4470_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4469_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
return v___x_4470_;
}
}
}
else
{
lean_object* v___x_4473_; 
lean_inc_ref(v_expectedType_4246_);
v___x_4473_ = l_Lean_Meta_isExprDefEq(v_expectedType_4246_, v_snd_4415_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; uint8_t v___x_4475_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref(v___x_4473_);
v___x_4475_ = lean_unbox(v_a_4474_);
lean_dec(v_a_4474_);
if (v___x_4475_ == 0)
{
lean_object* v_toConstantVal_4476_; lean_object* v_name_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4481_; 
lean_dec(v_fst_4411_);
lean_dec_ref(v_x_4254_);
lean_dec_ref(v_x_4253_);
lean_dec(v_val_4252_);
v_toConstantVal_4476_ = lean_ctor_get(v_val_4404_, 0);
lean_inc_ref(v_toConstantVal_4476_);
lean_dec_ref(v_val_4404_);
v_name_4477_ = lean_ctor_get(v_toConstantVal_4476_, 0);
lean_inc(v_name_4477_);
lean_dec_ref(v_toConstantVal_4476_);
v___x_4478_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_4479_ = l_Lean_MessageData_ofExpr(v_expectedType_4246_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set_tag(v___x_4417_, 7);
lean_ctor_set(v___x_4417_, 1, v___x_4479_);
lean_ctor_set(v___x_4417_, 0, v___x_4478_);
v___x_4481_ = v___x_4417_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4478_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4479_);
v___x_4481_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
lean_object* v___x_4482_; lean_object* v___x_4484_; 
v___x_4482_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_4414_ == 0)
{
lean_ctor_set_tag(v___x_4413_, 7);
lean_ctor_set(v___x_4413_, 1, v___x_4482_);
lean_ctor_set(v___x_4413_, 0, v___x_4481_);
v___x_4484_ = v___x_4413_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
v___x_4485_ = l_Lean_MessageData_ofConstName(v_name_4477_, v___x_4247_);
v___x_4486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4484_);
lean_ctor_set(v___x_4486_, 1, v___x_4485_);
v___x_4487_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4486_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
v___x_4489_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4488_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4489_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
else
{
lean_del_object(v___x_4417_);
lean_del_object(v___x_4413_);
v___y_4421_ = v___y_4256_;
v___y_4422_ = v___y_4257_;
v___y_4423_ = v___y_4258_;
v___y_4424_ = v___y_4259_;
goto v___jp_4420_;
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_del_object(v___x_4417_);
lean_del_object(v___x_4413_);
lean_dec(v_fst_4411_);
lean_dec_ref(v_val_4404_);
lean_dec_ref(v_x_4254_);
lean_dec_ref(v_x_4253_);
lean_dec(v_val_4252_);
lean_dec_ref(v_expectedType_4246_);
v_a_4500_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4473_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4473_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
v___jp_4420_:
{
lean_object* v_numParams_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v_numParams_4425_ = lean_ctor_get(v_val_4404_, 3);
lean_inc(v_numParams_4425_);
lean_dec_ref(v_val_4404_);
v___x_4426_ = lean_box(0);
v___x_4427_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4419_, v_fst_4411_, v_x_4254_, v___x_4248_, v_compile_4249_, v_logCompileErrors_4250_, v___x_4247_, v_isMeta_4251_, v_val_4252_, v_expectedType_4246_, v_numParams_4425_, v___x_4426_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec_ref(v_x_4254_);
if (lean_obj_tag(v___x_4427_) == 0)
{
size_t v_sz_4428_; size_t v___x_4429_; lean_object* v___x_4430_; 
lean_dec_ref(v___x_4427_);
v_sz_4428_ = lean_array_size(v_fst_4411_);
v___x_4429_ = ((size_t)0ULL);
v___x_4430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_4428_, v___x_4429_, v_fst_4411_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4439_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = l_Lean_mkAppN(v_x_4253_, v_a_4431_);
lean_dec(v_a_4431_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4435_);
v___x_4437_ = v___x_4433_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec_ref(v_x_4253_);
v_a_4440_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4430_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4430_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
else
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec(v_fst_4411_);
lean_dec_ref(v_x_4253_);
v_a_4448_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4427_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4427_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec_ref(v_val_4404_);
lean_dec_ref(v_x_4254_);
lean_dec_ref(v_x_4253_);
lean_dec(v_val_4252_);
lean_dec_ref(v_expectedType_4246_);
v_a_4511_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4408_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4408_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
else
{
lean_dec_ref(v_val_4404_);
lean_dec_ref(v_x_4254_);
lean_dec_ref(v_x_4253_);
lean_dec(v_val_4252_);
lean_dec_ref(v_expectedType_4246_);
return v___x_4405_;
}
}
else
{
lean_dec(v_a_4403_);
lean_dec_ref(v_x_4254_);
lean_dec_ref(v_x_4253_);
lean_dec(v_val_4252_);
v___y_4379_ = v___y_4256_;
v___y_4380_ = v___y_4257_;
v___y_4381_ = v___y_4258_;
v___y_4382_ = v___y_4259_;
goto v___jp_4378_;
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref(v_x_4254_);
lean_dec_ref(v_x_4253_);
lean_dec(v_val_4252_);
lean_dec_ref(v_expectedType_4246_);
lean_dec_ref(v_inst_4245_);
v_a_4519_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4402_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4402_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
v___jp_4378_:
{
lean_object* v_options_4383_; uint8_t v_hasTrace_4384_; 
v_options_4383_ = lean_ctor_get(v___y_4381_, 2);
v_hasTrace_4384_ = lean_ctor_get_uint8(v_options_4383_, sizeof(void*)*1);
if (v_hasTrace_4384_ == 0)
{
v___y_4301_ = v___y_4379_;
v___y_4302_ = v___y_4380_;
v___y_4303_ = v___y_4381_;
v_options_4304_ = v_options_4383_;
v___y_4305_ = v___y_4382_;
goto v___jp_4300_;
}
else
{
lean_object* v_inheritedTraceOptions_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v_inheritedTraceOptions_4385_ = lean_ctor_get(v___y_4381_, 13);
v___x_4386_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_4387_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4385_, v_options_4383_, v___x_4386_);
if (v___x_4387_ == 0)
{
v___y_4301_ = v___y_4379_;
v___y_4302_ = v___y_4380_;
v___y_4303_ = v___y_4381_;
v_options_4304_ = v_options_4383_;
v___y_4305_ = v___y_4382_;
goto v___jp_4300_;
}
else
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4388_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_4245_);
v___x_4389_ = l_Lean_MessageData_ofExpr(v_inst_4245_);
v___x_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4388_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4377_, v___x_4390_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_dec_ref(v___x_4391_);
v___y_4301_ = v___y_4379_;
v___y_4302_ = v___y_4380_;
v___y_4303_ = v___y_4381_;
v_options_4304_ = v_options_4383_;
v___y_4305_ = v___y_4382_;
goto v___jp_4300_;
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_dec_ref(v_expectedType_4246_);
lean_dec_ref(v_inst_4245_);
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
}
}
v___jp_4261_:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_enableRealizationsForConst(v___y_4262_, v___y_4264_, v___y_4265_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4273_ == 0)
{
lean_object* v_unused_4274_; 
v_unused_4274_ = lean_ctor_get(v___x_4266_, 0);
lean_dec(v_unused_4274_);
v___x_4268_ = v___x_4266_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_dec(v___x_4266_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 0, v___y_4263_);
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___y_4263_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec_ref(v___y_4263_);
v_a_4275_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4266_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4266_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
v___jp_4283_:
{
if (v_compile_4249_ == 0)
{
v___y_4262_ = v___y_4284_;
v___y_4263_ = v___y_4285_;
v___y_4264_ = v___y_4286_;
v___y_4265_ = v___y_4287_;
goto v___jp_4261_;
}
else
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4288_ = lean_unsigned_to_nat(1u);
v___x_4289_ = lean_mk_empty_array_with_capacity(v___x_4288_);
lean_inc(v___y_4284_);
v___x_4290_ = lean_array_push(v___x_4289_, v___y_4284_);
v___x_4291_ = l_Lean_compileDecls(v___x_4290_, v_logCompileErrors_4250_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_dec_ref(v___x_4291_);
v___y_4262_ = v___y_4284_;
v___y_4263_ = v___y_4285_;
v___y_4264_ = v___y_4286_;
v___y_4265_ = v___y_4287_;
goto v___jp_4261_;
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
v___jp_4300_:
{
lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4306_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4307_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4304_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; 
lean_dec_ref(v_expectedType_4246_);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v_inst_4245_);
return v___x_4308_;
}
else
{
lean_object* v___x_4309_; 
lean_inc(v___y_4305_);
lean_inc_ref(v___y_4303_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc_ref(v_inst_4245_);
v___x_4309_ = lean_infer_type(v_inst_4245_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4305_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref(v___x_4309_);
lean_inc_ref(v_expectedType_4246_);
v___x_4311_ = l_Lean_Meta_isExprDefEq(v_expectedType_4246_, v_a_4310_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4305_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4362_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4362_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4362_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
uint8_t v___x_4316_; 
v___x_4316_ = lean_unbox(v_a_4312_);
lean_dec(v_a_4312_);
if (v___x_4316_ == 0)
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v_a_4319_; lean_object* v___x_4320_; 
lean_del_object(v___x_4314_);
v___x_4317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_4318_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4317_, v___y_4305_);
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc_n(v_a_4319_, 2);
lean_dec_ref(v___x_4318_);
v___x_4320_ = l_Lean_Meta_mkAuxDefinition(v_a_4319_, v_expectedType_4246_, v_inst_4245_, v___x_4247_, v___x_4247_, v___x_4248_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4305_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref(v___x_4320_);
v___x_4322_ = 3;
lean_inc(v_a_4319_);
v___x_4323_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4319_, v___x_4322_, v___y_4302_, v___y_4305_);
lean_dec_ref(v___x_4323_);
if (v_isMeta_4251_ == 0)
{
v___y_4284_ = v_a_4319_;
v___y_4285_ = v_a_4321_;
v___y_4286_ = v___y_4303_;
v___y_4287_ = v___y_4305_;
goto v___jp_4283_;
}
else
{
lean_object* v___x_4324_; lean_object* v_env_4325_; lean_object* v_nextMacroScope_4326_; lean_object* v_ngen_4327_; lean_object* v_auxDeclNGen_4328_; lean_object* v_traceState_4329_; lean_object* v_messages_4330_; lean_object* v_infoState_4331_; lean_object* v_snapshotTasks_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4357_; 
v___x_4324_ = lean_st_ref_take(v___y_4305_);
v_env_4325_ = lean_ctor_get(v___x_4324_, 0);
v_nextMacroScope_4326_ = lean_ctor_get(v___x_4324_, 1);
v_ngen_4327_ = lean_ctor_get(v___x_4324_, 2);
v_auxDeclNGen_4328_ = lean_ctor_get(v___x_4324_, 3);
v_traceState_4329_ = lean_ctor_get(v___x_4324_, 4);
v_messages_4330_ = lean_ctor_get(v___x_4324_, 6);
v_infoState_4331_ = lean_ctor_get(v___x_4324_, 7);
v_snapshotTasks_4332_ = lean_ctor_get(v___x_4324_, 8);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4357_ == 0)
{
lean_object* v_unused_4358_; 
v_unused_4358_ = lean_ctor_get(v___x_4324_, 5);
lean_dec(v_unused_4358_);
v___x_4334_ = v___x_4324_;
v_isShared_4335_ = v_isSharedCheck_4357_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_snapshotTasks_4332_);
lean_inc(v_infoState_4331_);
lean_inc(v_messages_4330_);
lean_inc(v_traceState_4329_);
lean_inc(v_auxDeclNGen_4328_);
lean_inc(v_ngen_4327_);
lean_inc(v_nextMacroScope_4326_);
lean_inc(v_env_4325_);
lean_dec(v___x_4324_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4357_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4339_; 
lean_inc(v_a_4319_);
v___x_4336_ = l_Lean_markMeta(v_env_4325_, v_a_4319_);
v___x_4337_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 5, v___x_4337_);
lean_ctor_set(v___x_4334_, 0, v___x_4336_);
v___x_4339_ = v___x_4334_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_nextMacroScope_4326_);
lean_ctor_set(v_reuseFailAlloc_4356_, 2, v_ngen_4327_);
lean_ctor_set(v_reuseFailAlloc_4356_, 3, v_auxDeclNGen_4328_);
lean_ctor_set(v_reuseFailAlloc_4356_, 4, v_traceState_4329_);
lean_ctor_set(v_reuseFailAlloc_4356_, 5, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4356_, 6, v_messages_4330_);
lean_ctor_set(v_reuseFailAlloc_4356_, 7, v_infoState_4331_);
lean_ctor_set(v_reuseFailAlloc_4356_, 8, v_snapshotTasks_4332_);
v___x_4339_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v_mctx_4342_; lean_object* v_zetaDeltaFVarIds_4343_; lean_object* v_postponed_4344_; lean_object* v_diag_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4354_; 
v___x_4340_ = lean_st_ref_set(v___y_4305_, v___x_4339_);
v___x_4341_ = lean_st_ref_take(v___y_4302_);
v_mctx_4342_ = lean_ctor_get(v___x_4341_, 0);
v_zetaDeltaFVarIds_4343_ = lean_ctor_get(v___x_4341_, 2);
v_postponed_4344_ = lean_ctor_get(v___x_4341_, 3);
v_diag_4345_ = lean_ctor_get(v___x_4341_, 4);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4354_ == 0)
{
lean_object* v_unused_4355_; 
v_unused_4355_ = lean_ctor_get(v___x_4341_, 1);
lean_dec(v_unused_4355_);
v___x_4347_ = v___x_4341_;
v_isShared_4348_ = v_isSharedCheck_4354_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_diag_4345_);
lean_inc(v_postponed_4344_);
lean_inc(v_zetaDeltaFVarIds_4343_);
lean_inc(v_mctx_4342_);
lean_dec(v___x_4341_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4354_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4349_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 1, v___x_4349_);
v___x_4351_ = v___x_4347_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_mctx_4342_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_zetaDeltaFVarIds_4343_);
lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_postponed_4344_);
lean_ctor_set(v_reuseFailAlloc_4353_, 4, v_diag_4345_);
v___x_4351_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_st_ref_set(v___y_4302_, v___x_4351_);
v___y_4284_ = v_a_4319_;
v___y_4285_ = v_a_4321_;
v___y_4286_ = v___y_4303_;
v___y_4287_ = v___y_4305_;
goto v___jp_4283_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4319_);
return v___x_4320_;
}
}
else
{
lean_object* v___x_4360_; 
lean_dec_ref(v_expectedType_4246_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v_inst_4245_);
v___x_4360_ = v___x_4314_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_inst_4245_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec_ref(v_expectedType_4246_);
lean_dec_ref(v_inst_4245_);
v_a_4363_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4311_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4311_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4246_);
lean_dec_ref(v_inst_4245_);
return v___x_4309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object* v_expectedType_4527_, lean_object* v_inst_4528_, uint8_t v___x_4529_, uint8_t v_hasTrace_4530_, uint8_t v_compile_4531_, uint8_t v_logCompileErrors_4532_, uint8_t v_isMeta_4533_, lean_object* v_val_4534_, lean_object* v_____r_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v___x_4541_; 
lean_inc_ref(v_expectedType_4527_);
v___x_4541_ = l_Lean_Meta_isProp(v_expectedType_4527_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4563_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4544_ = v___x_4541_;
v_isShared_4545_ = v_isSharedCheck_4563_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4541_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4563_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
uint8_t v___x_4546_; 
v___x_4546_ = lean_unbox(v_a_4542_);
lean_dec(v_a_4542_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; 
lean_del_object(v___x_4544_);
lean_inc(v___y_4539_);
lean_inc_ref(v___y_4538_);
lean_inc(v___y_4537_);
lean_inc_ref(v___y_4536_);
lean_inc_ref(v_inst_4528_);
v___x_4547_ = lean_whnf(v_inst_4528_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v_dummy_4549_; lean_object* v_nargs_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_a_4548_);
lean_dec_ref(v___x_4547_);
v_dummy_4549_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_4550_ = l_Lean_Expr_getAppNumArgs(v_a_4548_);
lean_inc(v_nargs_4550_);
v___x_4551_ = lean_mk_array(v_nargs_4550_, v_dummy_4549_);
v___x_4552_ = lean_unsigned_to_nat(1u);
v___x_4553_ = lean_nat_sub(v_nargs_4550_, v___x_4552_);
lean_dec(v_nargs_4550_);
v___x_4554_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_4528_, v_expectedType_4527_, v___x_4529_, v_hasTrace_4530_, v_compile_4531_, v_logCompileErrors_4532_, v_isMeta_4533_, v_val_4534_, v_a_4548_, v___x_4551_, v___x_4553_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
lean_dec(v___x_4553_);
return v___x_4554_;
}
else
{
lean_dec(v_val_4534_);
lean_dec_ref(v_inst_4528_);
lean_dec_ref(v_expectedType_4527_);
return v___x_4547_;
}
}
else
{
lean_object* v_options_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; 
lean_dec(v_val_4534_);
v_options_4555_ = lean_ctor_get(v___y_4538_, 2);
v___x_4556_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4557_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4555_, v___x_4556_);
if (v___x_4557_ == 0)
{
lean_object* v___x_4559_; 
lean_dec_ref(v_expectedType_4527_);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v_inst_4528_);
v___x_4559_ = v___x_4544_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_inst_4528_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
lean_del_object(v___x_4544_);
v___x_4561_ = lean_box(0);
v___x_4562_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_4527_, v_inst_4528_, v_hasTrace_4530_, v___x_4561_, v_hasTrace_4530_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
return v___x_4562_;
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec(v_val_4534_);
lean_dec_ref(v_inst_4528_);
lean_dec_ref(v_expectedType_4527_);
v_a_4564_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4541_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4541_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___closed__3(void){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = ((lean_object*)(l_Lean_Meta_wrapInstance___closed__2));
v___x_4574_ = l_Lean_stringToMessageData(v___x_4573_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(lean_object* v_upperBound_4575_, lean_object* v_fst_4576_, lean_object* v_args_4577_, uint8_t v___x_4578_, uint8_t v_compile_4579_, uint8_t v_logCompileErrors_4580_, uint8_t v_isMeta_4581_, lean_object* v_val_4582_, lean_object* v_expectedType_4583_, lean_object* v_a_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_a_4592_; lean_object* v___y_4597_; uint8_t v___x_4616_; 
v___x_4616_ = lean_nat_dec_lt(v_a_4584_, v_upperBound_4575_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_b_4585_);
return v___x_4617_;
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4618_ = lean_array_fget_borrowed(v_fst_4576_, v_a_4584_);
v___x_4619_ = l_Lean_Expr_mvarId_x21(v___x_4618_);
lean_inc(v___x_4619_);
v___x_4620_ = l_Lean_MVarId_getDecl(v___x_4619_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v_userName_4622_; lean_object* v_type_4623_; lean_object* v___x_4624_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref(v___x_4620_);
v_userName_4622_ = lean_ctor_get(v_a_4621_, 0);
lean_inc(v_userName_4622_);
v_type_4623_ = lean_ctor_get(v_a_4621_, 2);
lean_inc_ref(v_type_4623_);
lean_dec(v_a_4621_);
v___x_4624_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_4623_, v___y_4587_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc_n(v_a_4625_, 2);
lean_dec_ref(v___x_4624_);
v___x_4626_ = l_Lean_Meta_isProp(v_a_4625_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4628_; lean_object* v_cls_4629_; lean_object* v___f_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref(v___x_4626_);
v___x_4628_ = lean_box(0);
v_cls_4629_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_4630_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_4631_ = lean_array_fget_borrowed(v_args_4577_, v_a_4584_);
v___x_4632_ = lean_unbox(v_a_4627_);
lean_dec(v_a_4627_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
lean_inc(v_a_4625_);
v___x_4633_ = l_Lean_Meta_isClass_x3f(v_a_4625_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4732_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4732_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4732_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___f_4642_; 
v___x_4638_ = lean_box(v___x_4578_);
v___x_4639_ = lean_box(v_compile_4579_);
v___x_4640_ = lean_box(v_logCompileErrors_4580_);
v___x_4641_ = lean_box(v_isMeta_4581_);
lean_inc(v_a_4625_);
lean_inc(v___x_4631_);
lean_inc(v___x_4619_);
v___f_4642_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1___boxed), 14, 8);
lean_closure_set(v___f_4642_, 0, v___x_4619_);
lean_closure_set(v___f_4642_, 1, v___x_4631_);
lean_closure_set(v___f_4642_, 2, v___x_4628_);
lean_closure_set(v___f_4642_, 3, v_a_4625_);
lean_closure_set(v___f_4642_, 4, v___x_4638_);
lean_closure_set(v___f_4642_, 5, v___x_4639_);
lean_closure_set(v___f_4642_, 6, v___x_4640_);
lean_closure_set(v___f_4642_, 7, v___x_4641_);
if (lean_obj_tag(v_a_4634_) == 0)
{
lean_del_object(v___x_4636_);
goto v___jp_4645_;
}
else
{
lean_dec_ref(v_a_4634_);
if (v___x_4578_ == 0)
{
lean_del_object(v___x_4636_);
goto v___jp_4645_;
}
else
{
lean_object* v_options_4693_; lean_object* v_a_4695_; lean_object* v___y_4698_; uint8_t v___y_4699_; lean_object* v_a_4704_; lean_object* v___y_4708_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
lean_dec_ref(v___f_4642_);
lean_dec(v_userName_4622_);
v_options_4693_ = lean_ctor_get(v___y_4588_, 2);
v___x_4712_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4713_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4693_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; 
lean_del_object(v___x_4636_);
lean_inc(v___x_4631_);
v___x_4714_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_4631_, v_a_4625_, v_compile_4579_, v_logCompileErrors_4580_, v_isMeta_4581_, v___x_4619_, v___x_4628_, v___x_4628_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4714_;
goto v___jp_4596_;
}
else
{
lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4715_ = lean_box(0);
lean_inc(v_a_4625_);
v___x_4716_ = l_Lean_Meta_trySynthInstance(v_a_4625_, v___x_4715_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref(v___x_4716_);
if (lean_obj_tag(v_a_4717_) == 1)
{
lean_object* v_a_4718_; lean_object* v___x_4719_; 
v_a_4718_ = lean_ctor_get(v_a_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref(v_a_4717_);
v___x_4719_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_4629_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; uint8_t v___x_4721_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref(v___x_4719_);
v___x_4721_ = lean_unbox(v_a_4720_);
lean_dec(v_a_4720_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4722_; 
lean_inc(v___x_4619_);
v___x_4722_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_4619_, v_a_4718_, v___x_4628_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4708_ = v___x_4722_;
goto v___jp_4707_;
}
else
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4723_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_4718_);
v___x_4724_ = l_Lean_MessageData_ofExpr(v_a_4718_);
v___x_4725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4723_);
lean_ctor_set(v___x_4725_, 1, v___x_4724_);
v___x_4726_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4629_, v___x_4725_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4728_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref(v___x_4726_);
lean_inc(v___x_4619_);
v___x_4728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_4619_, v_a_4718_, v_a_4727_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4708_ = v___x_4728_;
goto v___jp_4707_;
}
else
{
lean_object* v_a_4729_; 
lean_dec(v_a_4718_);
v_a_4729_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4729_);
lean_dec_ref(v___x_4726_);
v_a_4704_ = v_a_4729_;
goto v___jp_4703_;
}
}
}
else
{
lean_object* v_a_4730_; 
lean_dec(v_a_4718_);
v_a_4730_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4730_);
lean_dec_ref(v___x_4719_);
v_a_4704_ = v_a_4730_;
goto v___jp_4703_;
}
}
else
{
lean_dec(v_a_4717_);
lean_del_object(v___x_4636_);
v_a_4695_ = v___x_4628_;
goto v___jp_4694_;
}
}
else
{
lean_object* v_a_4731_; 
v_a_4731_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4731_);
lean_dec_ref(v___x_4716_);
v_a_4704_ = v_a_4731_;
goto v___jp_4703_;
}
}
v___jp_4694_:
{
lean_object* v___x_4696_; 
lean_inc(v___x_4631_);
v___x_4696_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_4631_, v_a_4625_, v_compile_4579_, v_logCompileErrors_4580_, v_isMeta_4581_, v___x_4619_, v___x_4628_, v_a_4695_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4696_;
goto v___jp_4596_;
}
v___jp_4697_:
{
if (v___y_4699_ == 0)
{
lean_dec_ref(v___y_4698_);
lean_del_object(v___x_4636_);
v_a_4695_ = v___x_4628_;
goto v___jp_4694_;
}
else
{
lean_object* v___x_4701_; 
lean_dec(v_a_4625_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set_tag(v___x_4636_, 1);
lean_ctor_set(v___x_4636_, 0, v___y_4698_);
v___x_4701_ = v___x_4636_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___y_4698_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
v___jp_4703_:
{
uint8_t v___x_4705_; 
v___x_4705_ = l_Lean_Exception_isInterrupt(v_a_4704_);
if (v___x_4705_ == 0)
{
uint8_t v___x_4706_; 
lean_inc_ref(v_a_4704_);
v___x_4706_ = l_Lean_Exception_isRuntime(v_a_4704_);
v___y_4698_ = v_a_4704_;
v___y_4699_ = v___x_4706_;
goto v___jp_4697_;
}
else
{
v___y_4698_ = v_a_4704_;
v___y_4699_ = v___x_4705_;
goto v___jp_4697_;
}
}
v___jp_4707_:
{
if (lean_obj_tag(v___y_4708_) == 0)
{
lean_object* v_a_4709_; 
lean_del_object(v___x_4636_);
v_a_4709_ = lean_ctor_get(v___y_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref(v___y_4708_);
if (lean_obj_tag(v_a_4709_) == 0)
{
lean_dec(v_a_4625_);
lean_dec(v___x_4619_);
v_a_4592_ = v___x_4628_;
goto v___jp_4591_;
}
else
{
lean_object* v_a_4710_; 
v_a_4710_ = lean_ctor_get(v_a_4709_, 0);
lean_inc(v_a_4710_);
lean_dec_ref(v_a_4709_);
v_a_4695_ = v_a_4710_;
goto v___jp_4694_;
}
}
else
{
lean_object* v_a_4711_; 
v_a_4711_ = lean_ctor_get(v___y_4708_, 0);
lean_inc(v_a_4711_);
lean_dec_ref(v___y_4708_);
v_a_4704_ = v_a_4711_;
goto v___jp_4703_;
}
}
}
}
v___jp_4643_:
{
lean_object* v___x_4644_; 
lean_inc(v___x_4631_);
v___x_4644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(v___x_4619_, v___x_4631_, v___x_4628_, v_a_4625_, v___x_4578_, v_compile_4579_, v_logCompileErrors_4580_, v_isMeta_4581_, v___x_4628_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4644_;
goto v___jp_4596_;
}
v___jp_4645_:
{
lean_object* v_options_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; 
v_options_4646_ = lean_ctor_get(v___y_4588_, 2);
v___x_4647_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4648_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4646_, v___x_4647_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; 
lean_dec_ref(v___f_4642_);
lean_dec(v_userName_4622_);
lean_inc(v___x_4631_);
v___x_4649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(v___x_4619_, v___x_4631_, v___x_4628_, v_a_4625_, v___x_4578_, v_compile_4579_, v_logCompileErrors_4580_, v_isMeta_4581_, v___x_4628_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4649_;
goto v___jp_4596_;
}
else
{
lean_object* v___x_4650_; 
lean_inc(v_userName_4622_);
lean_inc(v_val_4582_);
v___x_4650_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_4582_, v_userName_4622_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v_fst_4652_; lean_object* v_snd_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4684_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref(v___x_4650_);
v_fst_4652_ = lean_ctor_get(v_a_4651_, 0);
v_snd_4653_ = lean_ctor_get(v_a_4651_, 1);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_a_4651_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4655_ = v_a_4651_;
v_isShared_4656_ = v_isSharedCheck_4684_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_snd_4653_);
lean_inc(v_fst_4652_);
lean_dec(v_a_4651_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4684_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
uint8_t v___x_4657_; 
v___x_4657_ = lean_name_eq(v_fst_4652_, v_val_4582_);
if (v___x_4657_ == 0)
{
if (v___x_4578_ == 0)
{
lean_del_object(v___x_4655_);
lean_dec(v_snd_4653_);
lean_dec(v_fst_4652_);
lean_dec_ref(v___f_4642_);
lean_dec(v_userName_4622_);
goto v___jp_4643_;
}
else
{
lean_object* v___x_4658_; 
lean_dec(v_a_4625_);
v___x_4658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_4629_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; uint8_t v___x_4660_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4659_);
lean_dec_ref(v___x_4658_);
v___x_4660_ = lean_unbox(v_a_4659_);
lean_dec(v_a_4659_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; 
lean_del_object(v___x_4655_);
lean_dec(v_userName_4622_);
lean_inc_ref(v_expectedType_4583_);
lean_inc(v_val_4582_);
v___x_4661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_4582_, v_fst_4652_, v_expectedType_4583_, v___f_4630_, v___f_4642_, v___x_4628_, v_cls_4629_, v_snd_4653_, v___x_4619_, v___x_4628_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4661_;
goto v___jp_4596_;
}
else
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
v___x_4662_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_4663_ = l_Lean_MessageData_ofName(v_userName_4622_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set_tag(v___x_4655_, 7);
lean_ctor_set(v___x_4655_, 1, v___x_4663_);
lean_ctor_set(v___x_4655_, 0, v___x_4662_);
v___x_4665_ = v___x_4655_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4662_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4666_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_4667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4665_);
lean_ctor_set(v___x_4667_, 1, v___x_4666_);
lean_inc(v_fst_4652_);
v___x_4668_ = l_Lean_MessageData_ofName(v_fst_4652_);
v___x_4669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4667_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
v___x_4670_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4669_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
v___x_4672_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4629_, v___x_4671_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4674_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref(v___x_4672_);
lean_inc_ref(v_expectedType_4583_);
lean_inc(v_val_4582_);
v___x_4674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_4582_, v_fst_4652_, v_expectedType_4583_, v___f_4630_, v___f_4642_, v___x_4628_, v_cls_4629_, v_snd_4653_, v___x_4619_, v_a_4673_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4674_;
goto v___jp_4596_;
}
else
{
lean_dec(v_snd_4653_);
lean_dec(v_fst_4652_);
lean_dec_ref(v___f_4642_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
return v___x_4672_;
}
}
}
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4683_; 
lean_del_object(v___x_4655_);
lean_dec(v_snd_4653_);
lean_dec(v_fst_4652_);
lean_dec_ref(v___f_4642_);
lean_dec(v_userName_4622_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4676_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4678_ = v___x_4658_;
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4658_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4676_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
}
else
{
lean_del_object(v___x_4655_);
lean_dec(v_snd_4653_);
lean_dec(v_fst_4652_);
lean_dec_ref(v___f_4642_);
lean_dec(v_userName_4622_);
goto v___jp_4643_;
}
}
}
else
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4692_; 
lean_dec_ref(v___f_4642_);
lean_dec(v_a_4625_);
lean_dec(v_userName_4622_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4685_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4687_ = v___x_4650_;
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4650_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec(v_a_4625_);
lean_dec(v_userName_4622_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4733_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4633_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4633_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
else
{
lean_object* v___x_4741_; 
lean_dec(v_userName_4622_);
lean_inc(v___y_4589_);
lean_inc_ref(v___y_4588_);
lean_inc(v___y_4587_);
lean_inc_ref(v___y_4586_);
lean_inc(v___x_4631_);
v___x_4741_ = lean_infer_type(v___x_4631_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v___x_4743_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc_n(v_a_4742_, 2);
lean_dec_ref(v___x_4741_);
lean_inc(v_a_4625_);
v___x_4743_ = l_Lean_Meta_isExprDefEq(v_a_4625_, v_a_4742_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___f_4745_; uint8_t v___x_4746_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref(v___x_4743_);
v___f_4745_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_4746_ = lean_unbox(v_a_4744_);
lean_dec(v_a_4744_);
if (v___x_4746_ == 0)
{
lean_object* v___x_4747_; 
v___x_4747_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_4629_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; uint8_t v___x_4749_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v___x_4747_);
v___x_4749_ = lean_unbox(v_a_4748_);
lean_dec(v_a_4748_);
if (v___x_4749_ == 0)
{
lean_object* v___x_4750_; 
lean_dec(v_a_4742_);
lean_inc(v___x_4631_);
v___x_4750_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_4625_, v___x_4631_, v___x_4578_, v___x_4619_, v___f_4745_, v___x_4628_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4750_;
goto v___jp_4596_;
}
else
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_4584_);
v___x_4752_ = l_Nat_reprFast(v_a_4584_);
v___x_4753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4752_);
v___x_4754_ = l_Lean_MessageData_ofFormat(v___x_4753_);
v___x_4755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4751_);
lean_ctor_set(v___x_4755_, 1, v___x_4754_);
v___x_4756_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_4757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
lean_inc(v_a_4625_);
v___x_4758_ = l_Lean_MessageData_ofExpr(v_a_4625_);
v___x_4759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4757_);
lean_ctor_set(v___x_4759_, 1, v___x_4758_);
v___x_4760_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_4761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4759_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = l_Lean_MessageData_ofExpr(v_a_4742_);
v___x_4763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4761_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
v___x_4764_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4763_);
lean_ctor_set(v___x_4765_, 1, v___x_4764_);
lean_inc(v___x_4631_);
v___x_4766_ = l_Lean_MessageData_ofExpr(v___x_4631_);
v___x_4767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4765_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4629_, v___x_4767_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4770_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref(v___x_4768_);
lean_inc(v___x_4631_);
v___x_4770_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_4625_, v___x_4631_, v___x_4578_, v___x_4619_, v___f_4745_, v_a_4769_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4770_;
goto v___jp_4596_;
}
else
{
lean_dec(v_a_4625_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
return v___x_4768_;
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec(v_a_4742_);
lean_dec(v_a_4625_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4771_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4747_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4747_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
else
{
lean_object* v___x_4779_; 
lean_dec(v_a_4742_);
lean_dec(v_a_4625_);
lean_inc(v___x_4631_);
v___x_4779_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_4619_, v___x_4631_, v___y_4587_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4781_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref(v___x_4779_);
v___x_4781_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_4628_, v_a_4780_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
v___y_4597_ = v___x_4781_;
goto v___jp_4596_;
}
else
{
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
return v___x_4779_;
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_a_4742_);
lean_dec(v_a_4625_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4782_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4743_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4743_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v_a_4625_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4790_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4741_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4741_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec(v_a_4625_);
lean_dec(v_userName_4622_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4798_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4626_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4626_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
lean_dec(v_userName_4622_);
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4806_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4624_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4624_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
lean_dec(v___x_4619_);
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4814_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4620_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4620_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
v___jp_4591_:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4593_ = lean_unsigned_to_nat(1u);
v___x_4594_ = lean_nat_add(v_a_4584_, v___x_4593_);
lean_dec(v_a_4584_);
v_a_4584_ = v___x_4594_;
v_b_4585_ = v_a_4592_;
goto _start;
}
v___jp_4596_:
{
if (lean_obj_tag(v___y_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4607_; 
v_a_4598_ = lean_ctor_get(v___y_4597_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___y_4597_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4600_ = v___y_4597_;
v_isShared_4601_ = v_isSharedCheck_4607_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___y_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4607_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
if (lean_obj_tag(v_a_4598_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4604_; 
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4602_ = lean_ctor_get(v_a_4598_, 0);
lean_inc(v_a_4602_);
lean_dec_ref(v_a_4598_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v_a_4602_);
v___x_4604_ = v___x_4600_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
else
{
lean_object* v_a_4606_; 
lean_del_object(v___x_4600_);
v_a_4606_ = lean_ctor_get(v_a_4598_, 0);
lean_inc(v_a_4606_);
lean_dec_ref(v_a_4598_);
v_a_4592_ = v_a_4606_;
goto v___jp_4591_;
}
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec(v_a_4584_);
lean_dec_ref(v_expectedType_4583_);
lean_dec(v_val_4582_);
v_a_4608_ = lean_ctor_get(v___y_4597_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___y_4597_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___y_4597_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___y_4597_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(lean_object* v_inst_4822_, lean_object* v_expectedType_4823_, uint8_t v___x_4824_, uint8_t v_compile_4825_, uint8_t v_logCompileErrors_4826_, uint8_t v_isMeta_4827_, lean_object* v_val_4828_, lean_object* v_x_4829_, lean_object* v_x_4830_, lean_object* v_x_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___y_4840_; lean_object* v___y_4841_; lean_object* v___y_4860_; lean_object* v___y_4861_; lean_object* v___y_4862_; lean_object* v___y_4863_; lean_object* v___y_4877_; lean_object* v___y_4878_; lean_object* v___y_4879_; lean_object* v_options_4880_; lean_object* v___y_4881_; 
if (lean_obj_tag(v_x_4829_) == 5)
{
lean_object* v_fn_4949_; lean_object* v_arg_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v_fn_4949_ = lean_ctor_get(v_x_4829_, 0);
lean_inc_ref(v_fn_4949_);
v_arg_4950_ = lean_ctor_get(v_x_4829_, 1);
lean_inc_ref(v_arg_4950_);
lean_dec_ref(v_x_4829_);
v___x_4951_ = lean_array_set(v_x_4830_, v_x_4831_, v_arg_4950_);
v___x_4952_ = lean_unsigned_to_nat(1u);
v___x_4953_ = lean_nat_sub(v_x_4831_, v___x_4952_);
lean_dec(v_x_4831_);
v_x_4829_ = v_fn_4949_;
v_x_4830_ = v___x_4951_;
v_x_4831_ = v___x_4953_;
goto _start;
}
else
{
lean_object* v_cls_4955_; lean_object* v___y_4957_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v___y_4960_; lean_object* v___x_4978_; 
lean_dec(v_x_4831_);
v_cls_4955_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4978_ = l_Lean_Expr_constName_x3f(v_x_4829_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4829_);
lean_dec(v_val_4828_);
v___y_4957_ = v___y_4832_;
v___y_4958_ = v___y_4833_;
v___y_4959_ = v___y_4834_;
v___y_4960_ = v___y_4835_;
goto v___jp_4956_;
}
else
{
lean_object* v_val_4979_; lean_object* v___x_4980_; 
v_val_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_val_4979_);
lean_dec_ref(v___x_4978_);
v___x_4980_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4979_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4981_);
lean_dec_ref(v___x_4980_);
if (lean_obj_tag(v_a_4981_) == 6)
{
lean_object* v_val_4982_; lean_object* v___x_4983_; 
lean_dec_ref(v_inst_4822_);
v_val_4982_ = lean_ctor_get(v_a_4981_, 0);
lean_inc_ref(v_val_4982_);
lean_dec_ref(v_a_4981_);
lean_inc(v___y_4835_);
lean_inc_ref(v___y_4834_);
lean_inc(v___y_4833_);
lean_inc_ref(v___y_4832_);
lean_inc_ref(v_x_4829_);
v___x_4983_ = lean_infer_type(v_x_4829_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; uint8_t v___x_4985_; lean_object* v___x_4986_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref(v___x_4983_);
v___x_4985_ = 0;
v___x_4986_ = l_Lean_Meta_forallMetaTelescope(v_a_4984_, v___x_4985_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v_snd_4988_; lean_object* v_fst_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_5089_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref(v___x_4986_);
v_snd_4988_ = lean_ctor_get(v_a_4987_, 1);
v_fst_4989_ = lean_ctor_get(v_a_4987_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v_a_4987_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_4991_ = v_a_4987_;
v_isShared_4992_ = v_isSharedCheck_5089_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_snd_4988_);
lean_inc(v_fst_4989_);
lean_dec(v_a_4987_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_5089_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v_snd_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5087_; 
v_snd_4993_ = lean_ctor_get(v_snd_4988_, 1);
v_isSharedCheck_5087_ = !lean_is_exclusive(v_snd_4988_);
if (v_isSharedCheck_5087_ == 0)
{
lean_object* v_unused_5088_; 
v_unused_5088_ = lean_ctor_get(v_snd_4988_, 0);
lean_dec(v_unused_5088_);
v___x_4995_ = v_snd_4988_;
v_isShared_4996_ = v_isSharedCheck_5087_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_snd_4993_);
lean_dec(v_snd_4988_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5087_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4997_; lean_object* v___y_4999_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___x_5034_; uint8_t v___x_5035_; 
v___x_4997_ = lean_array_get_size(v_x_4830_);
v___x_5034_ = lean_array_get_size(v_fst_4989_);
v___x_5035_ = lean_nat_dec_eq(v___x_4997_, v___x_5034_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5039_; 
lean_dec(v_snd_4993_);
lean_dec(v_fst_4989_);
lean_dec_ref(v_val_4982_);
lean_dec(v_val_4828_);
lean_dec_ref(v_expectedType_4823_);
v___x_5036_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_5037_ = l_Lean_MessageData_ofExpr(v_x_4829_);
if (v_isShared_4996_ == 0)
{
lean_ctor_set_tag(v___x_4995_, 7);
lean_ctor_set(v___x_4995_, 1, v___x_5037_);
lean_ctor_set(v___x_4995_, 0, v___x_5036_);
v___x_5039_ = v___x_4995_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5036_);
lean_ctor_set(v_reuseFailAlloc_5050_, 1, v___x_5037_);
v___x_5039_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
lean_object* v___x_5040_; lean_object* v___x_5042_; 
v___x_5040_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3);
if (v_isShared_4992_ == 0)
{
lean_ctor_set_tag(v___x_4991_, 7);
lean_ctor_set(v___x_4991_, 1, v___x_5040_);
lean_ctor_set(v___x_4991_, 0, v___x_5039_);
v___x_5042_ = v___x_4991_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5039_);
lean_ctor_set(v_reuseFailAlloc_5049_, 1, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5043_ = lean_array_to_list(v_x_4830_);
v___x_5044_ = lean_box(0);
v___x_5045_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_5043_, v___x_5044_);
v___x_5046_ = l_Lean_MessageData_ofList(v___x_5045_);
v___x_5047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5042_);
lean_ctor_set(v___x_5047_, 1, v___x_5046_);
v___x_5048_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5047_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
return v___x_5048_;
}
}
}
else
{
lean_object* v___x_5051_; 
lean_inc_ref(v_expectedType_4823_);
v___x_5051_ = l_Lean_Meta_isExprDefEq(v_expectedType_4823_, v_snd_4993_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; uint8_t v___x_5053_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_a_5052_);
lean_dec_ref(v___x_5051_);
v___x_5053_ = lean_unbox(v_a_5052_);
if (v___x_5053_ == 0)
{
lean_object* v_toConstantVal_5054_; lean_object* v_name_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5059_; 
lean_dec(v_fst_4989_);
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4829_);
lean_dec(v_val_4828_);
v_toConstantVal_5054_ = lean_ctor_get(v_val_4982_, 0);
lean_inc_ref(v_toConstantVal_5054_);
lean_dec_ref(v_val_4982_);
v_name_5055_ = lean_ctor_get(v_toConstantVal_5054_, 0);
lean_inc(v_name_5055_);
lean_dec_ref(v_toConstantVal_5054_);
v___x_5056_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_5057_ = l_Lean_MessageData_ofExpr(v_expectedType_4823_);
if (v_isShared_4996_ == 0)
{
lean_ctor_set_tag(v___x_4995_, 7);
lean_ctor_set(v___x_4995_, 1, v___x_5057_);
lean_ctor_set(v___x_4995_, 0, v___x_5056_);
v___x_5059_ = v___x_4995_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v___x_5056_);
lean_ctor_set(v_reuseFailAlloc_5078_, 1, v___x_5057_);
v___x_5059_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5060_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_4992_ == 0)
{
lean_ctor_set_tag(v___x_4991_, 7);
lean_ctor_set(v___x_4991_, 1, v___x_5060_);
lean_ctor_set(v___x_4991_, 0, v___x_5059_);
v___x_5062_ = v___x_4991_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5059_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
uint8_t v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
v___x_5063_ = lean_unbox(v_a_5052_);
lean_dec(v_a_5052_);
v___x_5064_ = l_Lean_MessageData_ofConstName(v_name_5055_, v___x_5063_);
v___x_5065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5062_);
lean_ctor_set(v___x_5065_, 1, v___x_5064_);
v___x_5066_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_5067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5065_);
lean_ctor_set(v___x_5067_, 1, v___x_5066_);
v___x_5068_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5067_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5068_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5068_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
}
else
{
lean_dec(v_a_5052_);
lean_del_object(v___x_4995_);
lean_del_object(v___x_4991_);
v___y_4999_ = v___y_4832_;
v___y_5000_ = v___y_4833_;
v___y_5001_ = v___y_4834_;
v___y_5002_ = v___y_4835_;
goto v___jp_4998_;
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_del_object(v___x_4995_);
lean_del_object(v___x_4991_);
lean_dec(v_fst_4989_);
lean_dec_ref(v_val_4982_);
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4829_);
lean_dec(v_val_4828_);
lean_dec_ref(v_expectedType_4823_);
v_a_5079_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5051_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5051_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
v___jp_4998_:
{
lean_object* v_numParams_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v_numParams_5003_ = lean_ctor_get(v_val_4982_, 3);
lean_inc(v_numParams_5003_);
lean_dec_ref(v_val_4982_);
v___x_5004_ = lean_box(0);
v___x_5005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v___x_4997_, v_fst_4989_, v_x_4830_, v___x_4824_, v_compile_4825_, v_logCompileErrors_4826_, v_isMeta_4827_, v_val_4828_, v_expectedType_4823_, v_numParams_5003_, v___x_5004_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec_ref(v_x_4830_);
if (lean_obj_tag(v___x_5005_) == 0)
{
size_t v_sz_5006_; size_t v___x_5007_; lean_object* v___x_5008_; 
lean_dec_ref(v___x_5005_);
v_sz_5006_ = lean_array_size(v_fst_4989_);
v___x_5007_ = ((size_t)0ULL);
v___x_5008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_5006_, v___x_5007_, v_fst_4989_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5017_; 
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5011_ = v___x_5008_;
v_isShared_5012_ = v_isSharedCheck_5017_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_5008_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5017_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5013_; lean_object* v___x_5015_; 
v___x_5013_ = l_Lean_mkAppN(v_x_4829_, v_a_5009_);
lean_dec(v_a_5009_);
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 0, v___x_5013_);
v___x_5015_ = v___x_5011_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec_ref(v_x_4829_);
v_a_5018_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5008_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5008_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
lean_dec(v_fst_4989_);
lean_dec_ref(v_x_4829_);
v_a_5026_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_5005_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5005_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
lean_dec_ref(v_val_4982_);
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4829_);
lean_dec(v_val_4828_);
lean_dec_ref(v_expectedType_4823_);
v_a_5090_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_4986_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_4986_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
else
{
lean_dec_ref(v_val_4982_);
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4829_);
lean_dec(v_val_4828_);
lean_dec_ref(v_expectedType_4823_);
return v___x_4983_;
}
}
else
{
lean_dec(v_a_4981_);
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4829_);
lean_dec(v_val_4828_);
v___y_4957_ = v___y_4832_;
v___y_4958_ = v___y_4833_;
v___y_4959_ = v___y_4834_;
v___y_4960_ = v___y_4835_;
goto v___jp_4956_;
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4829_);
lean_dec(v_val_4828_);
lean_dec_ref(v_expectedType_4823_);
lean_dec_ref(v_inst_4822_);
v_a_5098_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_4980_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_4980_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v___x_5103_; 
if (v_isShared_5101_ == 0)
{
v___x_5103_ = v___x_5100_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
v___jp_4956_:
{
lean_object* v_options_4961_; uint8_t v_hasTrace_4962_; 
v_options_4961_ = lean_ctor_get(v___y_4959_, 2);
v_hasTrace_4962_ = lean_ctor_get_uint8(v_options_4961_, sizeof(void*)*1);
if (v_hasTrace_4962_ == 0)
{
v___y_4877_ = v___y_4957_;
v___y_4878_ = v___y_4958_;
v___y_4879_ = v___y_4959_;
v_options_4880_ = v_options_4961_;
v___y_4881_ = v___y_4960_;
goto v___jp_4876_;
}
else
{
lean_object* v_inheritedTraceOptions_4963_; lean_object* v___x_4964_; uint8_t v___x_4965_; 
v_inheritedTraceOptions_4963_ = lean_ctor_get(v___y_4959_, 13);
v___x_4964_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_4965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4963_, v_options_4961_, v___x_4964_);
if (v___x_4965_ == 0)
{
v___y_4877_ = v___y_4957_;
v___y_4878_ = v___y_4958_;
v___y_4879_ = v___y_4959_;
v_options_4880_ = v_options_4961_;
v___y_4881_ = v___y_4960_;
goto v___jp_4876_;
}
else
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4966_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_4822_);
v___x_4967_ = l_Lean_MessageData_ofExpr(v_inst_4822_);
v___x_4968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4966_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
v___x_4969_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4955_, v___x_4968_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_dec_ref(v___x_4969_);
v___y_4877_ = v___y_4957_;
v___y_4878_ = v___y_4958_;
v___y_4879_ = v___y_4959_;
v_options_4880_ = v_options_4961_;
v___y_4881_ = v___y_4960_;
goto v___jp_4876_;
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_dec_ref(v_expectedType_4823_);
lean_dec_ref(v_inst_4822_);
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4969_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
}
}
}
v___jp_4837_:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_enableRealizationsForConst(v___y_4838_, v___y_4840_, v___y_4841_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4849_ == 0)
{
lean_object* v_unused_4850_; 
v_unused_4850_ = lean_ctor_get(v___x_4842_, 0);
lean_dec(v_unused_4850_);
v___x_4844_ = v___x_4842_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_dec(v___x_4842_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 0, v___y_4839_);
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___y_4839_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
else
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4858_; 
lean_dec_ref(v___y_4839_);
v_a_4851_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4853_ = v___x_4842_;
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4842_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4854_ == 0)
{
v___x_4856_ = v___x_4853_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4851_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
v___jp_4859_:
{
if (v_compile_4825_ == 0)
{
v___y_4838_ = v___y_4860_;
v___y_4839_ = v___y_4861_;
v___y_4840_ = v___y_4862_;
v___y_4841_ = v___y_4863_;
goto v___jp_4837_;
}
else
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4864_ = lean_unsigned_to_nat(1u);
v___x_4865_ = lean_mk_empty_array_with_capacity(v___x_4864_);
lean_inc(v___y_4860_);
v___x_4866_ = lean_array_push(v___x_4865_, v___y_4860_);
v___x_4867_ = l_Lean_compileDecls(v___x_4866_, v_logCompileErrors_4826_, v___y_4862_, v___y_4863_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_dec_ref(v___x_4867_);
v___y_4838_ = v___y_4860_;
v___y_4839_ = v___y_4861_;
v___y_4840_ = v___y_4862_;
v___y_4841_ = v___y_4863_;
goto v___jp_4837_;
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
v___jp_4876_:
{
lean_object* v___x_4882_; uint8_t v___x_4883_; 
v___x_4882_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4883_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4880_, v___x_4882_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; 
lean_dec_ref(v_expectedType_4823_);
v___x_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4884_, 0, v_inst_4822_);
return v___x_4884_;
}
else
{
lean_object* v___x_4885_; 
lean_inc(v___y_4881_);
lean_inc_ref(v___y_4879_);
lean_inc(v___y_4878_);
lean_inc_ref(v___y_4877_);
lean_inc_ref(v_inst_4822_);
v___x_4885_ = lean_infer_type(v_inst_4822_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4881_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v___x_4887_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v___x_4885_);
lean_inc_ref(v_expectedType_4823_);
v___x_4887_ = l_Lean_Meta_isExprDefEq(v_expectedType_4823_, v_a_4886_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4881_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4940_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4940_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4940_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
uint8_t v___x_4892_; 
v___x_4892_ = lean_unbox(v_a_4888_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v_a_4895_; uint8_t v___x_4896_; uint8_t v___x_4897_; lean_object* v___x_4898_; 
lean_del_object(v___x_4890_);
v___x_4893_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_4894_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4893_, v___y_4881_);
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
lean_inc_n(v_a_4895_, 2);
lean_dec_ref(v___x_4894_);
v___x_4896_ = lean_unbox(v_a_4888_);
v___x_4897_ = lean_unbox(v_a_4888_);
lean_dec(v_a_4888_);
v___x_4898_ = l_Lean_Meta_mkAuxDefinition(v_a_4895_, v_expectedType_4823_, v_inst_4822_, v___x_4896_, v___x_4897_, v___x_4824_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4881_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; uint8_t v___x_4900_; lean_object* v___x_4901_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
lean_inc(v_a_4899_);
lean_dec_ref(v___x_4898_);
v___x_4900_ = 3;
lean_inc(v_a_4895_);
v___x_4901_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4895_, v___x_4900_, v___y_4878_, v___y_4881_);
lean_dec_ref(v___x_4901_);
if (v_isMeta_4827_ == 0)
{
v___y_4860_ = v_a_4895_;
v___y_4861_ = v_a_4899_;
v___y_4862_ = v___y_4879_;
v___y_4863_ = v___y_4881_;
goto v___jp_4859_;
}
else
{
lean_object* v___x_4902_; lean_object* v_env_4903_; lean_object* v_nextMacroScope_4904_; lean_object* v_ngen_4905_; lean_object* v_auxDeclNGen_4906_; lean_object* v_traceState_4907_; lean_object* v_messages_4908_; lean_object* v_infoState_4909_; lean_object* v_snapshotTasks_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4935_; 
v___x_4902_ = lean_st_ref_take(v___y_4881_);
v_env_4903_ = lean_ctor_get(v___x_4902_, 0);
v_nextMacroScope_4904_ = lean_ctor_get(v___x_4902_, 1);
v_ngen_4905_ = lean_ctor_get(v___x_4902_, 2);
v_auxDeclNGen_4906_ = lean_ctor_get(v___x_4902_, 3);
v_traceState_4907_ = lean_ctor_get(v___x_4902_, 4);
v_messages_4908_ = lean_ctor_get(v___x_4902_, 6);
v_infoState_4909_ = lean_ctor_get(v___x_4902_, 7);
v_snapshotTasks_4910_ = lean_ctor_get(v___x_4902_, 8);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4935_ == 0)
{
lean_object* v_unused_4936_; 
v_unused_4936_ = lean_ctor_get(v___x_4902_, 5);
lean_dec(v_unused_4936_);
v___x_4912_ = v___x_4902_;
v_isShared_4913_ = v_isSharedCheck_4935_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_snapshotTasks_4910_);
lean_inc(v_infoState_4909_);
lean_inc(v_messages_4908_);
lean_inc(v_traceState_4907_);
lean_inc(v_auxDeclNGen_4906_);
lean_inc(v_ngen_4905_);
lean_inc(v_nextMacroScope_4904_);
lean_inc(v_env_4903_);
lean_dec(v___x_4902_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4935_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4917_; 
lean_inc(v_a_4895_);
v___x_4914_ = l_Lean_markMeta(v_env_4903_, v_a_4895_);
v___x_4915_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 5, v___x_4915_);
lean_ctor_set(v___x_4912_, 0, v___x_4914_);
v___x_4917_ = v___x_4912_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_nextMacroScope_4904_);
lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_ngen_4905_);
lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_auxDeclNGen_4906_);
lean_ctor_set(v_reuseFailAlloc_4934_, 4, v_traceState_4907_);
lean_ctor_set(v_reuseFailAlloc_4934_, 5, v___x_4915_);
lean_ctor_set(v_reuseFailAlloc_4934_, 6, v_messages_4908_);
lean_ctor_set(v_reuseFailAlloc_4934_, 7, v_infoState_4909_);
lean_ctor_set(v_reuseFailAlloc_4934_, 8, v_snapshotTasks_4910_);
v___x_4917_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v_mctx_4920_; lean_object* v_zetaDeltaFVarIds_4921_; lean_object* v_postponed_4922_; lean_object* v_diag_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4932_; 
v___x_4918_ = lean_st_ref_set(v___y_4881_, v___x_4917_);
v___x_4919_ = lean_st_ref_take(v___y_4878_);
v_mctx_4920_ = lean_ctor_get(v___x_4919_, 0);
v_zetaDeltaFVarIds_4921_ = lean_ctor_get(v___x_4919_, 2);
v_postponed_4922_ = lean_ctor_get(v___x_4919_, 3);
v_diag_4923_ = lean_ctor_get(v___x_4919_, 4);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4932_ == 0)
{
lean_object* v_unused_4933_; 
v_unused_4933_ = lean_ctor_get(v___x_4919_, 1);
lean_dec(v_unused_4933_);
v___x_4925_ = v___x_4919_;
v_isShared_4926_ = v_isSharedCheck_4932_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_diag_4923_);
lean_inc(v_postponed_4922_);
lean_inc(v_zetaDeltaFVarIds_4921_);
lean_inc(v_mctx_4920_);
lean_dec(v___x_4919_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4932_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; lean_object* v___x_4929_; 
v___x_4927_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 1, v___x_4927_);
v___x_4929_ = v___x_4925_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_mctx_4920_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v___x_4927_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_zetaDeltaFVarIds_4921_);
lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_postponed_4922_);
lean_ctor_set(v_reuseFailAlloc_4931_, 4, v_diag_4923_);
v___x_4929_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4930_; 
v___x_4930_ = lean_st_ref_set(v___y_4878_, v___x_4929_);
v___y_4860_ = v_a_4895_;
v___y_4861_ = v_a_4899_;
v___y_4862_ = v___y_4879_;
v___y_4863_ = v___y_4881_;
goto v___jp_4859_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4895_);
return v___x_4898_;
}
}
else
{
lean_object* v___x_4938_; 
lean_dec(v_a_4888_);
lean_dec_ref(v_expectedType_4823_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v_inst_4822_);
v___x_4938_ = v___x_4890_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_inst_4822_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec_ref(v_expectedType_4823_);
lean_dec_ref(v_inst_4822_);
v_a_4941_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4887_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4887_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4823_);
lean_dec_ref(v_inst_4822_);
return v___x_4885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(lean_object* v_inst_5106_, lean_object* v_expectedType_5107_, uint8_t v___x_5108_, uint8_t v_compile_5109_, uint8_t v_logCompileErrors_5110_, uint8_t v_isMeta_5111_, lean_object* v_val_5112_, lean_object* v_x_5113_, lean_object* v_x_5114_, lean_object* v_x_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_){
_start:
{
lean_object* v___y_5122_; lean_object* v___y_5123_; lean_object* v___y_5124_; lean_object* v___y_5125_; lean_object* v___y_5144_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5147_; lean_object* v___y_5161_; lean_object* v___y_5162_; lean_object* v___y_5163_; lean_object* v_options_5164_; lean_object* v___y_5165_; 
if (lean_obj_tag(v_x_5113_) == 5)
{
lean_object* v_fn_5233_; lean_object* v_arg_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v_fn_5233_ = lean_ctor_get(v_x_5113_, 0);
lean_inc_ref(v_fn_5233_);
v_arg_5234_ = lean_ctor_get(v_x_5113_, 1);
lean_inc_ref(v_arg_5234_);
lean_dec_ref(v_x_5113_);
v___x_5235_ = lean_array_set(v_x_5114_, v_x_5115_, v_arg_5234_);
v___x_5236_ = lean_unsigned_to_nat(1u);
v___x_5237_ = lean_nat_sub(v_x_5115_, v___x_5236_);
v___x_5238_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(v_inst_5106_, v_expectedType_5107_, v___x_5108_, v_compile_5109_, v_logCompileErrors_5110_, v_isMeta_5111_, v_val_5112_, v_fn_5233_, v___x_5235_, v___x_5237_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
return v___x_5238_;
}
else
{
lean_object* v_cls_5239_; lean_object* v___y_5241_; lean_object* v___y_5242_; lean_object* v___y_5243_; lean_object* v___y_5244_; lean_object* v___x_5262_; 
v_cls_5239_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5262_ = l_Lean_Expr_constName_x3f(v_x_5113_);
if (lean_obj_tag(v___x_5262_) == 0)
{
lean_dec_ref(v_x_5114_);
lean_dec_ref(v_x_5113_);
lean_dec(v_val_5112_);
v___y_5241_ = v___y_5116_;
v___y_5242_ = v___y_5117_;
v___y_5243_ = v___y_5118_;
v___y_5244_ = v___y_5119_;
goto v___jp_5240_;
}
else
{
lean_object* v_val_5263_; lean_object* v___x_5264_; 
v_val_5263_ = lean_ctor_get(v___x_5262_, 0);
lean_inc(v_val_5263_);
lean_dec_ref(v___x_5262_);
v___x_5264_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_5263_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5264_) == 0)
{
lean_object* v_a_5265_; 
v_a_5265_ = lean_ctor_get(v___x_5264_, 0);
lean_inc(v_a_5265_);
lean_dec_ref(v___x_5264_);
if (lean_obj_tag(v_a_5265_) == 6)
{
lean_object* v_val_5266_; lean_object* v___x_5267_; 
lean_dec_ref(v_inst_5106_);
v_val_5266_ = lean_ctor_get(v_a_5265_, 0);
lean_inc_ref(v_val_5266_);
lean_dec_ref(v_a_5265_);
lean_inc(v___y_5119_);
lean_inc_ref(v___y_5118_);
lean_inc(v___y_5117_);
lean_inc_ref(v___y_5116_);
lean_inc_ref(v_x_5113_);
v___x_5267_ = lean_infer_type(v_x_5113_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5267_) == 0)
{
lean_object* v_a_5268_; uint8_t v___x_5269_; lean_object* v___x_5270_; 
v_a_5268_ = lean_ctor_get(v___x_5267_, 0);
lean_inc(v_a_5268_);
lean_dec_ref(v___x_5267_);
v___x_5269_ = 0;
v___x_5270_ = l_Lean_Meta_forallMetaTelescope(v_a_5268_, v___x_5269_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5270_) == 0)
{
lean_object* v_a_5271_; lean_object* v_snd_5272_; lean_object* v_fst_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5373_; 
v_a_5271_ = lean_ctor_get(v___x_5270_, 0);
lean_inc(v_a_5271_);
lean_dec_ref(v___x_5270_);
v_snd_5272_ = lean_ctor_get(v_a_5271_, 1);
v_fst_5273_ = lean_ctor_get(v_a_5271_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v_a_5271_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5275_ = v_a_5271_;
v_isShared_5276_ = v_isSharedCheck_5373_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_snd_5272_);
lean_inc(v_fst_5273_);
lean_dec(v_a_5271_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5373_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v_snd_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5371_; 
v_snd_5277_ = lean_ctor_get(v_snd_5272_, 1);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_snd_5272_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v_snd_5272_, 0);
lean_dec(v_unused_5372_);
v___x_5279_ = v_snd_5272_;
v_isShared_5280_ = v_isSharedCheck_5371_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_snd_5277_);
lean_dec(v_snd_5272_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5371_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5281_; lean_object* v___y_5283_; lean_object* v___y_5284_; lean_object* v___y_5285_; lean_object* v___y_5286_; lean_object* v___x_5318_; uint8_t v___x_5319_; 
v___x_5281_ = lean_array_get_size(v_x_5114_);
v___x_5318_ = lean_array_get_size(v_fst_5273_);
v___x_5319_ = lean_nat_dec_eq(v___x_5281_, v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5323_; 
lean_dec(v_snd_5277_);
lean_dec(v_fst_5273_);
lean_dec_ref(v_val_5266_);
lean_dec(v_val_5112_);
lean_dec_ref(v_expectedType_5107_);
v___x_5320_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_5321_ = l_Lean_MessageData_ofExpr(v_x_5113_);
if (v_isShared_5280_ == 0)
{
lean_ctor_set_tag(v___x_5279_, 7);
lean_ctor_set(v___x_5279_, 1, v___x_5321_);
lean_ctor_set(v___x_5279_, 0, v___x_5320_);
v___x_5323_ = v___x_5279_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5320_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v___x_5321_);
v___x_5323_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; lean_object* v___x_5326_; 
v___x_5324_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___closed__3);
if (v_isShared_5276_ == 0)
{
lean_ctor_set_tag(v___x_5275_, 7);
lean_ctor_set(v___x_5275_, 1, v___x_5324_);
lean_ctor_set(v___x_5275_, 0, v___x_5323_);
v___x_5326_ = v___x_5275_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5323_);
lean_ctor_set(v_reuseFailAlloc_5333_, 1, v___x_5324_);
v___x_5326_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; 
v___x_5327_ = lean_array_to_list(v_x_5114_);
v___x_5328_ = lean_box(0);
v___x_5329_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_5327_, v___x_5328_);
v___x_5330_ = l_Lean_MessageData_ofList(v___x_5329_);
v___x_5331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5326_);
lean_ctor_set(v___x_5331_, 1, v___x_5330_);
v___x_5332_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5331_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
return v___x_5332_;
}
}
}
else
{
lean_object* v___x_5335_; 
lean_inc_ref(v_expectedType_5107_);
v___x_5335_ = l_Lean_Meta_isExprDefEq(v_expectedType_5107_, v_snd_5277_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; uint8_t v___x_5337_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
lean_inc(v_a_5336_);
lean_dec_ref(v___x_5335_);
v___x_5337_ = lean_unbox(v_a_5336_);
if (v___x_5337_ == 0)
{
lean_object* v_toConstantVal_5338_; lean_object* v_name_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5343_; 
lean_dec(v_fst_5273_);
lean_dec_ref(v_x_5114_);
lean_dec_ref(v_x_5113_);
lean_dec(v_val_5112_);
v_toConstantVal_5338_ = lean_ctor_get(v_val_5266_, 0);
lean_inc_ref(v_toConstantVal_5338_);
lean_dec_ref(v_val_5266_);
v_name_5339_ = lean_ctor_get(v_toConstantVal_5338_, 0);
lean_inc(v_name_5339_);
lean_dec_ref(v_toConstantVal_5338_);
v___x_5340_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_5341_ = l_Lean_MessageData_ofExpr(v_expectedType_5107_);
if (v_isShared_5280_ == 0)
{
lean_ctor_set_tag(v___x_5279_, 7);
lean_ctor_set(v___x_5279_, 1, v___x_5341_);
lean_ctor_set(v___x_5279_, 0, v___x_5340_);
v___x_5343_ = v___x_5279_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5340_);
lean_ctor_set(v_reuseFailAlloc_5362_, 1, v___x_5341_);
v___x_5343_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
lean_object* v___x_5344_; lean_object* v___x_5346_; 
v___x_5344_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_5276_ == 0)
{
lean_ctor_set_tag(v___x_5275_, 7);
lean_ctor_set(v___x_5275_, 1, v___x_5344_);
lean_ctor_set(v___x_5275_, 0, v___x_5343_);
v___x_5346_ = v___x_5275_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5361_, 1, v___x_5344_);
v___x_5346_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
uint8_t v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5360_; 
v___x_5347_ = lean_unbox(v_a_5336_);
lean_dec(v_a_5336_);
v___x_5348_ = l_Lean_MessageData_ofConstName(v_name_5339_, v___x_5347_);
v___x_5349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5349_, 0, v___x_5346_);
lean_ctor_set(v___x_5349_, 1, v___x_5348_);
v___x_5350_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_5351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5351_, 0, v___x_5349_);
lean_ctor_set(v___x_5351_, 1, v___x_5350_);
v___x_5352_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5351_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5355_ = v___x_5352_;
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5352_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5358_; 
if (v_isShared_5356_ == 0)
{
v___x_5358_ = v___x_5355_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5353_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
}
else
{
lean_dec(v_a_5336_);
lean_del_object(v___x_5279_);
lean_del_object(v___x_5275_);
v___y_5283_ = v___y_5116_;
v___y_5284_ = v___y_5117_;
v___y_5285_ = v___y_5118_;
v___y_5286_ = v___y_5119_;
goto v___jp_5282_;
}
}
else
{
lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5370_; 
lean_del_object(v___x_5279_);
lean_del_object(v___x_5275_);
lean_dec(v_fst_5273_);
lean_dec_ref(v_val_5266_);
lean_dec_ref(v_x_5114_);
lean_dec_ref(v_x_5113_);
lean_dec(v_val_5112_);
lean_dec_ref(v_expectedType_5107_);
v_a_5363_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5365_ = v___x_5335_;
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5335_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5368_; 
if (v_isShared_5366_ == 0)
{
v___x_5368_ = v___x_5365_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5363_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
v___jp_5282_:
{
lean_object* v_numParams_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
v_numParams_5287_ = lean_ctor_get(v_val_5266_, 3);
lean_inc(v_numParams_5287_);
lean_dec_ref(v_val_5266_);
v___x_5288_ = lean_box(0);
v___x_5289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v___x_5281_, v_fst_5273_, v_x_5114_, v___x_5108_, v_compile_5109_, v_logCompileErrors_5110_, v_isMeta_5111_, v_val_5112_, v_expectedType_5107_, v_numParams_5287_, v___x_5288_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
lean_dec_ref(v_x_5114_);
if (lean_obj_tag(v___x_5289_) == 0)
{
size_t v_sz_5290_; size_t v___x_5291_; lean_object* v___x_5292_; 
lean_dec_ref(v___x_5289_);
v_sz_5290_ = lean_array_size(v_fst_5273_);
v___x_5291_ = ((size_t)0ULL);
v___x_5292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_5290_, v___x_5291_, v_fst_5273_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5301_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5295_ = v___x_5292_;
v_isShared_5296_ = v_isSharedCheck_5301_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5292_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5301_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5297_; lean_object* v___x_5299_; 
v___x_5297_ = l_Lean_mkAppN(v_x_5113_, v_a_5293_);
lean_dec(v_a_5293_);
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 0, v___x_5297_);
v___x_5299_ = v___x_5295_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5297_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_dec_ref(v_x_5113_);
v_a_5302_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5292_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5292_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
else
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5317_; 
lean_dec(v_fst_5273_);
lean_dec_ref(v_x_5113_);
v_a_5310_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5312_ = v___x_5289_;
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5289_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
if (v_isShared_5313_ == 0)
{
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec_ref(v_val_5266_);
lean_dec_ref(v_x_5114_);
lean_dec_ref(v_x_5113_);
lean_dec(v_val_5112_);
lean_dec_ref(v_expectedType_5107_);
v_a_5374_ = lean_ctor_get(v___x_5270_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5270_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5270_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
else
{
lean_dec_ref(v_val_5266_);
lean_dec_ref(v_x_5114_);
lean_dec_ref(v_x_5113_);
lean_dec(v_val_5112_);
lean_dec_ref(v_expectedType_5107_);
return v___x_5267_;
}
}
else
{
lean_dec(v_a_5265_);
lean_dec_ref(v_x_5114_);
lean_dec_ref(v_x_5113_);
lean_dec(v_val_5112_);
v___y_5241_ = v___y_5116_;
v___y_5242_ = v___y_5117_;
v___y_5243_ = v___y_5118_;
v___y_5244_ = v___y_5119_;
goto v___jp_5240_;
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_dec_ref(v_x_5114_);
lean_dec_ref(v_x_5113_);
lean_dec(v_val_5112_);
lean_dec_ref(v_expectedType_5107_);
lean_dec_ref(v_inst_5106_);
v_a_5382_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5264_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5264_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
v___jp_5240_:
{
lean_object* v_options_5245_; uint8_t v_hasTrace_5246_; 
v_options_5245_ = lean_ctor_get(v___y_5243_, 2);
v_hasTrace_5246_ = lean_ctor_get_uint8(v_options_5245_, sizeof(void*)*1);
if (v_hasTrace_5246_ == 0)
{
v___y_5161_ = v___y_5241_;
v___y_5162_ = v___y_5242_;
v___y_5163_ = v___y_5243_;
v_options_5164_ = v_options_5245_;
v___y_5165_ = v___y_5244_;
goto v___jp_5160_;
}
else
{
lean_object* v_inheritedTraceOptions_5247_; lean_object* v___x_5248_; uint8_t v___x_5249_; 
v_inheritedTraceOptions_5247_ = lean_ctor_get(v___y_5243_, 13);
v___x_5248_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5249_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5247_, v_options_5245_, v___x_5248_);
if (v___x_5249_ == 0)
{
v___y_5161_ = v___y_5241_;
v___y_5162_ = v___y_5242_;
v___y_5163_ = v___y_5243_;
v_options_5164_ = v_options_5245_;
v___y_5165_ = v___y_5244_;
goto v___jp_5160_;
}
else
{
lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
v___x_5250_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_5106_);
v___x_5251_ = l_Lean_MessageData_ofExpr(v_inst_5106_);
v___x_5252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5250_);
lean_ctor_set(v___x_5252_, 1, v___x_5251_);
v___x_5253_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5239_, v___x_5252_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
if (lean_obj_tag(v___x_5253_) == 0)
{
lean_dec_ref(v___x_5253_);
v___y_5161_ = v___y_5241_;
v___y_5162_ = v___y_5242_;
v___y_5163_ = v___y_5243_;
v_options_5164_ = v_options_5245_;
v___y_5165_ = v___y_5244_;
goto v___jp_5160_;
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
lean_dec_ref(v_expectedType_5107_);
lean_dec_ref(v_inst_5106_);
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5253_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
}
}
v___jp_5121_:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Lean_enableRealizationsForConst(v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5133_ == 0)
{
lean_object* v_unused_5134_; 
v_unused_5134_ = lean_ctor_get(v___x_5126_, 0);
lean_dec(v_unused_5134_);
v___x_5128_ = v___x_5126_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_dec(v___x_5126_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v___y_5122_);
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___y_5122_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
lean_dec_ref(v___y_5122_);
v_a_5135_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5137_ = v___x_5126_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5126_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
v___jp_5143_:
{
if (v_compile_5109_ == 0)
{
v___y_5122_ = v___y_5144_;
v___y_5123_ = v___y_5145_;
v___y_5124_ = v___y_5146_;
v___y_5125_ = v___y_5147_;
goto v___jp_5121_;
}
else
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5148_ = lean_unsigned_to_nat(1u);
v___x_5149_ = lean_mk_empty_array_with_capacity(v___x_5148_);
lean_inc(v___y_5145_);
v___x_5150_ = lean_array_push(v___x_5149_, v___y_5145_);
v___x_5151_ = l_Lean_compileDecls(v___x_5150_, v_logCompileErrors_5110_, v___y_5146_, v___y_5147_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_dec_ref(v___x_5151_);
v___y_5122_ = v___y_5144_;
v___y_5123_ = v___y_5145_;
v___y_5124_ = v___y_5146_;
v___y_5125_ = v___y_5147_;
goto v___jp_5121_;
}
else
{
lean_object* v_a_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5159_; 
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5154_ = v___x_5151_;
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_a_5152_);
lean_dec(v___x_5151_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v___x_5157_; 
if (v_isShared_5155_ == 0)
{
v___x_5157_ = v___x_5154_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5152_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
}
}
v___jp_5160_:
{
lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___x_5166_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5167_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5164_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; 
lean_dec_ref(v_expectedType_5107_);
v___x_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5168_, 0, v_inst_5106_);
return v___x_5168_;
}
else
{
lean_object* v___x_5169_; 
lean_inc(v___y_5165_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
lean_inc_ref(v_inst_5106_);
v___x_5169_ = lean_infer_type(v_inst_5106_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5165_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; lean_object* v___x_5171_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
lean_dec_ref(v___x_5169_);
lean_inc_ref(v_expectedType_5107_);
v___x_5171_ = l_Lean_Meta_isExprDefEq(v_expectedType_5107_, v_a_5170_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5165_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5224_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5174_ = v___x_5171_;
v_isShared_5175_ = v_isSharedCheck_5224_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5171_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5224_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
uint8_t v___x_5176_; 
v___x_5176_ = lean_unbox(v_a_5172_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v_a_5179_; uint8_t v___x_5180_; uint8_t v___x_5181_; lean_object* v___x_5182_; 
lean_del_object(v___x_5174_);
v___x_5177_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_5178_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_5177_, v___y_5165_);
v_a_5179_ = lean_ctor_get(v___x_5178_, 0);
lean_inc_n(v_a_5179_, 2);
lean_dec_ref(v___x_5178_);
v___x_5180_ = lean_unbox(v_a_5172_);
v___x_5181_ = lean_unbox(v_a_5172_);
lean_dec(v_a_5172_);
v___x_5182_ = l_Lean_Meta_mkAuxDefinition(v_a_5179_, v_expectedType_5107_, v_inst_5106_, v___x_5180_, v___x_5181_, v___x_5108_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5165_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; uint8_t v___x_5184_; lean_object* v___x_5185_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
lean_dec_ref(v___x_5182_);
v___x_5184_ = 3;
lean_inc(v_a_5179_);
v___x_5185_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_5179_, v___x_5184_, v___y_5162_, v___y_5165_);
lean_dec_ref(v___x_5185_);
if (v_isMeta_5111_ == 0)
{
v___y_5144_ = v_a_5183_;
v___y_5145_ = v_a_5179_;
v___y_5146_ = v___y_5163_;
v___y_5147_ = v___y_5165_;
goto v___jp_5143_;
}
else
{
lean_object* v___x_5186_; lean_object* v_env_5187_; lean_object* v_nextMacroScope_5188_; lean_object* v_ngen_5189_; lean_object* v_auxDeclNGen_5190_; lean_object* v_traceState_5191_; lean_object* v_messages_5192_; lean_object* v_infoState_5193_; lean_object* v_snapshotTasks_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5219_; 
v___x_5186_ = lean_st_ref_take(v___y_5165_);
v_env_5187_ = lean_ctor_get(v___x_5186_, 0);
v_nextMacroScope_5188_ = lean_ctor_get(v___x_5186_, 1);
v_ngen_5189_ = lean_ctor_get(v___x_5186_, 2);
v_auxDeclNGen_5190_ = lean_ctor_get(v___x_5186_, 3);
v_traceState_5191_ = lean_ctor_get(v___x_5186_, 4);
v_messages_5192_ = lean_ctor_get(v___x_5186_, 6);
v_infoState_5193_ = lean_ctor_get(v___x_5186_, 7);
v_snapshotTasks_5194_ = lean_ctor_get(v___x_5186_, 8);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5219_ == 0)
{
lean_object* v_unused_5220_; 
v_unused_5220_ = lean_ctor_get(v___x_5186_, 5);
lean_dec(v_unused_5220_);
v___x_5196_ = v___x_5186_;
v_isShared_5197_ = v_isSharedCheck_5219_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_snapshotTasks_5194_);
lean_inc(v_infoState_5193_);
lean_inc(v_messages_5192_);
lean_inc(v_traceState_5191_);
lean_inc(v_auxDeclNGen_5190_);
lean_inc(v_ngen_5189_);
lean_inc(v_nextMacroScope_5188_);
lean_inc(v_env_5187_);
lean_dec(v___x_5186_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5219_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5201_; 
lean_inc(v_a_5179_);
v___x_5198_ = l_Lean_markMeta(v_env_5187_, v_a_5179_);
v___x_5199_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 5, v___x_5199_);
lean_ctor_set(v___x_5196_, 0, v___x_5198_);
v___x_5201_ = v___x_5196_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5198_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_nextMacroScope_5188_);
lean_ctor_set(v_reuseFailAlloc_5218_, 2, v_ngen_5189_);
lean_ctor_set(v_reuseFailAlloc_5218_, 3, v_auxDeclNGen_5190_);
lean_ctor_set(v_reuseFailAlloc_5218_, 4, v_traceState_5191_);
lean_ctor_set(v_reuseFailAlloc_5218_, 5, v___x_5199_);
lean_ctor_set(v_reuseFailAlloc_5218_, 6, v_messages_5192_);
lean_ctor_set(v_reuseFailAlloc_5218_, 7, v_infoState_5193_);
lean_ctor_set(v_reuseFailAlloc_5218_, 8, v_snapshotTasks_5194_);
v___x_5201_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v_mctx_5204_; lean_object* v_zetaDeltaFVarIds_5205_; lean_object* v_postponed_5206_; lean_object* v_diag_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5216_; 
v___x_5202_ = lean_st_ref_set(v___y_5165_, v___x_5201_);
v___x_5203_ = lean_st_ref_take(v___y_5162_);
v_mctx_5204_ = lean_ctor_get(v___x_5203_, 0);
v_zetaDeltaFVarIds_5205_ = lean_ctor_get(v___x_5203_, 2);
v_postponed_5206_ = lean_ctor_get(v___x_5203_, 3);
v_diag_5207_ = lean_ctor_get(v___x_5203_, 4);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5216_ == 0)
{
lean_object* v_unused_5217_; 
v_unused_5217_ = lean_ctor_get(v___x_5203_, 1);
lean_dec(v_unused_5217_);
v___x_5209_ = v___x_5203_;
v_isShared_5210_ = v_isSharedCheck_5216_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_diag_5207_);
lean_inc(v_postponed_5206_);
lean_inc(v_zetaDeltaFVarIds_5205_);
lean_inc(v_mctx_5204_);
lean_dec(v___x_5203_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5216_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5211_; lean_object* v___x_5213_; 
v___x_5211_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 1, v___x_5211_);
v___x_5213_ = v___x_5209_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_mctx_5204_);
lean_ctor_set(v_reuseFailAlloc_5215_, 1, v___x_5211_);
lean_ctor_set(v_reuseFailAlloc_5215_, 2, v_zetaDeltaFVarIds_5205_);
lean_ctor_set(v_reuseFailAlloc_5215_, 3, v_postponed_5206_);
lean_ctor_set(v_reuseFailAlloc_5215_, 4, v_diag_5207_);
v___x_5213_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
lean_object* v___x_5214_; 
v___x_5214_ = lean_st_ref_set(v___y_5162_, v___x_5213_);
v___y_5144_ = v_a_5183_;
v___y_5145_ = v_a_5179_;
v___y_5146_ = v___y_5163_;
v___y_5147_ = v___y_5165_;
goto v___jp_5143_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5179_);
return v___x_5182_;
}
}
else
{
lean_object* v___x_5222_; 
lean_dec(v_a_5172_);
lean_dec_ref(v_expectedType_5107_);
if (v_isShared_5175_ == 0)
{
lean_ctor_set(v___x_5174_, 0, v_inst_5106_);
v___x_5222_ = v___x_5174_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_inst_5106_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
lean_dec_ref(v_expectedType_5107_);
lean_dec_ref(v_inst_5106_);
v_a_5225_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5171_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5171_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_5107_);
lean_dec_ref(v_inst_5106_);
return v___x_5169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object* v_expectedType_5390_, lean_object* v_inst_5391_, uint8_t v___x_5392_, uint8_t v_compile_5393_, uint8_t v_logCompileErrors_5394_, uint8_t v_isMeta_5395_, lean_object* v_val_5396_, lean_object* v_____r_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v___x_5403_; 
lean_inc_ref(v_expectedType_5390_);
v___x_5403_ = l_Lean_Meta_isProp(v_expectedType_5390_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5425_; 
v_a_5404_ = lean_ctor_get(v___x_5403_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5406_ = v___x_5403_;
v_isShared_5407_ = v_isSharedCheck_5425_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5403_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5425_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
uint8_t v___x_5408_; 
v___x_5408_ = lean_unbox(v_a_5404_);
lean_dec(v_a_5404_);
if (v___x_5408_ == 0)
{
lean_object* v___x_5409_; 
lean_del_object(v___x_5406_);
lean_inc(v___y_5401_);
lean_inc_ref(v___y_5400_);
lean_inc(v___y_5399_);
lean_inc_ref(v___y_5398_);
lean_inc_ref(v_inst_5391_);
v___x_5409_ = lean_whnf(v_inst_5391_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5409_) == 0)
{
lean_object* v_a_5410_; lean_object* v_dummy_5411_; lean_object* v_nargs_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
v_a_5410_ = lean_ctor_get(v___x_5409_, 0);
lean_inc(v_a_5410_);
lean_dec_ref(v___x_5409_);
v_dummy_5411_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5412_ = l_Lean_Expr_getAppNumArgs(v_a_5410_);
lean_inc(v_nargs_5412_);
v___x_5413_ = lean_mk_array(v_nargs_5412_, v_dummy_5411_);
v___x_5414_ = lean_unsigned_to_nat(1u);
v___x_5415_ = lean_nat_sub(v_nargs_5412_, v___x_5414_);
lean_dec(v_nargs_5412_);
v___x_5416_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(v_inst_5391_, v_expectedType_5390_, v___x_5392_, v_compile_5393_, v_logCompileErrors_5394_, v_isMeta_5395_, v_val_5396_, v_a_5410_, v___x_5413_, v___x_5415_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
lean_dec(v___x_5415_);
return v___x_5416_;
}
else
{
lean_dec(v_val_5396_);
lean_dec_ref(v_inst_5391_);
lean_dec_ref(v_expectedType_5390_);
return v___x_5409_;
}
}
else
{
lean_object* v_options_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; 
lean_dec(v_val_5396_);
v_options_5417_ = lean_ctor_get(v___y_5400_, 2);
v___x_5418_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5419_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5417_, v___x_5418_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5421_; 
lean_dec_ref(v_expectedType_5390_);
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 0, v_inst_5391_);
v___x_5421_ = v___x_5406_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_inst_5391_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
else
{
lean_object* v___x_5423_; lean_object* v___x_5424_; 
lean_del_object(v___x_5406_);
v___x_5423_ = lean_box(0);
v___x_5424_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5390_, v_inst_5391_, v___x_5392_, v___x_5423_, v___x_5392_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
return v___x_5424_;
}
}
}
}
else
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5433_; 
lean_dec(v_val_5396_);
lean_dec_ref(v_inst_5391_);
lean_dec_ref(v_expectedType_5390_);
v_a_5426_ = lean_ctor_get(v___x_5403_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5428_ = v___x_5403_;
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5403_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5431_; 
if (v_isShared_5429_ == 0)
{
v___x_5431_ = v___x_5428_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_a_5426_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object* v_inst_5434_, lean_object* v_expectedType_5435_, uint8_t v_compile_5436_, uint8_t v_logCompileErrors_5437_, uint8_t v_isMeta_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_){
_start:
{
lean_object* v___x_5444_; lean_object* v_options_5445_; uint8_t v_foApprox_5446_; uint8_t v_ctxApprox_5447_; uint8_t v_quasiPatternApprox_5448_; uint8_t v_constApprox_5449_; uint8_t v_isDefEqStuckEx_5450_; uint8_t v_unificationHints_5451_; uint8_t v_proofIrrelevance_5452_; uint8_t v_assignSyntheticOpaque_5453_; uint8_t v_offsetCnstrs_5454_; uint8_t v_etaStruct_5455_; uint8_t v_univApprox_5456_; uint8_t v_iota_5457_; uint8_t v_beta_5458_; uint8_t v_proj_5459_; uint8_t v_zeta_5460_; uint8_t v_zetaDelta_5461_; uint8_t v_zetaUnused_5462_; uint8_t v_zetaHave_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5714_; 
v___x_5444_ = l_Lean_Meta_Context_config(v_a_5439_);
v_options_5445_ = lean_ctor_get(v_a_5441_, 2);
v_foApprox_5446_ = lean_ctor_get_uint8(v___x_5444_, 0);
v_ctxApprox_5447_ = lean_ctor_get_uint8(v___x_5444_, 1);
v_quasiPatternApprox_5448_ = lean_ctor_get_uint8(v___x_5444_, 2);
v_constApprox_5449_ = lean_ctor_get_uint8(v___x_5444_, 3);
v_isDefEqStuckEx_5450_ = lean_ctor_get_uint8(v___x_5444_, 4);
v_unificationHints_5451_ = lean_ctor_get_uint8(v___x_5444_, 5);
v_proofIrrelevance_5452_ = lean_ctor_get_uint8(v___x_5444_, 6);
v_assignSyntheticOpaque_5453_ = lean_ctor_get_uint8(v___x_5444_, 7);
v_offsetCnstrs_5454_ = lean_ctor_get_uint8(v___x_5444_, 8);
v_etaStruct_5455_ = lean_ctor_get_uint8(v___x_5444_, 10);
v_univApprox_5456_ = lean_ctor_get_uint8(v___x_5444_, 11);
v_iota_5457_ = lean_ctor_get_uint8(v___x_5444_, 12);
v_beta_5458_ = lean_ctor_get_uint8(v___x_5444_, 13);
v_proj_5459_ = lean_ctor_get_uint8(v___x_5444_, 14);
v_zeta_5460_ = lean_ctor_get_uint8(v___x_5444_, 15);
v_zetaDelta_5461_ = lean_ctor_get_uint8(v___x_5444_, 16);
v_zetaUnused_5462_ = lean_ctor_get_uint8(v___x_5444_, 17);
v_zetaHave_5463_ = lean_ctor_get_uint8(v___x_5444_, 18);
v_isSharedCheck_5714_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5714_ == 0)
{
v___x_5465_ = v___x_5444_;
v_isShared_5466_ = v_isSharedCheck_5714_;
goto v_resetjp_5464_;
}
else
{
lean_dec(v___x_5444_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5714_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
uint8_t v_trackZetaDelta_5467_; lean_object* v_zetaDeltaSet_5468_; lean_object* v_lctx_5469_; lean_object* v_localInstances_5470_; lean_object* v_defEqCtx_x3f_5471_; lean_object* v_synthPendingDepth_5472_; lean_object* v_canUnfold_x3f_5473_; uint8_t v_univApprox_5474_; uint8_t v_inTypeClassResolution_5475_; uint8_t v_cacheInferType_5476_; lean_object* v_inheritedTraceOptions_5477_; uint8_t v_hasTrace_5478_; uint8_t v___x_5479_; lean_object* v_config_5481_; 
v_trackZetaDelta_5467_ = lean_ctor_get_uint8(v_a_5439_, sizeof(void*)*7);
v_zetaDeltaSet_5468_ = lean_ctor_get(v_a_5439_, 1);
v_lctx_5469_ = lean_ctor_get(v_a_5439_, 2);
v_localInstances_5470_ = lean_ctor_get(v_a_5439_, 3);
v_defEqCtx_x3f_5471_ = lean_ctor_get(v_a_5439_, 4);
v_synthPendingDepth_5472_ = lean_ctor_get(v_a_5439_, 5);
v_canUnfold_x3f_5473_ = lean_ctor_get(v_a_5439_, 6);
v_univApprox_5474_ = lean_ctor_get_uint8(v_a_5439_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5475_ = lean_ctor_get_uint8(v_a_5439_, sizeof(void*)*7 + 2);
v_cacheInferType_5476_ = lean_ctor_get_uint8(v_a_5439_, sizeof(void*)*7 + 3);
v_inheritedTraceOptions_5477_ = lean_ctor_get(v_a_5441_, 13);
v_hasTrace_5478_ = lean_ctor_get_uint8(v_options_5445_, sizeof(void*)*1);
v___x_5479_ = 3;
if (v_isShared_5466_ == 0)
{
v_config_5481_ = v___x_5465_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 0, v_foApprox_5446_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 1, v_ctxApprox_5447_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 2, v_quasiPatternApprox_5448_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 3, v_constApprox_5449_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 4, v_isDefEqStuckEx_5450_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 5, v_unificationHints_5451_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 6, v_proofIrrelevance_5452_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 7, v_assignSyntheticOpaque_5453_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 8, v_offsetCnstrs_5454_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 10, v_etaStruct_5455_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 11, v_univApprox_5456_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 12, v_iota_5457_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 13, v_beta_5458_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 14, v_proj_5459_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 15, v_zeta_5460_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 16, v_zetaDelta_5461_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 17, v_zetaUnused_5462_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, 18, v_zetaHave_5463_);
v_config_5481_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
uint64_t v___x_5482_; uint64_t v___x_5483_; uint64_t v___x_5484_; uint64_t v___x_5485_; uint64_t v___x_5486_; uint64_t v_key_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; 
lean_ctor_set_uint8(v_config_5481_, 9, v___x_5479_);
v___x_5482_ = l_Lean_Meta_Context_configKey(v_a_5439_);
v___x_5483_ = 2ULL;
v___x_5484_ = lean_uint64_shift_right(v___x_5482_, v___x_5483_);
v___x_5485_ = lean_uint64_shift_left(v___x_5484_, v___x_5483_);
v___x_5486_ = lean_uint64_once(&l_Lean_Meta_wrapInstance___closed__0, &l_Lean_Meta_wrapInstance___closed__0_once, _init_l_Lean_Meta_wrapInstance___closed__0);
v_key_5487_ = lean_uint64_lor(v___x_5485_, v___x_5486_);
v___x_5488_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5488_, 0, v_config_5481_);
lean_ctor_set_uint64(v___x_5488_, sizeof(void*)*1, v_key_5487_);
lean_inc(v_canUnfold_x3f_5473_);
lean_inc(v_synthPendingDepth_5472_);
lean_inc(v_defEqCtx_x3f_5471_);
lean_inc_ref(v_localInstances_5470_);
lean_inc_ref(v_lctx_5469_);
lean_inc(v_zetaDeltaSet_5468_);
v___x_5489_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5489_, 0, v___x_5488_);
lean_ctor_set(v___x_5489_, 1, v_zetaDeltaSet_5468_);
lean_ctor_set(v___x_5489_, 2, v_lctx_5469_);
lean_ctor_set(v___x_5489_, 3, v_localInstances_5470_);
lean_ctor_set(v___x_5489_, 4, v_defEqCtx_x3f_5471_);
lean_ctor_set(v___x_5489_, 5, v_synthPendingDepth_5472_);
lean_ctor_set(v___x_5489_, 6, v_canUnfold_x3f_5473_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*7, v_trackZetaDelta_5467_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*7 + 1, v_univApprox_5474_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5475_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*7 + 3, v_cacheInferType_5476_);
if (v_hasTrace_5478_ == 0)
{
lean_object* v___x_5490_; 
lean_inc_ref(v_expectedType_5435_);
v___x_5490_ = l_Lean_Meta_isClass_x3f(v_expectedType_5435_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5529_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5493_ = v___x_5490_;
v_isShared_5494_ = v_isSharedCheck_5529_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5490_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5529_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
if (lean_obj_tag(v_a_5491_) == 1)
{
lean_object* v_val_5495_; lean_object* v___x_5496_; 
lean_del_object(v___x_5493_);
v_val_5495_ = lean_ctor_get(v_a_5491_, 0);
lean_inc(v_val_5495_);
lean_dec_ref(v_a_5491_);
lean_inc_ref(v_expectedType_5435_);
v___x_5496_ = l_Lean_Meta_isProp(v_expectedType_5435_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5496_) == 0)
{
lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5517_; 
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5499_ = v___x_5496_;
v_isShared_5500_ = v_isSharedCheck_5517_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v___x_5496_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5517_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
uint8_t v___x_5501_; 
v___x_5501_ = lean_unbox(v_a_5497_);
lean_dec(v_a_5497_);
if (v___x_5501_ == 0)
{
lean_object* v___x_5502_; 
lean_del_object(v___x_5499_);
lean_inc(v_a_5442_);
lean_inc_ref(v_a_5441_);
lean_inc(v_a_5440_);
lean_inc_ref(v___x_5489_);
lean_inc_ref(v_inst_5434_);
v___x_5502_ = lean_whnf(v_inst_5434_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v_dummy_5504_; lean_object* v_nargs_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
lean_dec_ref(v___x_5502_);
v_dummy_5504_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5505_ = l_Lean_Expr_getAppNumArgs(v_a_5503_);
lean_inc(v_nargs_5505_);
v___x_5506_ = lean_mk_array(v_nargs_5505_, v_dummy_5504_);
v___x_5507_ = lean_unsigned_to_nat(1u);
v___x_5508_ = lean_nat_sub(v_nargs_5505_, v___x_5507_);
lean_dec(v_nargs_5505_);
v___x_5509_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(v_inst_5434_, v_expectedType_5435_, v_hasTrace_5478_, v_compile_5436_, v_logCompileErrors_5437_, v_isMeta_5438_, v_val_5495_, v_a_5503_, v___x_5506_, v___x_5508_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
lean_dec_ref(v___x_5489_);
lean_dec(v___x_5508_);
return v___x_5509_;
}
else
{
lean_dec(v_val_5495_);
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
return v___x_5502_;
}
}
else
{
lean_object* v___x_5510_; uint8_t v___x_5511_; 
lean_dec(v_val_5495_);
v___x_5510_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5511_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5445_, v___x_5510_);
if (v___x_5511_ == 0)
{
lean_object* v___x_5513_; 
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
if (v_isShared_5500_ == 0)
{
lean_ctor_set(v___x_5499_, 0, v_inst_5434_);
v___x_5513_ = v___x_5499_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_inst_5434_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
else
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
lean_del_object(v___x_5499_);
v___x_5515_ = lean_box(0);
v___x_5516_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5435_, v_inst_5434_, v___x_5511_, v___x_5515_, v___x_5511_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
lean_dec_ref(v___x_5489_);
return v___x_5516_;
}
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
lean_dec(v_val_5495_);
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5518_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5496_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5496_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
else
{
lean_object* v___x_5527_; 
lean_dec(v_a_5491_);
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 0, v_inst_5434_);
v___x_5527_ = v___x_5493_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_inst_5434_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
else
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5537_; 
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5530_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5490_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5490_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5535_; 
if (v_isShared_5533_ == 0)
{
v___x_5535_ = v___x_5532_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
else
{
lean_object* v___f_5538_; lean_object* v_cls_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; uint8_t v___x_5542_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v_a_5546_; lean_object* v___y_5556_; lean_object* v___y_5557_; lean_object* v_a_5558_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v_a_5563_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5572_; lean_object* v___y_5573_; lean_object* v_a_5574_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v_a_5589_; lean_object* v___y_5592_; lean_object* v___y_5593_; lean_object* v_a_5594_; lean_object* v___y_5597_; lean_object* v___y_5598_; lean_object* v___y_5599_; 
lean_inc_ref(v_expectedType_5435_);
v___f_5538_ = lean_alloc_closure((void*)(l_Lean_Meta_wrapInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5538_, 0, v_expectedType_5435_);
v_cls_5539_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5540_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_5541_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5542_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5477_, v_options_5445_, v___x_5541_);
if (v___x_5542_ == 0)
{
lean_object* v___x_5645_; uint8_t v___x_5646_; 
v___x_5645_ = l_Lean_trace_profiler;
v___x_5646_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5445_, v___x_5645_);
if (v___x_5646_ == 0)
{
lean_object* v___x_5647_; 
lean_dec_ref(v___f_5538_);
lean_inc_ref(v_expectedType_5435_);
v___x_5647_ = l_Lean_Meta_isClass_x3f(v_expectedType_5435_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5647_) == 0)
{
lean_object* v_a_5648_; lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5704_; 
v_a_5648_ = lean_ctor_get(v___x_5647_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___x_5647_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5650_ = v___x_5647_;
v_isShared_5651_ = v_isSharedCheck_5704_;
goto v_resetjp_5649_;
}
else
{
lean_inc(v_a_5648_);
lean_dec(v___x_5647_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5704_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
if (lean_obj_tag(v_a_5648_) == 1)
{
lean_object* v_val_5652_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5657_; 
lean_del_object(v___x_5650_);
v_val_5652_ = lean_ctor_get(v_a_5648_, 0);
lean_inc(v_val_5652_);
lean_dec_ref(v_a_5648_);
if (v___x_5542_ == 0)
{
v___y_5654_ = v___x_5489_;
v___y_5655_ = v_a_5440_;
v___y_5656_ = v_a_5441_;
v___y_5657_ = v_a_5442_;
goto v___jp_5653_;
}
else
{
lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5689_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
lean_inc(v_val_5652_);
v___x_5690_ = l_Lean_MessageData_ofName(v_val_5652_);
v___x_5691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5689_);
lean_ctor_set(v___x_5691_, 1, v___x_5690_);
v___x_5692_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5539_, v___x_5691_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5692_) == 0)
{
lean_dec_ref(v___x_5692_);
v___y_5654_ = v___x_5489_;
v___y_5655_ = v_a_5440_;
v___y_5656_ = v_a_5441_;
v___y_5657_ = v_a_5442_;
goto v___jp_5653_;
}
else
{
lean_object* v_a_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5700_; 
lean_dec(v_val_5652_);
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5695_ = v___x_5692_;
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_a_5693_);
lean_dec(v___x_5692_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5698_; 
if (v_isShared_5696_ == 0)
{
v___x_5698_ = v___x_5695_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_a_5693_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
return v___x_5698_;
}
}
}
}
v___jp_5653_:
{
lean_object* v___x_5658_; 
lean_inc_ref(v_expectedType_5435_);
v___x_5658_ = l_Lean_Meta_isProp(v_expectedType_5435_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5680_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5661_ = v___x_5658_;
v_isShared_5662_ = v_isSharedCheck_5680_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5658_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5680_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
uint8_t v___x_5663_; 
v___x_5663_ = lean_unbox(v_a_5659_);
lean_dec(v_a_5659_);
if (v___x_5663_ == 0)
{
lean_object* v___x_5664_; 
lean_del_object(v___x_5661_);
lean_inc(v___y_5657_);
lean_inc_ref(v___y_5656_);
lean_inc(v___y_5655_);
lean_inc_ref(v___y_5654_);
lean_inc_ref(v_inst_5434_);
v___x_5664_ = lean_whnf(v_inst_5434_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_object* v_a_5665_; lean_object* v_dummy_5666_; lean_object* v_nargs_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; 
v_a_5665_ = lean_ctor_get(v___x_5664_, 0);
lean_inc(v_a_5665_);
lean_dec_ref(v___x_5664_);
v_dummy_5666_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5667_ = l_Lean_Expr_getAppNumArgs(v_a_5665_);
lean_inc(v_nargs_5667_);
v___x_5668_ = lean_mk_array(v_nargs_5667_, v_dummy_5666_);
v___x_5669_ = lean_unsigned_to_nat(1u);
v___x_5670_ = lean_nat_sub(v_nargs_5667_, v___x_5669_);
lean_dec(v_nargs_5667_);
v___x_5671_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_5434_, v_expectedType_5435_, v___x_5646_, v_hasTrace_5478_, v_compile_5436_, v_logCompileErrors_5437_, v_isMeta_5438_, v_val_5652_, v_a_5665_, v___x_5668_, v___x_5670_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
lean_dec_ref(v___y_5654_);
lean_dec(v___x_5670_);
return v___x_5671_;
}
else
{
lean_dec_ref(v___y_5654_);
lean_dec(v_val_5652_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
return v___x_5664_;
}
}
else
{
lean_object* v_options_5672_; lean_object* v___x_5673_; uint8_t v___x_5674_; 
lean_dec(v_val_5652_);
v_options_5672_ = lean_ctor_get(v___y_5656_, 2);
v___x_5673_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5674_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5672_, v___x_5673_);
if (v___x_5674_ == 0)
{
lean_object* v___x_5676_; 
lean_dec_ref(v___y_5654_);
lean_dec_ref(v_expectedType_5435_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 0, v_inst_5434_);
v___x_5676_ = v___x_5661_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_inst_5434_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
}
}
else
{
lean_object* v___x_5678_; lean_object* v___x_5679_; 
lean_del_object(v___x_5661_);
v___x_5678_ = lean_box(0);
v___x_5679_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5435_, v_inst_5434_, v_hasTrace_5478_, v___x_5678_, v_hasTrace_5478_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
lean_dec_ref(v___y_5654_);
return v___x_5679_;
}
}
}
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
lean_dec_ref(v___y_5654_);
lean_dec(v_val_5652_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5681_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5658_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5658_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
else
{
lean_object* v___x_5702_; 
lean_dec(v_a_5648_);
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
if (v_isShared_5651_ == 0)
{
lean_ctor_set(v___x_5650_, 0, v_inst_5434_);
v___x_5702_ = v___x_5650_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_inst_5434_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
else
{
lean_object* v_a_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5712_; 
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5705_ = lean_ctor_get(v___x_5647_, 0);
v_isSharedCheck_5712_ = !lean_is_exclusive(v___x_5647_);
if (v_isSharedCheck_5712_ == 0)
{
v___x_5707_ = v___x_5647_;
v_isShared_5708_ = v_isSharedCheck_5712_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_a_5705_);
lean_dec(v___x_5647_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5712_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
lean_object* v___x_5710_; 
if (v_isShared_5708_ == 0)
{
v___x_5710_ = v___x_5707_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v_a_5705_);
v___x_5710_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
return v___x_5710_;
}
}
}
}
else
{
goto v___jp_5602_;
}
}
else
{
goto v___jp_5602_;
}
v___jp_5543_:
{
lean_object* v___x_5547_; double v___x_5548_; double v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5547_ = lean_io_get_num_heartbeats();
v___x_5548_ = lean_float_of_nat(v___y_5544_);
v___x_5549_ = lean_float_of_nat(v___x_5547_);
v___x_5550_ = lean_box_float(v___x_5548_);
v___x_5551_ = lean_box_float(v___x_5549_);
v___x_5552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5552_, 0, v___x_5550_);
lean_ctor_set(v___x_5552_, 1, v___x_5551_);
v___x_5553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5553_, 0, v_a_5546_);
lean_ctor_set(v___x_5553_, 1, v___x_5552_);
v___x_5554_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(v_cls_5539_, v_hasTrace_5478_, v___x_5540_, v_options_5445_, v___x_5542_, v___y_5545_, v___f_5538_, v___x_5553_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
lean_dec_ref(v___x_5489_);
return v___x_5554_;
}
v___jp_5555_:
{
lean_object* v___x_5559_; 
v___x_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5559_, 0, v_a_5558_);
v___y_5544_ = v___y_5556_;
v___y_5545_ = v___y_5557_;
v_a_5546_ = v___x_5559_;
goto v___jp_5543_;
}
v___jp_5560_:
{
lean_object* v___x_5564_; 
v___x_5564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5564_, 0, v_a_5563_);
v___y_5544_ = v___y_5561_;
v___y_5545_ = v___y_5562_;
v_a_5546_ = v___x_5564_;
goto v___jp_5543_;
}
v___jp_5565_:
{
if (lean_obj_tag(v___y_5568_) == 0)
{
lean_object* v_a_5569_; 
v_a_5569_ = lean_ctor_get(v___y_5568_, 0);
lean_inc(v_a_5569_);
lean_dec_ref(v___y_5568_);
v___y_5556_ = v___y_5566_;
v___y_5557_ = v___y_5567_;
v_a_5558_ = v_a_5569_;
goto v___jp_5555_;
}
else
{
lean_object* v_a_5570_; 
v_a_5570_ = lean_ctor_get(v___y_5568_, 0);
lean_inc(v_a_5570_);
lean_dec_ref(v___y_5568_);
v___y_5561_ = v___y_5566_;
v___y_5562_ = v___y_5567_;
v_a_5563_ = v_a_5570_;
goto v___jp_5560_;
}
}
v___jp_5571_:
{
lean_object* v___x_5575_; double v___x_5576_; double v___x_5577_; double v___x_5578_; double v___x_5579_; double v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___x_5575_ = lean_io_mono_nanos_now();
v___x_5576_ = lean_float_of_nat(v___y_5572_);
v___x_5577_ = lean_float_once(&l_Lean_Meta_wrapInstance___closed__1, &l_Lean_Meta_wrapInstance___closed__1_once, _init_l_Lean_Meta_wrapInstance___closed__1);
v___x_5578_ = lean_float_div(v___x_5576_, v___x_5577_);
v___x_5579_ = lean_float_of_nat(v___x_5575_);
v___x_5580_ = lean_float_div(v___x_5579_, v___x_5577_);
v___x_5581_ = lean_box_float(v___x_5578_);
v___x_5582_ = lean_box_float(v___x_5580_);
v___x_5583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5583_, 0, v___x_5581_);
lean_ctor_set(v___x_5583_, 1, v___x_5582_);
v___x_5584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5584_, 0, v_a_5574_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(v_cls_5539_, v_hasTrace_5478_, v___x_5540_, v_options_5445_, v___x_5542_, v___y_5573_, v___f_5538_, v___x_5584_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
lean_dec_ref(v___x_5489_);
return v___x_5585_;
}
v___jp_5586_:
{
lean_object* v___x_5590_; 
v___x_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5590_, 0, v_a_5589_);
v___y_5572_ = v___y_5587_;
v___y_5573_ = v___y_5588_;
v_a_5574_ = v___x_5590_;
goto v___jp_5571_;
}
v___jp_5591_:
{
lean_object* v___x_5595_; 
v___x_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5595_, 0, v_a_5594_);
v___y_5572_ = v___y_5592_;
v___y_5573_ = v___y_5593_;
v_a_5574_ = v___x_5595_;
goto v___jp_5571_;
}
v___jp_5596_:
{
if (lean_obj_tag(v___y_5599_) == 0)
{
lean_object* v_a_5600_; 
v_a_5600_ = lean_ctor_get(v___y_5599_, 0);
lean_inc(v_a_5600_);
lean_dec_ref(v___y_5599_);
v___y_5592_ = v___y_5597_;
v___y_5593_ = v___y_5598_;
v_a_5594_ = v_a_5600_;
goto v___jp_5591_;
}
else
{
lean_object* v_a_5601_; 
v_a_5601_ = lean_ctor_get(v___y_5599_, 0);
lean_inc(v_a_5601_);
lean_dec_ref(v___y_5599_);
v___y_5587_ = v___y_5597_;
v___y_5588_ = v___y_5598_;
v_a_5589_ = v_a_5601_;
goto v___jp_5586_;
}
}
v___jp_5602_:
{
lean_object* v___x_5603_; 
v___x_5603_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_a_5442_);
if (lean_obj_tag(v___x_5603_) == 0)
{
lean_object* v_a_5604_; lean_object* v___x_5605_; uint8_t v___x_5606_; 
v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
lean_inc(v_a_5604_);
lean_dec_ref(v___x_5603_);
v___x_5605_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5606_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5445_, v___x_5605_);
if (v___x_5606_ == 0)
{
lean_object* v___x_5607_; lean_object* v___x_5608_; 
v___x_5607_ = lean_io_mono_nanos_now();
lean_inc_ref(v_expectedType_5435_);
v___x_5608_ = l_Lean_Meta_isClass_x3f(v_expectedType_5435_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5608_) == 0)
{
lean_object* v_a_5609_; 
v_a_5609_ = lean_ctor_get(v___x_5608_, 0);
lean_inc(v_a_5609_);
lean_dec_ref(v___x_5608_);
if (lean_obj_tag(v_a_5609_) == 1)
{
if (v___x_5542_ == 0)
{
lean_object* v_val_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; 
v_val_5610_ = lean_ctor_get(v_a_5609_, 0);
lean_inc(v_val_5610_);
lean_dec_ref(v_a_5609_);
v___x_5611_ = lean_box(0);
v___x_5612_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5435_, v_inst_5434_, v___x_5606_, v_hasTrace_5478_, v_compile_5436_, v_logCompileErrors_5437_, v_isMeta_5438_, v_val_5610_, v___x_5611_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
v___y_5597_ = v___x_5607_;
v___y_5598_ = v_a_5604_;
v___y_5599_ = v___x_5612_;
goto v___jp_5596_;
}
else
{
lean_object* v_val_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; 
v_val_5613_ = lean_ctor_get(v_a_5609_, 0);
lean_inc_n(v_val_5613_, 2);
lean_dec_ref(v_a_5609_);
v___x_5614_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5615_ = l_Lean_MessageData_ofName(v_val_5613_);
v___x_5616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5614_);
lean_ctor_set(v___x_5616_, 1, v___x_5615_);
v___x_5617_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5539_, v___x_5616_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; lean_object* v___x_5619_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
lean_inc(v_a_5618_);
lean_dec_ref(v___x_5617_);
v___x_5619_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5435_, v_inst_5434_, v___x_5606_, v_hasTrace_5478_, v_compile_5436_, v_logCompileErrors_5437_, v_isMeta_5438_, v_val_5613_, v_a_5618_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
v___y_5597_ = v___x_5607_;
v___y_5598_ = v_a_5604_;
v___y_5599_ = v___x_5619_;
goto v___jp_5596_;
}
else
{
lean_object* v_a_5620_; 
lean_dec(v_val_5613_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5620_ = lean_ctor_get(v___x_5617_, 0);
lean_inc(v_a_5620_);
lean_dec_ref(v___x_5617_);
v___y_5587_ = v___x_5607_;
v___y_5588_ = v_a_5604_;
v_a_5589_ = v_a_5620_;
goto v___jp_5586_;
}
}
}
else
{
lean_dec(v_a_5609_);
lean_dec_ref(v_expectedType_5435_);
v___y_5592_ = v___x_5607_;
v___y_5593_ = v_a_5604_;
v_a_5594_ = v_inst_5434_;
goto v___jp_5591_;
}
}
else
{
lean_object* v_a_5621_; 
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5621_ = lean_ctor_get(v___x_5608_, 0);
lean_inc(v_a_5621_);
lean_dec_ref(v___x_5608_);
v___y_5587_ = v___x_5607_;
v___y_5588_ = v_a_5604_;
v_a_5589_ = v_a_5621_;
goto v___jp_5586_;
}
}
else
{
lean_object* v___x_5622_; lean_object* v___x_5623_; 
v___x_5622_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_expectedType_5435_);
v___x_5623_ = l_Lean_Meta_isClass_x3f(v_expectedType_5435_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5623_) == 0)
{
lean_object* v_a_5624_; 
v_a_5624_ = lean_ctor_get(v___x_5623_, 0);
lean_inc(v_a_5624_);
lean_dec_ref(v___x_5623_);
if (lean_obj_tag(v_a_5624_) == 1)
{
if (v___x_5542_ == 0)
{
lean_object* v_val_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v_val_5625_ = lean_ctor_get(v_a_5624_, 0);
lean_inc(v_val_5625_);
lean_dec_ref(v_a_5624_);
v___x_5626_ = lean_box(0);
v___x_5627_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5435_, v_inst_5434_, v___x_5606_, v_compile_5436_, v_logCompileErrors_5437_, v_isMeta_5438_, v_val_5625_, v___x_5626_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
v___y_5566_ = v___x_5622_;
v___y_5567_ = v_a_5604_;
v___y_5568_ = v___x_5627_;
goto v___jp_5565_;
}
else
{
lean_object* v_val_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; 
v_val_5628_ = lean_ctor_get(v_a_5624_, 0);
lean_inc_n(v_val_5628_, 2);
lean_dec_ref(v_a_5624_);
v___x_5629_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5630_ = l_Lean_MessageData_ofName(v_val_5628_);
v___x_5631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5629_);
lean_ctor_set(v___x_5631_, 1, v___x_5630_);
v___x_5632_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5539_, v___x_5631_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5632_) == 0)
{
lean_object* v_a_5633_; lean_object* v___x_5634_; 
v_a_5633_ = lean_ctor_get(v___x_5632_, 0);
lean_inc(v_a_5633_);
lean_dec_ref(v___x_5632_);
v___x_5634_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5435_, v_inst_5434_, v___x_5606_, v_compile_5436_, v_logCompileErrors_5437_, v_isMeta_5438_, v_val_5628_, v_a_5633_, v___x_5489_, v_a_5440_, v_a_5441_, v_a_5442_);
v___y_5566_ = v___x_5622_;
v___y_5567_ = v_a_5604_;
v___y_5568_ = v___x_5634_;
goto v___jp_5565_;
}
else
{
lean_object* v_a_5635_; 
lean_dec(v_val_5628_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5635_ = lean_ctor_get(v___x_5632_, 0);
lean_inc(v_a_5635_);
lean_dec_ref(v___x_5632_);
v___y_5561_ = v___x_5622_;
v___y_5562_ = v_a_5604_;
v_a_5563_ = v_a_5635_;
goto v___jp_5560_;
}
}
}
else
{
lean_dec(v_a_5624_);
lean_dec_ref(v_expectedType_5435_);
v___y_5556_ = v___x_5622_;
v___y_5557_ = v_a_5604_;
v_a_5558_ = v_inst_5434_;
goto v___jp_5555_;
}
}
else
{
lean_object* v_a_5636_; 
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5636_ = lean_ctor_get(v___x_5623_, 0);
lean_inc(v_a_5636_);
lean_dec_ref(v___x_5623_);
v___y_5561_ = v___x_5622_;
v___y_5562_ = v_a_5604_;
v_a_5563_ = v_a_5636_;
goto v___jp_5560_;
}
}
}
else
{
lean_object* v_a_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5644_; 
lean_dec_ref(v___f_5538_);
lean_dec_ref(v___x_5489_);
lean_dec_ref(v_expectedType_5435_);
lean_dec_ref(v_inst_5434_);
v_a_5637_ = lean_ctor_get(v___x_5603_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5639_ = v___x_5603_;
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_a_5637_);
lean_dec(v___x_5603_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5640_ == 0)
{
v___x_5642_ = v___x_5639_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(lean_object* v___x_5715_, lean_object* v_a_5716_, uint8_t v_compile_5717_, uint8_t v_logCompileErrors_5718_, uint8_t v_isMeta_5719_, lean_object* v___x_5720_, lean_object* v___x_5721_, lean_object* v_____r_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
lean_object* v___x_5728_; 
v___x_5728_ = l_Lean_Meta_wrapInstance(v___x_5715_, v_a_5716_, v_compile_5717_, v_logCompileErrors_5718_, v_isMeta_5719_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
if (lean_obj_tag(v___x_5728_) == 0)
{
lean_object* v_a_5729_; lean_object* v___x_5730_; 
v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
lean_inc(v_a_5729_);
lean_dec_ref(v___x_5728_);
v___x_5730_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_5720_, v_a_5729_, v___y_5724_);
if (lean_obj_tag(v___x_5730_) == 0)
{
lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5738_; 
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5730_);
if (v_isSharedCheck_5738_ == 0)
{
lean_object* v_unused_5739_; 
v_unused_5739_ = lean_ctor_get(v___x_5730_, 0);
lean_dec(v_unused_5739_);
v___x_5732_ = v___x_5730_;
v_isShared_5733_ = v_isSharedCheck_5738_;
goto v_resetjp_5731_;
}
else
{
lean_dec(v___x_5730_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5738_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5734_; lean_object* v___x_5736_; 
v___x_5734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5721_);
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 0, v___x_5734_);
v___x_5736_ = v___x_5732_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v___x_5734_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
}
else
{
lean_object* v_a_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5747_; 
v_a_5740_ = lean_ctor_get(v___x_5730_, 0);
v_isSharedCheck_5747_ = !lean_is_exclusive(v___x_5730_);
if (v_isSharedCheck_5747_ == 0)
{
v___x_5742_ = v___x_5730_;
v_isShared_5743_ = v_isSharedCheck_5747_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_a_5740_);
lean_dec(v___x_5730_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5747_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v___x_5745_; 
if (v_isShared_5743_ == 0)
{
v___x_5745_ = v___x_5742_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_a_5740_);
v___x_5745_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
return v___x_5745_;
}
}
}
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5755_; 
lean_dec(v___x_5720_);
v_a_5748_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5750_ = v___x_5728_;
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5728_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5753_; 
if (v_isShared_5751_ == 0)
{
v___x_5753_ = v___x_5750_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4___boxed(lean_object* v___x_5756_, lean_object* v_a_5757_, lean_object* v_compile_5758_, lean_object* v_logCompileErrors_5759_, lean_object* v_isMeta_5760_, lean_object* v___x_5761_, lean_object* v___x_5762_, lean_object* v_____r_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_){
_start:
{
uint8_t v_compile_boxed_5769_; uint8_t v_logCompileErrors_boxed_5770_; uint8_t v_isMeta_boxed_5771_; lean_object* v_res_5772_; 
v_compile_boxed_5769_ = lean_unbox(v_compile_5758_);
v_logCompileErrors_boxed_5770_ = lean_unbox(v_logCompileErrors_5759_);
v_isMeta_boxed_5771_ = lean_unbox(v_isMeta_5760_);
v_res_5772_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_5756_, v_a_5757_, v_compile_boxed_5769_, v_logCompileErrors_boxed_5770_, v_isMeta_boxed_5771_, v___x_5761_, v___x_5762_, v_____r_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object* v_expectedType_5773_, lean_object* v_inst_5774_, lean_object* v___x_5775_, lean_object* v_hasTrace_5776_, lean_object* v_compile_5777_, lean_object* v_logCompileErrors_5778_, lean_object* v_isMeta_5779_, lean_object* v_val_5780_, lean_object* v_____r_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_){
_start:
{
uint8_t v___x_160429__boxed_5787_; uint8_t v_hasTrace_boxed_5788_; uint8_t v_compile_boxed_5789_; uint8_t v_logCompileErrors_boxed_5790_; uint8_t v_isMeta_boxed_5791_; lean_object* v_res_5792_; 
v___x_160429__boxed_5787_ = lean_unbox(v___x_5775_);
v_hasTrace_boxed_5788_ = lean_unbox(v_hasTrace_5776_);
v_compile_boxed_5789_ = lean_unbox(v_compile_5777_);
v_logCompileErrors_boxed_5790_ = lean_unbox(v_logCompileErrors_5778_);
v_isMeta_boxed_5791_ = lean_unbox(v_isMeta_5779_);
v_res_5792_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5773_, v_inst_5774_, v___x_160429__boxed_5787_, v_hasTrace_boxed_5788_, v_compile_boxed_5789_, v_logCompileErrors_boxed_5790_, v_isMeta_boxed_5791_, v_val_5780_, v_____r_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec(v___y_5783_);
lean_dec_ref(v___y_5782_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object* v_expectedType_5793_, lean_object* v_inst_5794_, lean_object* v___x_5795_, lean_object* v_compile_5796_, lean_object* v_logCompileErrors_5797_, lean_object* v_isMeta_5798_, lean_object* v_val_5799_, lean_object* v_____r_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_){
_start:
{
uint8_t v___x_160454__boxed_5806_; uint8_t v_compile_boxed_5807_; uint8_t v_logCompileErrors_boxed_5808_; uint8_t v_isMeta_boxed_5809_; lean_object* v_res_5810_; 
v___x_160454__boxed_5806_ = lean_unbox(v___x_5795_);
v_compile_boxed_5807_ = lean_unbox(v_compile_5796_);
v_logCompileErrors_boxed_5808_ = lean_unbox(v_logCompileErrors_5797_);
v_isMeta_boxed_5809_ = lean_unbox(v_isMeta_5798_);
v_res_5810_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5793_, v_inst_5794_, v___x_160454__boxed_5806_, v_compile_boxed_5807_, v_logCompileErrors_boxed_5808_, v_isMeta_boxed_5809_, v_val_5799_, v_____r_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_);
lean_dec(v___y_5804_);
lean_dec_ref(v___y_5803_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
return v_res_5810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___boxed(lean_object* v_inst_5811_, lean_object* v_expectedType_5812_, lean_object* v___x_5813_, lean_object* v___x_5814_, lean_object* v_compile_5815_, lean_object* v_logCompileErrors_5816_, lean_object* v_isMeta_5817_, lean_object* v_val_5818_, lean_object* v_x_5819_, lean_object* v_x_5820_, lean_object* v_x_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
uint8_t v___x_160491__boxed_5827_; uint8_t v___x_160492__boxed_5828_; uint8_t v_compile_boxed_5829_; uint8_t v_logCompileErrors_boxed_5830_; uint8_t v_isMeta_boxed_5831_; lean_object* v_res_5832_; 
v___x_160491__boxed_5827_ = lean_unbox(v___x_5813_);
v___x_160492__boxed_5828_ = lean_unbox(v___x_5814_);
v_compile_boxed_5829_ = lean_unbox(v_compile_5815_);
v_logCompileErrors_boxed_5830_ = lean_unbox(v_logCompileErrors_5816_);
v_isMeta_boxed_5831_ = lean_unbox(v_isMeta_5817_);
v_res_5832_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(v_inst_5811_, v_expectedType_5812_, v___x_160491__boxed_5827_, v___x_160492__boxed_5828_, v_compile_boxed_5829_, v_logCompileErrors_boxed_5830_, v_isMeta_boxed_5831_, v_val_5818_, v_x_5819_, v_x_5820_, v_x_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_);
lean_dec(v___y_5825_);
lean_dec_ref(v___y_5824_);
lean_dec(v___y_5823_);
lean_dec_ref(v___y_5822_);
return v_res_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25___boxed(lean_object* v_inst_5833_, lean_object* v_expectedType_5834_, lean_object* v___x_5835_, lean_object* v_compile_5836_, lean_object* v_logCompileErrors_5837_, lean_object* v_isMeta_5838_, lean_object* v_val_5839_, lean_object* v_x_5840_, lean_object* v_x_5841_, lean_object* v_x_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
uint8_t v___x_160647__boxed_5848_; uint8_t v_compile_boxed_5849_; uint8_t v_logCompileErrors_boxed_5850_; uint8_t v_isMeta_boxed_5851_; lean_object* v_res_5852_; 
v___x_160647__boxed_5848_ = lean_unbox(v___x_5835_);
v_compile_boxed_5849_ = lean_unbox(v_compile_5836_);
v_logCompileErrors_boxed_5850_ = lean_unbox(v_logCompileErrors_5837_);
v_isMeta_boxed_5851_ = lean_unbox(v_isMeta_5838_);
v_res_5852_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(v_inst_5833_, v_expectedType_5834_, v___x_160647__boxed_5848_, v_compile_boxed_5849_, v_logCompileErrors_boxed_5850_, v_isMeta_boxed_5851_, v_val_5839_, v_x_5840_, v_x_5841_, v_x_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
lean_dec(v___y_5846_);
lean_dec_ref(v___y_5845_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
return v_res_5852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object* v_inst_5853_, lean_object* v_expectedType_5854_, lean_object* v___x_5855_, lean_object* v___x_5856_, lean_object* v_compile_5857_, lean_object* v_logCompileErrors_5858_, lean_object* v_isMeta_5859_, lean_object* v_val_5860_, lean_object* v_x_5861_, lean_object* v_x_5862_, lean_object* v_x_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_){
_start:
{
uint8_t v___x_160815__boxed_5869_; uint8_t v___x_160816__boxed_5870_; uint8_t v_compile_boxed_5871_; uint8_t v_logCompileErrors_boxed_5872_; uint8_t v_isMeta_boxed_5873_; lean_object* v_res_5874_; 
v___x_160815__boxed_5869_ = lean_unbox(v___x_5855_);
v___x_160816__boxed_5870_ = lean_unbox(v___x_5856_);
v_compile_boxed_5871_ = lean_unbox(v_compile_5857_);
v_logCompileErrors_boxed_5872_ = lean_unbox(v_logCompileErrors_5858_);
v_isMeta_boxed_5873_ = lean_unbox(v_isMeta_5859_);
v_res_5874_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_5853_, v_expectedType_5854_, v___x_160815__boxed_5869_, v___x_160816__boxed_5870_, v_compile_boxed_5871_, v_logCompileErrors_boxed_5872_, v_isMeta_boxed_5873_, v_val_5860_, v_x_5861_, v_x_5862_, v_x_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec(v_x_5863_);
return v_res_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16___boxed(lean_object* v_inst_5875_, lean_object* v_expectedType_5876_, lean_object* v___x_5877_, lean_object* v_compile_5878_, lean_object* v_logCompileErrors_5879_, lean_object* v_isMeta_5880_, lean_object* v_val_5881_, lean_object* v_x_5882_, lean_object* v_x_5883_, lean_object* v_x_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_){
_start:
{
uint8_t v___x_160984__boxed_5890_; uint8_t v_compile_boxed_5891_; uint8_t v_logCompileErrors_boxed_5892_; uint8_t v_isMeta_boxed_5893_; lean_object* v_res_5894_; 
v___x_160984__boxed_5890_ = lean_unbox(v___x_5877_);
v_compile_boxed_5891_ = lean_unbox(v_compile_5878_);
v_logCompileErrors_boxed_5892_ = lean_unbox(v_logCompileErrors_5879_);
v_isMeta_boxed_5893_ = lean_unbox(v_isMeta_5880_);
v_res_5894_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(v_inst_5875_, v_expectedType_5876_, v___x_160984__boxed_5890_, v_compile_boxed_5891_, v_logCompileErrors_boxed_5892_, v_isMeta_boxed_5893_, v_val_5881_, v_x_5882_, v_x_5883_, v_x_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec(v_x_5884_);
return v_res_5894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12___boxed(lean_object* v_inst_5895_, lean_object* v_expectedType_5896_, lean_object* v___x_5897_, lean_object* v_compile_5898_, lean_object* v_logCompileErrors_5899_, lean_object* v_isMeta_5900_, lean_object* v_val_5901_, lean_object* v_x_5902_, lean_object* v_x_5903_, lean_object* v_x_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_){
_start:
{
uint8_t v___x_161152__boxed_5910_; uint8_t v_compile_boxed_5911_; uint8_t v_logCompileErrors_boxed_5912_; uint8_t v_isMeta_boxed_5913_; lean_object* v_res_5914_; 
v___x_161152__boxed_5910_ = lean_unbox(v___x_5897_);
v_compile_boxed_5911_ = lean_unbox(v_compile_5898_);
v_logCompileErrors_boxed_5912_ = lean_unbox(v_logCompileErrors_5899_);
v_isMeta_boxed_5913_ = lean_unbox(v_isMeta_5900_);
v_res_5914_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(v_inst_5895_, v_expectedType_5896_, v___x_161152__boxed_5910_, v_compile_boxed_5911_, v_logCompileErrors_boxed_5912_, v_isMeta_boxed_5913_, v_val_5901_, v_x_5902_, v_x_5903_, v_x_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
lean_dec(v___y_5908_);
lean_dec_ref(v___y_5907_);
lean_dec(v___y_5906_);
lean_dec_ref(v___y_5905_);
return v_res_5914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object* v_inst_5915_, lean_object* v_expectedType_5916_, lean_object* v___x_5917_, lean_object* v_compile_5918_, lean_object* v_logCompileErrors_5919_, lean_object* v_isMeta_5920_, lean_object* v_val_5921_, lean_object* v_x_5922_, lean_object* v_x_5923_, lean_object* v_x_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_){
_start:
{
uint8_t v___x_161321__boxed_5930_; uint8_t v_compile_boxed_5931_; uint8_t v_logCompileErrors_boxed_5932_; uint8_t v_isMeta_boxed_5933_; lean_object* v_res_5934_; 
v___x_161321__boxed_5930_ = lean_unbox(v___x_5917_);
v_compile_boxed_5931_ = lean_unbox(v_compile_5918_);
v_logCompileErrors_boxed_5932_ = lean_unbox(v_logCompileErrors_5919_);
v_isMeta_boxed_5933_ = lean_unbox(v_isMeta_5920_);
v_res_5934_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(v_inst_5915_, v_expectedType_5916_, v___x_161321__boxed_5930_, v_compile_boxed_5931_, v_logCompileErrors_boxed_5932_, v_isMeta_boxed_5933_, v_val_5921_, v_x_5922_, v_x_5923_, v_x_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_);
lean_dec(v___y_5928_);
lean_dec_ref(v___y_5927_);
lean_dec(v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec(v_x_5924_);
return v_res_5934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5935_ = _args[0];
lean_object* v_fst_5936_ = _args[1];
lean_object* v_args_5937_ = _args[2];
lean_object* v___x_5938_ = _args[3];
lean_object* v_compile_5939_ = _args[4];
lean_object* v_logCompileErrors_5940_ = _args[5];
lean_object* v___x_5941_ = _args[6];
lean_object* v_isMeta_5942_ = _args[7];
lean_object* v_val_5943_ = _args[8];
lean_object* v_expectedType_5944_ = _args[9];
lean_object* v_a_5945_ = _args[10];
lean_object* v_b_5946_ = _args[11];
lean_object* v___y_5947_ = _args[12];
lean_object* v___y_5948_ = _args[13];
lean_object* v___y_5949_ = _args[14];
lean_object* v___y_5950_ = _args[15];
lean_object* v___y_5951_ = _args[16];
_start:
{
uint8_t v___x_161517__boxed_5952_; uint8_t v_compile_boxed_5953_; uint8_t v_logCompileErrors_boxed_5954_; uint8_t v___x_161518__boxed_5955_; uint8_t v_isMeta_boxed_5956_; lean_object* v_res_5957_; 
v___x_161517__boxed_5952_ = lean_unbox(v___x_5938_);
v_compile_boxed_5953_ = lean_unbox(v_compile_5939_);
v_logCompileErrors_boxed_5954_ = lean_unbox(v_logCompileErrors_5940_);
v___x_161518__boxed_5955_ = lean_unbox(v___x_5941_);
v_isMeta_boxed_5956_ = lean_unbox(v_isMeta_5942_);
v_res_5957_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_5935_, v_fst_5936_, v_args_5937_, v___x_161517__boxed_5952_, v_compile_boxed_5953_, v_logCompileErrors_boxed_5954_, v___x_161518__boxed_5955_, v_isMeta_boxed_5956_, v_val_5943_, v_expectedType_5944_, v_a_5945_, v_b_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
lean_dec_ref(v_args_5937_);
lean_dec_ref(v_fst_5936_);
lean_dec(v_upperBound_5935_);
return v_res_5957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___boxed(lean_object* v_upperBound_5958_, lean_object* v_fst_5959_, lean_object* v_args_5960_, lean_object* v_compile_5961_, lean_object* v_logCompileErrors_5962_, lean_object* v___x_5963_, lean_object* v_isMeta_5964_, lean_object* v_val_5965_, lean_object* v_expectedType_5966_, lean_object* v_a_5967_, lean_object* v_b_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_){
_start:
{
uint8_t v_compile_boxed_5974_; uint8_t v_logCompileErrors_boxed_5975_; uint8_t v___x_161668__boxed_5976_; uint8_t v_isMeta_boxed_5977_; lean_object* v_res_5978_; 
v_compile_boxed_5974_ = lean_unbox(v_compile_5961_);
v_logCompileErrors_boxed_5975_ = lean_unbox(v_logCompileErrors_5962_);
v___x_161668__boxed_5976_ = lean_unbox(v___x_5963_);
v_isMeta_boxed_5977_ = lean_unbox(v_isMeta_5964_);
v_res_5978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v_upperBound_5958_, v_fst_5959_, v_args_5960_, v_compile_boxed_5974_, v_logCompileErrors_boxed_5975_, v___x_161668__boxed_5976_, v_isMeta_boxed_5977_, v_val_5965_, v_expectedType_5966_, v_a_5967_, v_b_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
lean_dec(v___y_5972_);
lean_dec_ref(v___y_5971_);
lean_dec(v___y_5970_);
lean_dec_ref(v___y_5969_);
lean_dec_ref(v_args_5960_);
lean_dec_ref(v_fst_5959_);
lean_dec(v_upperBound_5958_);
return v_res_5978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5979_ = _args[0];
lean_object* v_fst_5980_ = _args[1];
lean_object* v_args_5981_ = _args[2];
lean_object* v___x_5982_ = _args[3];
lean_object* v_compile_5983_ = _args[4];
lean_object* v_logCompileErrors_5984_ = _args[5];
lean_object* v___x_5985_ = _args[6];
lean_object* v_isMeta_5986_ = _args[7];
lean_object* v_val_5987_ = _args[8];
lean_object* v_expectedType_5988_ = _args[9];
lean_object* v_a_5989_ = _args[10];
lean_object* v_b_5990_ = _args[11];
lean_object* v___y_5991_ = _args[12];
lean_object* v___y_5992_ = _args[13];
lean_object* v___y_5993_ = _args[14];
lean_object* v___y_5994_ = _args[15];
lean_object* v___y_5995_ = _args[16];
_start:
{
uint8_t v___x_161827__boxed_5996_; uint8_t v_compile_boxed_5997_; uint8_t v_logCompileErrors_boxed_5998_; uint8_t v___x_161828__boxed_5999_; uint8_t v_isMeta_boxed_6000_; lean_object* v_res_6001_; 
v___x_161827__boxed_5996_ = lean_unbox(v___x_5982_);
v_compile_boxed_5997_ = lean_unbox(v_compile_5983_);
v_logCompileErrors_boxed_5998_ = lean_unbox(v_logCompileErrors_5984_);
v___x_161828__boxed_5999_ = lean_unbox(v___x_5985_);
v_isMeta_boxed_6000_ = lean_unbox(v_isMeta_5986_);
v_res_6001_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(v_upperBound_5979_, v_fst_5980_, v_args_5981_, v___x_161827__boxed_5996_, v_compile_boxed_5997_, v_logCompileErrors_boxed_5998_, v___x_161828__boxed_5999_, v_isMeta_boxed_6000_, v_val_5987_, v_expectedType_5988_, v_a_5989_, v_b_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
lean_dec(v___y_5994_);
lean_dec_ref(v___y_5993_);
lean_dec(v___y_5992_);
lean_dec_ref(v___y_5991_);
lean_dec_ref(v_args_5981_);
lean_dec_ref(v_fst_5980_);
lean_dec(v_upperBound_5979_);
return v_res_6001_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___boxed(lean_object* v_upperBound_6002_, lean_object* v_fst_6003_, lean_object* v_args_6004_, lean_object* v___x_6005_, lean_object* v_compile_6006_, lean_object* v_logCompileErrors_6007_, lean_object* v_isMeta_6008_, lean_object* v_val_6009_, lean_object* v_expectedType_6010_, lean_object* v_a_6011_, lean_object* v_b_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_){
_start:
{
uint8_t v___x_161988__boxed_6018_; uint8_t v_compile_boxed_6019_; uint8_t v_logCompileErrors_boxed_6020_; uint8_t v_isMeta_boxed_6021_; lean_object* v_res_6022_; 
v___x_161988__boxed_6018_ = lean_unbox(v___x_6005_);
v_compile_boxed_6019_ = lean_unbox(v_compile_6006_);
v_logCompileErrors_boxed_6020_ = lean_unbox(v_logCompileErrors_6007_);
v_isMeta_boxed_6021_ = lean_unbox(v_isMeta_6008_);
v_res_6022_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v_upperBound_6002_, v_fst_6003_, v_args_6004_, v___x_161988__boxed_6018_, v_compile_boxed_6019_, v_logCompileErrors_boxed_6020_, v_isMeta_boxed_6021_, v_val_6009_, v_expectedType_6010_, v_a_6011_, v_b_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_);
lean_dec(v___y_6016_);
lean_dec_ref(v___y_6015_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
lean_dec_ref(v_args_6004_);
lean_dec_ref(v_fst_6003_);
lean_dec(v_upperBound_6002_);
return v_res_6022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object* v_inst_6023_, lean_object* v_expectedType_6024_, lean_object* v_compile_6025_, lean_object* v_logCompileErrors_6026_, lean_object* v_isMeta_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_){
_start:
{
uint8_t v_compile_boxed_6033_; uint8_t v_logCompileErrors_boxed_6034_; uint8_t v_isMeta_boxed_6035_; lean_object* v_res_6036_; 
v_compile_boxed_6033_ = lean_unbox(v_compile_6025_);
v_logCompileErrors_boxed_6034_ = lean_unbox(v_logCompileErrors_6026_);
v_isMeta_boxed_6035_ = lean_unbox(v_isMeta_6027_);
v_res_6036_ = l_Lean_Meta_wrapInstance(v_inst_6023_, v_expectedType_6024_, v_compile_boxed_6033_, v_logCompileErrors_boxed_6034_, v_isMeta_boxed_6035_, v_a_6028_, v_a_6029_, v_a_6030_, v_a_6031_);
lean_dec(v_a_6031_);
lean_dec_ref(v_a_6030_);
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6028_);
return v_res_6036_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7(lean_object* v_mvarId_6037_, lean_object* v_val_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_){
_start:
{
lean_object* v___x_6044_; 
v___x_6044_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_mvarId_6037_, v_val_6038_, v___y_6040_);
return v___x_6044_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object* v_mvarId_6045_, lean_object* v_val_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_){
_start:
{
lean_object* v_res_6052_; 
v_res_6052_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7(v_mvarId_6045_, v_val_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_);
lean_dec(v___y_6050_);
lean_dec_ref(v___y_6049_);
lean_dec(v___y_6048_);
lean_dec_ref(v___y_6047_);
return v_res_6052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8(lean_object* v_upperBound_6053_, lean_object* v_fst_6054_, lean_object* v_args_6055_, uint8_t v_compile_6056_, uint8_t v_logCompileErrors_6057_, uint8_t v___x_6058_, uint8_t v_isMeta_6059_, lean_object* v_val_6060_, lean_object* v_expectedType_6061_, lean_object* v_inst_6062_, lean_object* v_R_6063_, lean_object* v_a_6064_, lean_object* v_b_6065_, lean_object* v_c_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_){
_start:
{
lean_object* v___x_6072_; 
v___x_6072_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v_upperBound_6053_, v_fst_6054_, v_args_6055_, v_compile_6056_, v_logCompileErrors_6057_, v___x_6058_, v_isMeta_6059_, v_val_6060_, v_expectedType_6061_, v_a_6064_, v_b_6065_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_6073_ = _args[0];
lean_object* v_fst_6074_ = _args[1];
lean_object* v_args_6075_ = _args[2];
lean_object* v_compile_6076_ = _args[3];
lean_object* v_logCompileErrors_6077_ = _args[4];
lean_object* v___x_6078_ = _args[5];
lean_object* v_isMeta_6079_ = _args[6];
lean_object* v_val_6080_ = _args[7];
lean_object* v_expectedType_6081_ = _args[8];
lean_object* v_inst_6082_ = _args[9];
lean_object* v_R_6083_ = _args[10];
lean_object* v_a_6084_ = _args[11];
lean_object* v_b_6085_ = _args[12];
lean_object* v_c_6086_ = _args[13];
lean_object* v___y_6087_ = _args[14];
lean_object* v___y_6088_ = _args[15];
lean_object* v___y_6089_ = _args[16];
lean_object* v___y_6090_ = _args[17];
lean_object* v___y_6091_ = _args[18];
_start:
{
uint8_t v_compile_boxed_6092_; uint8_t v_logCompileErrors_boxed_6093_; uint8_t v___x_166482__boxed_6094_; uint8_t v_isMeta_boxed_6095_; lean_object* v_res_6096_; 
v_compile_boxed_6092_ = lean_unbox(v_compile_6076_);
v_logCompileErrors_boxed_6093_ = lean_unbox(v_logCompileErrors_6077_);
v___x_166482__boxed_6094_ = lean_unbox(v___x_6078_);
v_isMeta_boxed_6095_ = lean_unbox(v_isMeta_6079_);
v_res_6096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8(v_upperBound_6073_, v_fst_6074_, v_args_6075_, v_compile_boxed_6092_, v_logCompileErrors_boxed_6093_, v___x_166482__boxed_6094_, v_isMeta_boxed_6095_, v_val_6080_, v_expectedType_6081_, v_inst_6082_, v_R_6083_, v_a_6084_, v_b_6085_, v_c_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
lean_dec_ref(v_args_6075_);
lean_dec_ref(v_fst_6074_);
lean_dec(v_upperBound_6073_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17(lean_object* v_00_u03b1_6097_, lean_object* v_x_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_){
_start:
{
lean_object* v___x_6104_; 
v___x_6104_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_x_6098_);
return v___x_6104_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___boxed(lean_object* v_00_u03b1_6105_, lean_object* v_x_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_){
_start:
{
lean_object* v_res_6112_; 
v_res_6112_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17(v_00_u03b1_6105_, v_x_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_);
lean_dec(v___y_6110_);
lean_dec_ref(v___y_6109_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
return v_res_6112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object* v_upperBound_6113_, lean_object* v_fst_6114_, lean_object* v_args_6115_, uint8_t v___x_6116_, uint8_t v_compile_6117_, uint8_t v_logCompileErrors_6118_, uint8_t v___x_6119_, uint8_t v_isMeta_6120_, lean_object* v_val_6121_, lean_object* v_expectedType_6122_, lean_object* v_inst_6123_, lean_object* v_R_6124_, lean_object* v_a_6125_, lean_object* v_b_6126_, lean_object* v_c_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_){
_start:
{
lean_object* v___x_6133_; 
v___x_6133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_6113_, v_fst_6114_, v_args_6115_, v___x_6116_, v_compile_6117_, v_logCompileErrors_6118_, v___x_6119_, v_isMeta_6120_, v_val_6121_, v_expectedType_6122_, v_a_6125_, v_b_6126_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_);
return v___x_6133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object** _args){
lean_object* v_upperBound_6134_ = _args[0];
lean_object* v_fst_6135_ = _args[1];
lean_object* v_args_6136_ = _args[2];
lean_object* v___x_6137_ = _args[3];
lean_object* v_compile_6138_ = _args[4];
lean_object* v_logCompileErrors_6139_ = _args[5];
lean_object* v___x_6140_ = _args[6];
lean_object* v_isMeta_6141_ = _args[7];
lean_object* v_val_6142_ = _args[8];
lean_object* v_expectedType_6143_ = _args[9];
lean_object* v_inst_6144_ = _args[10];
lean_object* v_R_6145_ = _args[11];
lean_object* v_a_6146_ = _args[12];
lean_object* v_b_6147_ = _args[13];
lean_object* v_c_6148_ = _args[14];
lean_object* v___y_6149_ = _args[15];
lean_object* v___y_6150_ = _args[16];
lean_object* v___y_6151_ = _args[17];
lean_object* v___y_6152_ = _args[18];
lean_object* v___y_6153_ = _args[19];
_start:
{
uint8_t v___x_166534__boxed_6154_; uint8_t v_compile_boxed_6155_; uint8_t v_logCompileErrors_boxed_6156_; uint8_t v___x_166535__boxed_6157_; uint8_t v_isMeta_boxed_6158_; lean_object* v_res_6159_; 
v___x_166534__boxed_6154_ = lean_unbox(v___x_6137_);
v_compile_boxed_6155_ = lean_unbox(v_compile_6138_);
v_logCompileErrors_boxed_6156_ = lean_unbox(v_logCompileErrors_6139_);
v___x_166535__boxed_6157_ = lean_unbox(v___x_6140_);
v_isMeta_boxed_6158_ = lean_unbox(v_isMeta_6141_);
v_res_6159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(v_upperBound_6134_, v_fst_6135_, v_args_6136_, v___x_166534__boxed_6154_, v_compile_boxed_6155_, v_logCompileErrors_boxed_6156_, v___x_166535__boxed_6157_, v_isMeta_boxed_6158_, v_val_6142_, v_expectedType_6143_, v_inst_6144_, v_R_6145_, v_a_6146_, v_b_6147_, v_c_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
lean_dec(v___y_6152_);
lean_dec_ref(v___y_6151_);
lean_dec(v___y_6150_);
lean_dec_ref(v___y_6149_);
lean_dec_ref(v_args_6136_);
lean_dec_ref(v_fst_6135_);
lean_dec(v_upperBound_6134_);
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15(lean_object* v_upperBound_6160_, lean_object* v_fst_6161_, lean_object* v_args_6162_, uint8_t v___x_6163_, uint8_t v_compile_6164_, uint8_t v_logCompileErrors_6165_, uint8_t v_isMeta_6166_, lean_object* v_val_6167_, lean_object* v_expectedType_6168_, lean_object* v_inst_6169_, lean_object* v_R_6170_, lean_object* v_a_6171_, lean_object* v_b_6172_, lean_object* v_c_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v_upperBound_6160_, v_fst_6161_, v_args_6162_, v___x_6163_, v_compile_6164_, v_logCompileErrors_6165_, v_isMeta_6166_, v_val_6167_, v_expectedType_6168_, v_a_6171_, v_b_6172_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object** _args){
lean_object* v_upperBound_6180_ = _args[0];
lean_object* v_fst_6181_ = _args[1];
lean_object* v_args_6182_ = _args[2];
lean_object* v___x_6183_ = _args[3];
lean_object* v_compile_6184_ = _args[4];
lean_object* v_logCompileErrors_6185_ = _args[5];
lean_object* v_isMeta_6186_ = _args[6];
lean_object* v_val_6187_ = _args[7];
lean_object* v_expectedType_6188_ = _args[8];
lean_object* v_inst_6189_ = _args[9];
lean_object* v_R_6190_ = _args[10];
lean_object* v_a_6191_ = _args[11];
lean_object* v_b_6192_ = _args[12];
lean_object* v_c_6193_ = _args[13];
lean_object* v___y_6194_ = _args[14];
lean_object* v___y_6195_ = _args[15];
lean_object* v___y_6196_ = _args[16];
lean_object* v___y_6197_ = _args[17];
lean_object* v___y_6198_ = _args[18];
_start:
{
uint8_t v___x_166569__boxed_6199_; uint8_t v_compile_boxed_6200_; uint8_t v_logCompileErrors_boxed_6201_; uint8_t v_isMeta_boxed_6202_; lean_object* v_res_6203_; 
v___x_166569__boxed_6199_ = lean_unbox(v___x_6183_);
v_compile_boxed_6200_ = lean_unbox(v_compile_6184_);
v_logCompileErrors_boxed_6201_ = lean_unbox(v_logCompileErrors_6185_);
v_isMeta_boxed_6202_ = lean_unbox(v_isMeta_6186_);
v_res_6203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15(v_upperBound_6180_, v_fst_6181_, v_args_6182_, v___x_166569__boxed_6199_, v_compile_boxed_6200_, v_logCompileErrors_boxed_6201_, v_isMeta_boxed_6202_, v_val_6187_, v_expectedType_6188_, v_inst_6189_, v_R_6190_, v_a_6191_, v_b_6192_, v_c_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_);
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec_ref(v_args_6182_);
lean_dec_ref(v_fst_6181_);
lean_dec(v_upperBound_6180_);
return v_res_6203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(lean_object* v_00_u03b1_6204_, lean_object* v_constName_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_){
_start:
{
lean_object* v___x_6211_; 
v___x_6211_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
return v___x_6211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___boxed(lean_object* v_00_u03b1_6212_, lean_object* v_constName_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_){
_start:
{
lean_object* v_res_6219_; 
v_res_6219_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(v_00_u03b1_6212_, v_constName_6213_, v___y_6214_, v___y_6215_, v___y_6216_, v___y_6217_);
lean_dec(v___y_6217_);
lean_dec_ref(v___y_6216_);
lean_dec(v___y_6215_);
lean_dec_ref(v___y_6214_);
return v_res_6219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8(lean_object* v_00_u03b2_6220_, lean_object* v_x_6221_, lean_object* v_x_6222_, lean_object* v_x_6223_){
_start:
{
lean_object* v___x_6224_; 
v___x_6224_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(v_x_6221_, v_x_6222_, v_x_6223_);
return v___x_6224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20(lean_object* v_upperBound_6225_, lean_object* v_fst_6226_, lean_object* v_args_6227_, uint8_t v___x_6228_, uint8_t v_compile_6229_, uint8_t v_logCompileErrors_6230_, uint8_t v___x_6231_, uint8_t v_isMeta_6232_, lean_object* v_val_6233_, lean_object* v_expectedType_6234_, lean_object* v_inst_6235_, lean_object* v_R_6236_, lean_object* v_a_6237_, lean_object* v_b_6238_, lean_object* v_c_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_){
_start:
{
lean_object* v___x_6245_; 
v___x_6245_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(v_upperBound_6225_, v_fst_6226_, v_args_6227_, v___x_6228_, v_compile_6229_, v_logCompileErrors_6230_, v___x_6231_, v_isMeta_6232_, v_val_6233_, v_expectedType_6234_, v_a_6237_, v_b_6238_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_);
return v___x_6245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___boxed(lean_object** _args){
lean_object* v_upperBound_6246_ = _args[0];
lean_object* v_fst_6247_ = _args[1];
lean_object* v_args_6248_ = _args[2];
lean_object* v___x_6249_ = _args[3];
lean_object* v_compile_6250_ = _args[4];
lean_object* v_logCompileErrors_6251_ = _args[5];
lean_object* v___x_6252_ = _args[6];
lean_object* v_isMeta_6253_ = _args[7];
lean_object* v_val_6254_ = _args[8];
lean_object* v_expectedType_6255_ = _args[9];
lean_object* v_inst_6256_ = _args[10];
lean_object* v_R_6257_ = _args[11];
lean_object* v_a_6258_ = _args[12];
lean_object* v_b_6259_ = _args[13];
lean_object* v_c_6260_ = _args[14];
lean_object* v___y_6261_ = _args[15];
lean_object* v___y_6262_ = _args[16];
lean_object* v___y_6263_ = _args[17];
lean_object* v___y_6264_ = _args[18];
lean_object* v___y_6265_ = _args[19];
_start:
{
uint8_t v___x_166626__boxed_6266_; uint8_t v_compile_boxed_6267_; uint8_t v_logCompileErrors_boxed_6268_; uint8_t v___x_166627__boxed_6269_; uint8_t v_isMeta_boxed_6270_; lean_object* v_res_6271_; 
v___x_166626__boxed_6266_ = lean_unbox(v___x_6249_);
v_compile_boxed_6267_ = lean_unbox(v_compile_6250_);
v_logCompileErrors_boxed_6268_ = lean_unbox(v_logCompileErrors_6251_);
v___x_166627__boxed_6269_ = lean_unbox(v___x_6252_);
v_isMeta_boxed_6270_ = lean_unbox(v_isMeta_6253_);
v_res_6271_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20(v_upperBound_6246_, v_fst_6247_, v_args_6248_, v___x_166626__boxed_6266_, v_compile_boxed_6267_, v_logCompileErrors_boxed_6268_, v___x_166627__boxed_6269_, v_isMeta_boxed_6270_, v_val_6254_, v_expectedType_6255_, v_inst_6256_, v_R_6257_, v_a_6258_, v_b_6259_, v_c_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_);
lean_dec(v___y_6264_);
lean_dec_ref(v___y_6263_);
lean_dec(v___y_6262_);
lean_dec_ref(v___y_6261_);
lean_dec_ref(v_args_6248_);
lean_dec_ref(v_fst_6247_);
lean_dec(v_upperBound_6246_);
return v_res_6271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7(lean_object* v_00_u03b1_6272_, lean_object* v_ref_6273_, lean_object* v_constName_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_){
_start:
{
lean_object* v___x_6280_; 
v___x_6280_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(v_ref_6273_, v_constName_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_);
return v___x_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___boxed(lean_object* v_00_u03b1_6281_, lean_object* v_ref_6282_, lean_object* v_constName_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7(v_00_u03b1_6281_, v_ref_6282_, v_constName_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
lean_dec(v_ref_6282_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_6290_, lean_object* v_x_6291_, size_t v_x_6292_, size_t v_x_6293_, lean_object* v_x_6294_, lean_object* v_x_6295_){
_start:
{
lean_object* v___x_6296_; 
v___x_6296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_x_6291_, v_x_6292_, v_x_6293_, v_x_6294_, v_x_6295_);
return v___x_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_6297_, lean_object* v_x_6298_, lean_object* v_x_6299_, lean_object* v_x_6300_, lean_object* v_x_6301_, lean_object* v_x_6302_){
_start:
{
size_t v_x_166677__boxed_6303_; size_t v_x_166678__boxed_6304_; lean_object* v_res_6305_; 
v_x_166677__boxed_6303_ = lean_unbox_usize(v_x_6299_);
lean_dec(v_x_6299_);
v_x_166678__boxed_6304_ = lean_unbox_usize(v_x_6300_);
lean_dec(v_x_6300_);
v_res_6305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11(v_00_u03b2_6297_, v_x_6298_, v_x_166677__boxed_6303_, v_x_166678__boxed_6304_, v_x_6301_, v_x_6302_);
return v_res_6305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21(lean_object* v_00_u03b1_6306_, lean_object* v_ref_6307_, lean_object* v_msg_6308_, lean_object* v_declHint_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_){
_start:
{
lean_object* v___x_6315_; 
v___x_6315_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(v_ref_6307_, v_msg_6308_, v_declHint_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
return v___x_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___boxed(lean_object* v_00_u03b1_6316_, lean_object* v_ref_6317_, lean_object* v_msg_6318_, lean_object* v_declHint_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_){
_start:
{
lean_object* v_res_6325_; 
v_res_6325_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21(v_00_u03b1_6316_, v_ref_6317_, v_msg_6318_, v_declHint_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
lean_dec(v___y_6323_);
lean_dec_ref(v___y_6322_);
lean_dec(v___y_6321_);
lean_dec_ref(v___y_6320_);
lean_dec(v_ref_6317_);
return v_res_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24(lean_object* v_00_u03b2_6326_, lean_object* v_n_6327_, lean_object* v_k_6328_, lean_object* v_v_6329_){
_start:
{
lean_object* v___x_6330_; 
v___x_6330_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(v_n_6327_, v_k_6328_, v_v_6329_);
return v___x_6330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25(lean_object* v_00_u03b2_6331_, size_t v_depth_6332_, lean_object* v_keys_6333_, lean_object* v_vals_6334_, lean_object* v_heq_6335_, lean_object* v_i_6336_, lean_object* v_entries_6337_){
_start:
{
lean_object* v___x_6338_; 
v___x_6338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(v_depth_6332_, v_keys_6333_, v_vals_6334_, v_i_6336_, v_entries_6337_);
return v___x_6338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___boxed(lean_object* v_00_u03b2_6339_, lean_object* v_depth_6340_, lean_object* v_keys_6341_, lean_object* v_vals_6342_, lean_object* v_heq_6343_, lean_object* v_i_6344_, lean_object* v_entries_6345_){
_start:
{
size_t v_depth_boxed_6346_; lean_object* v_res_6347_; 
v_depth_boxed_6346_ = lean_unbox_usize(v_depth_6340_);
lean_dec(v_depth_6340_);
v_res_6347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25(v_00_u03b2_6339_, v_depth_boxed_6346_, v_keys_6341_, v_vals_6342_, v_heq_6343_, v_i_6344_, v_entries_6345_);
lean_dec_ref(v_vals_6342_);
lean_dec_ref(v_keys_6341_);
return v_res_6347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31(lean_object* v_msg_6348_, lean_object* v_declHint_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_){
_start:
{
lean_object* v___x_6355_; 
v___x_6355_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(v_msg_6348_, v_declHint_6349_, v___y_6353_);
return v___x_6355_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___boxed(lean_object* v_msg_6356_, lean_object* v_declHint_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_){
_start:
{
lean_object* v_res_6363_; 
v_res_6363_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31(v_msg_6356_, v_declHint_6357_, v___y_6358_, v___y_6359_, v___y_6360_, v___y_6361_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec(v___y_6359_);
lean_dec_ref(v___y_6358_);
return v_res_6363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29(lean_object* v_00_u03b1_6364_, lean_object* v_ref_6365_, lean_object* v_msg_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_){
_start:
{
lean_object* v___x_6372_; 
v___x_6372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(v_ref_6365_, v_msg_6366_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_);
return v___x_6372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___boxed(lean_object* v_00_u03b1_6373_, lean_object* v_ref_6374_, lean_object* v_msg_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_){
_start:
{
lean_object* v_res_6381_; 
v_res_6381_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29(v_00_u03b1_6373_, v_ref_6374_, v_msg_6375_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_);
lean_dec(v___y_6379_);
lean_dec_ref(v___y_6378_);
lean_dec(v___y_6377_);
lean_dec_ref(v___y_6376_);
lean_dec(v_ref_6374_);
return v_res_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32(lean_object* v_00_u03b2_6382_, lean_object* v_x_6383_, lean_object* v_x_6384_, lean_object* v_x_6385_, lean_object* v_x_6386_){
_start:
{
lean_object* v___x_6387_; 
v___x_6387_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(v_x_6383_, v_x_6384_, v_x_6385_, v_x_6386_);
return v___x_6387_;
}
}
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_instances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_instances);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_data = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_data);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WrapInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_WrapInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_WrapInstance(builtin);
}
#ifdef __cplusplus
}
#endif
