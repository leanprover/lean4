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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_wrapInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "error when attempting to reuse existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "using projection of existing instance `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "did not find existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__2;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__14___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15_spec__18(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_wrapInstance___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "did not reduce to constructor application, returning/wrapping as is: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found inherited field `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` from parent `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "using existing instance "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof field "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " does not have expected type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " but "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = ", wrapping in auxiliary theorem: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "wrapInstance: incorrect number of arguments for constructor application `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "wrapInstance: `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not unify with the conclusion of `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_wrapInstance___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "class is "};
static const lean_object* l_Lean_Meta_wrapInstance___closed__2 = (const lean_object*)&l_Lean_Meta_wrapInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15_spec__24(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(lean_object* v_e_844_, lean_object* v___y_845_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = l_Lean_Expr_hasMVar(v_e_844_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_e_844_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v_mctx_850_; lean_object* v___x_851_; lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_854_; lean_object* v_cache_855_; lean_object* v_zetaDeltaFVarIds_856_; lean_object* v_postponed_857_; lean_object* v_diag_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_867_; 
v___x_849_ = lean_st_ref_get(v___y_845_);
v_mctx_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_mctx_850_);
lean_dec(v___x_849_);
v___x_851_ = l_Lean_instantiateMVarsCore(v_mctx_850_, v_e_844_);
v_fst_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_fst_852_);
v_snd_853_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_snd_853_);
lean_dec_ref(v___x_851_);
v___x_854_ = lean_st_ref_take(v___y_845_);
v_cache_855_ = lean_ctor_get(v___x_854_, 1);
v_zetaDeltaFVarIds_856_ = lean_ctor_get(v___x_854_, 2);
v_postponed_857_ = lean_ctor_get(v___x_854_, 3);
v_diag_858_ = lean_ctor_get(v___x_854_, 4);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v___x_854_, 0);
lean_dec(v_unused_868_);
v___x_860_ = v___x_854_;
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_diag_858_);
lean_inc(v_postponed_857_);
lean_inc(v_zetaDeltaFVarIds_856_);
lean_inc(v_cache_855_);
lean_dec(v___x_854_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v_snd_853_);
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_snd_853_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_cache_855_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_zetaDeltaFVarIds_856_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_postponed_857_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_diag_858_);
v___x_863_ = v_reuseFailAlloc_866_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_st_ref_set(v___y_845_, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_fst_852_);
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg___boxed(lean_object* v_e_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(v_e_869_, v___y_870_);
lean_dec(v___y_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4(lean_object* v_e_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(v_e_873_, v___y_875_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object* v_e_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4(v_e_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_886_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_unsigned_to_nat(32u);
v___x_888_ = lean_mk_empty_array_with_capacity(v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_890_ = ((size_t)5ULL);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_unsigned_to_nat(32u);
v___x_893_ = lean_mk_empty_array_with_capacity(v___x_892_);
v___x_894_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0);
v___x_895_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
lean_ctor_set(v___x_895_, 2, v___x_891_);
lean_ctor_set(v___x_895_, 3, v___x_891_);
lean_ctor_set_usize(v___x_895_, 4, v___x_890_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_traceState_899_; lean_object* v_traces_900_; lean_object* v___x_901_; lean_object* v_traceState_902_; lean_object* v_env_903_; lean_object* v_nextMacroScope_904_; lean_object* v_ngen_905_; lean_object* v_auxDeclNGen_906_; lean_object* v_cache_907_; lean_object* v_messages_908_; lean_object* v_infoState_909_; lean_object* v_snapshotTasks_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_929_; 
v___x_898_ = lean_st_ref_get(v___y_896_);
v_traceState_899_ = lean_ctor_get(v___x_898_, 4);
lean_inc_ref(v_traceState_899_);
lean_dec(v___x_898_);
v_traces_900_ = lean_ctor_get(v_traceState_899_, 0);
lean_inc_ref(v_traces_900_);
lean_dec_ref(v_traceState_899_);
v___x_901_ = lean_st_ref_take(v___y_896_);
v_traceState_902_ = lean_ctor_get(v___x_901_, 4);
v_env_903_ = lean_ctor_get(v___x_901_, 0);
v_nextMacroScope_904_ = lean_ctor_get(v___x_901_, 1);
v_ngen_905_ = lean_ctor_get(v___x_901_, 2);
v_auxDeclNGen_906_ = lean_ctor_get(v___x_901_, 3);
v_cache_907_ = lean_ctor_get(v___x_901_, 5);
v_messages_908_ = lean_ctor_get(v___x_901_, 6);
v_infoState_909_ = lean_ctor_get(v___x_901_, 7);
v_snapshotTasks_910_ = lean_ctor_get(v___x_901_, 8);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_929_ == 0)
{
v___x_912_ = v___x_901_;
v_isShared_913_ = v_isSharedCheck_929_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snapshotTasks_910_);
lean_inc(v_infoState_909_);
lean_inc(v_messages_908_);
lean_inc(v_cache_907_);
lean_inc(v_traceState_902_);
lean_inc(v_auxDeclNGen_906_);
lean_inc(v_ngen_905_);
lean_inc(v_nextMacroScope_904_);
lean_inc(v_env_903_);
lean_dec(v___x_901_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_929_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint64_t v_tid_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_927_; 
v_tid_914_ = lean_ctor_get_uint64(v_traceState_902_, sizeof(void*)*1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_traceState_902_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v_traceState_902_, 0);
lean_dec(v_unused_928_);
v___x_916_ = v_traceState_902_;
v_isShared_917_ = v_isSharedCheck_927_;
goto v_resetjp_915_;
}
else
{
lean_dec(v_traceState_902_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_927_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_918_);
lean_ctor_set_uint64(v_reuseFailAlloc_926_, sizeof(void*)*1, v_tid_914_);
v___x_920_ = v_reuseFailAlloc_926_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 4, v___x_920_);
v___x_922_ = v___x_912_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_env_903_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_nextMacroScope_904_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_ngen_905_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_auxDeclNGen_906_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_925_, 5, v_cache_907_);
lean_ctor_set(v_reuseFailAlloc_925_, 6, v_messages_908_);
lean_ctor_set(v_reuseFailAlloc_925_, 7, v_infoState_909_);
lean_ctor_set(v_reuseFailAlloc_925_, 8, v_snapshotTasks_910_);
v___x_922_ = v_reuseFailAlloc_925_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_st_ref_set(v___y_896_, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_traces_900_);
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___boxed(lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v___y_930_);
lean_dec(v___y_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v___y_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_944_;
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_Meta_wrapInstance___lam__0___closed__0));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object* v_expectedType_948_, lean_object* v_x_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = lean_obj_once(&l_Lean_Meta_wrapInstance___lam__0___closed__1, &l_Lean_Meta_wrapInstance___lam__0___closed__1_once, _init_l_Lean_Meta_wrapInstance___lam__0___closed__1);
v___x_956_ = l_Lean_MessageData_ofExpr(v_expectedType_948_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object* v_expectedType_959_, lean_object* v_x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Meta_wrapInstance___lam__0(v_expectedType_959_, v_x_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec_ref(v_x_960_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(lean_object* v_cls_967_, lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_ref_974_; lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1020_; 
v_ref_974_ = lean_ctor_get(v___y_971_, 5);
v___x_975_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1020_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1020_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v_traceState_981_; lean_object* v_env_982_; lean_object* v_nextMacroScope_983_; lean_object* v_ngen_984_; lean_object* v_auxDeclNGen_985_; lean_object* v_cache_986_; lean_object* v_messages_987_; lean_object* v_infoState_988_; lean_object* v_snapshotTasks_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1019_; 
v___x_980_ = lean_st_ref_take(v___y_972_);
v_traceState_981_ = lean_ctor_get(v___x_980_, 4);
v_env_982_ = lean_ctor_get(v___x_980_, 0);
v_nextMacroScope_983_ = lean_ctor_get(v___x_980_, 1);
v_ngen_984_ = lean_ctor_get(v___x_980_, 2);
v_auxDeclNGen_985_ = lean_ctor_get(v___x_980_, 3);
v_cache_986_ = lean_ctor_get(v___x_980_, 5);
v_messages_987_ = lean_ctor_get(v___x_980_, 6);
v_infoState_988_ = lean_ctor_get(v___x_980_, 7);
v_snapshotTasks_989_ = lean_ctor_get(v___x_980_, 8);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_991_ = v___x_980_;
v_isShared_992_ = v_isSharedCheck_1019_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_snapshotTasks_989_);
lean_inc(v_infoState_988_);
lean_inc(v_messages_987_);
lean_inc(v_cache_986_);
lean_inc(v_traceState_981_);
lean_inc(v_auxDeclNGen_985_);
lean_inc(v_ngen_984_);
lean_inc(v_nextMacroScope_983_);
lean_inc(v_env_982_);
lean_dec(v___x_980_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1019_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
uint64_t v_tid_993_; lean_object* v_traces_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1018_; 
v_tid_993_ = lean_ctor_get_uint64(v_traceState_981_, sizeof(void*)*1);
v_traces_994_ = lean_ctor_get(v_traceState_981_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_traceState_981_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_996_ = v_traceState_981_;
v_isShared_997_ = v_isSharedCheck_1018_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_traces_994_);
lean_dec(v_traceState_981_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1018_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; double v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_998_ = lean_box(0);
v___x_999_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
v___x_1000_ = 0;
v___x_1001_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_1002_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1002_, 0, v_cls_967_);
lean_ctor_set(v___x_1002_, 1, v___x_998_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
lean_ctor_set_float(v___x_1002_, sizeof(void*)*3, v___x_999_);
lean_ctor_set_float(v___x_1002_, sizeof(void*)*3 + 8, v___x_999_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*3 + 16, v___x_1000_);
v___x_1003_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2));
v___x_1004_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v_a_976_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
lean_inc(v_ref_974_);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_ref_974_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_PersistentArray_push___redArg(v_traces_994_, v___x_1005_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1006_);
v___x_1008_ = v___x_996_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1006_);
lean_ctor_set_uint64(v_reuseFailAlloc_1017_, sizeof(void*)*1, v_tid_993_);
v___x_1008_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 4, v___x_1008_);
v___x_1010_ = v___x_991_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_env_982_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_nextMacroScope_983_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_ngen_984_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_auxDeclNGen_985_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1016_, 5, v_cache_986_);
lean_ctor_set(v_reuseFailAlloc_1016_, 6, v_messages_987_);
lean_ctor_set(v_reuseFailAlloc_1016_, 7, v_infoState_988_);
lean_ctor_set(v_reuseFailAlloc_1016_, 8, v_snapshotTasks_989_);
v___x_1010_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1011_ = lean_st_ref_set(v___y_972_, v___x_1010_);
v___x_1012_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_1012_);
v___x_1014_ = v___x_978_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object* v_cls_1021_, lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_1021_, v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___redArg(lean_object* v_ref_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_fileName_1036_; lean_object* v_fileMap_1037_; lean_object* v_options_1038_; lean_object* v_currRecDepth_1039_; lean_object* v_maxRecDepth_1040_; lean_object* v_ref_1041_; lean_object* v_currNamespace_1042_; lean_object* v_openDecls_1043_; lean_object* v_initHeartbeats_1044_; lean_object* v_maxHeartbeats_1045_; lean_object* v_quotContext_1046_; lean_object* v_currMacroScope_1047_; uint8_t v_diag_1048_; lean_object* v_cancelTk_x3f_1049_; uint8_t v_suppressElabErrors_1050_; lean_object* v_inheritedTraceOptions_1051_; lean_object* v_ref_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_fileName_1036_ = lean_ctor_get(v___y_1033_, 0);
v_fileMap_1037_ = lean_ctor_get(v___y_1033_, 1);
v_options_1038_ = lean_ctor_get(v___y_1033_, 2);
v_currRecDepth_1039_ = lean_ctor_get(v___y_1033_, 3);
v_maxRecDepth_1040_ = lean_ctor_get(v___y_1033_, 4);
v_ref_1041_ = lean_ctor_get(v___y_1033_, 5);
v_currNamespace_1042_ = lean_ctor_get(v___y_1033_, 6);
v_openDecls_1043_ = lean_ctor_get(v___y_1033_, 7);
v_initHeartbeats_1044_ = lean_ctor_get(v___y_1033_, 8);
v_maxHeartbeats_1045_ = lean_ctor_get(v___y_1033_, 9);
v_quotContext_1046_ = lean_ctor_get(v___y_1033_, 10);
v_currMacroScope_1047_ = lean_ctor_get(v___y_1033_, 11);
v_diag_1048_ = lean_ctor_get_uint8(v___y_1033_, sizeof(void*)*14);
v_cancelTk_x3f_1049_ = lean_ctor_get(v___y_1033_, 12);
v_suppressElabErrors_1050_ = lean_ctor_get_uint8(v___y_1033_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1051_ = lean_ctor_get(v___y_1033_, 13);
v_ref_1052_ = l_Lean_replaceRef(v_ref_1029_, v_ref_1041_);
lean_inc_ref(v_inheritedTraceOptions_1051_);
lean_inc(v_cancelTk_x3f_1049_);
lean_inc(v_currMacroScope_1047_);
lean_inc(v_quotContext_1046_);
lean_inc(v_maxHeartbeats_1045_);
lean_inc(v_initHeartbeats_1044_);
lean_inc(v_openDecls_1043_);
lean_inc(v_currNamespace_1042_);
lean_inc(v_maxRecDepth_1040_);
lean_inc(v_currRecDepth_1039_);
lean_inc_ref(v_options_1038_);
lean_inc_ref(v_fileMap_1037_);
lean_inc_ref(v_fileName_1036_);
v___x_1053_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1053_, 0, v_fileName_1036_);
lean_ctor_set(v___x_1053_, 1, v_fileMap_1037_);
lean_ctor_set(v___x_1053_, 2, v_options_1038_);
lean_ctor_set(v___x_1053_, 3, v_currRecDepth_1039_);
lean_ctor_set(v___x_1053_, 4, v_maxRecDepth_1040_);
lean_ctor_set(v___x_1053_, 5, v_ref_1052_);
lean_ctor_set(v___x_1053_, 6, v_currNamespace_1042_);
lean_ctor_set(v___x_1053_, 7, v_openDecls_1043_);
lean_ctor_set(v___x_1053_, 8, v_initHeartbeats_1044_);
lean_ctor_set(v___x_1053_, 9, v_maxHeartbeats_1045_);
lean_ctor_set(v___x_1053_, 10, v_quotContext_1046_);
lean_ctor_set(v___x_1053_, 11, v_currMacroScope_1047_);
lean_ctor_set(v___x_1053_, 12, v_cancelTk_x3f_1049_);
lean_ctor_set(v___x_1053_, 13, v_inheritedTraceOptions_1051_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*14, v_diag_1048_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*14 + 1, v_suppressElabErrors_1050_);
v___x_1054_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_1030_, v___y_1031_, v___y_1032_, v___x_1053_, v___y_1034_);
lean_dec_ref(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___redArg___boxed(lean_object* v_ref_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___redArg(v_ref_1055_, v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v_ref_1055_);
return v_res_1062_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__0(void){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__0);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__2(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
lean_ctor_set(v___x_1068_, 2, v___x_1067_);
lean_ctor_set(v___x_1068_, 3, v___x_1067_);
lean_ctor_set(v___x_1068_, 4, v___x_1066_);
lean_ctor_set(v___x_1068_, 5, v___x_1066_);
lean_ctor_set(v___x_1068_, 6, v___x_1066_);
lean_ctor_set(v___x_1068_, 7, v___x_1066_);
lean_ctor_set(v___x_1068_, 8, v___x_1066_);
lean_ctor_set(v___x_1068_, 9, v___x_1066_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_unsigned_to_nat(32u);
v___x_1070_ = lean_mk_empty_array_with_capacity(v___x_1069_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__4(void){
_start:
{
size_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1072_ = ((size_t)5ULL);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_unsigned_to_nat(32u);
v___x_1075_ = lean_mk_empty_array_with_capacity(v___x_1074_);
v___x_1076_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__3);
v___x_1077_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
lean_ctor_set(v___x_1077_, 2, v___x_1073_);
lean_ctor_set(v___x_1077_, 3, v___x_1073_);
lean_ctor_set_usize(v___x_1077_, 4, v___x_1072_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__5(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1078_ = lean_box(1);
v___x_1079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__4);
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__1);
v___x_1081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_1079_);
lean_ctor_set(v___x_1081_, 2, v___x_1078_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__6));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__9(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__8));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__11(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__10));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__13(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__12));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__15(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__14));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__17(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__16));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__19(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__18));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg(lean_object* v_msg_1103_, lean_object* v_declHint_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v_env_1108_; uint8_t v___x_1109_; 
v___x_1107_ = lean_st_ref_get(v___y_1105_);
v_env_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_ref(v_env_1108_);
lean_dec(v___x_1107_);
v___x_1109_ = l_Lean_Name_isAnonymous(v_declHint_1104_);
if (v___x_1109_ == 0)
{
uint8_t v_isExporting_1110_; 
v_isExporting_1110_ = lean_ctor_get_uint8(v_env_1108_, sizeof(void*)*8);
if (v_isExporting_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec_ref(v_env_1108_);
lean_dec(v_declHint_1104_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_msg_1103_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
lean_inc_ref(v_env_1108_);
v___x_1112_ = l_Lean_Environment_setExporting(v_env_1108_, v___x_1109_);
lean_inc(v_declHint_1104_);
lean_inc_ref(v___x_1112_);
v___x_1113_ = l_Lean_Environment_contains(v___x_1112_, v_declHint_1104_, v_isExporting_1110_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_env_1108_);
lean_dec(v_declHint_1104_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_msg_1103_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_c_1120_; lean_object* v___x_1121_; 
v___x_1115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__2);
v___x_1116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__5);
v___x_1117_ = l_Lean_Options_empty;
v___x_1118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1112_);
lean_ctor_set(v___x_1118_, 1, v___x_1115_);
lean_ctor_set(v___x_1118_, 2, v___x_1116_);
lean_ctor_set(v___x_1118_, 3, v___x_1117_);
lean_inc(v_declHint_1104_);
v___x_1119_ = l_Lean_MessageData_ofConstName(v_declHint_1104_, v___x_1109_);
v_c_1120_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1120_, 0, v___x_1118_);
lean_ctor_set(v_c_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1108_, v_declHint_1104_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec_ref(v_env_1108_);
lean_dec(v_declHint_1104_);
v___x_1122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_c_1120_);
v___x_1124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__9);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_MessageData_note(v___x_1125_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_msg_1103_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
else
{
lean_object* v_val_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1164_; 
v_val_1129_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1131_ = v___x_1121_;
v_isShared_1132_ = v_isSharedCheck_1164_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_val_1129_);
lean_dec(v___x_1121_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1164_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_mod_1136_; uint8_t v___x_1137_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = l_Lean_Environment_header(v_env_1108_);
lean_dec_ref(v_env_1108_);
v___x_1135_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1134_);
v_mod_1136_ = lean_array_get(v___x_1133_, v___x_1135_, v_val_1129_);
lean_dec(v_val_1129_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = l_Lean_isPrivateName(v_declHint_1104_);
lean_dec(v_declHint_1104_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__11);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_c_1120_);
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__13);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_MessageData_ofName(v_mod_1136_);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__15);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_MessageData_note(v___x_1145_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_msg_1103_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1147_);
v___x_1149_ = v___x_1131_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__7);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
lean_ctor_set(v___x_1152_, 1, v_c_1120_);
v___x_1153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__17);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_MessageData_ofName(v_mod_1136_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___closed__19);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_MessageData_note(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_msg_1103_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1160_);
v___x_1162_ = v___x_1131_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1165_; 
lean_dec_ref(v_env_1108_);
lean_dec(v_declHint_1104_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_msg_1103_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg___boxed(lean_object* v_msg_1166_, lean_object* v_declHint_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg(v_msg_1166_, v_declHint_1167_, v___y_1168_);
lean_dec(v___y_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27(lean_object* v_msg_1171_, lean_object* v_declHint_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1188_; 
v___x_1178_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg(v_msg_1171_, v_declHint_1172_, v___y_1176_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1183_ = l_Lean_unknownIdentifierMessageTag;
v___x_1184_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_a_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27___boxed(lean_object* v_msg_1189_, lean_object* v_declHint_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27(v_msg_1189_, v_declHint_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___redArg(lean_object* v_ref_1197_, lean_object* v_msg_1198_, lean_object* v_declHint_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1207_; 
v___x_1205_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27(v_msg_1198_, v_declHint_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1205_);
v___x_1207_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___redArg(v_ref_1197_, v_a_1206_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___redArg___boxed(lean_object* v_ref_1208_, lean_object* v_msg_1209_, lean_object* v_declHint_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___redArg(v_ref_1208_, v_msg_1209_, v_declHint_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v_ref_1208_);
return v_res_1216_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__0));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg(lean_object* v_ref_1220_, lean_object* v_constName_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1227_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___closed__1);
v___x_1228_ = 0;
lean_inc(v_constName_1221_);
v___x_1229_ = l_Lean_MessageData_ofConstName(v_constName_1221_, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1227_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___redArg(v_ref_1220_, v___x_1232_, v_constName_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_ref_1234_, lean_object* v_constName_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg(v_ref_1234_, v_constName_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v_ref_1234_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___redArg(lean_object* v_constName_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_ref_1248_; lean_object* v___x_1249_; 
v_ref_1248_ = lean_ctor_get(v___y_1245_, 5);
v___x_1249_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg(v_ref_1248_, v_constName_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___redArg___boxed(lean_object* v_constName_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___redArg(v_constName_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(lean_object* v_constName_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; lean_object* v_env_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_st_ref_get(v___y_1261_);
v_env_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc_ref(v_env_1264_);
lean_dec(v___x_1263_);
v___x_1265_ = 0;
lean_inc(v_constName_1257_);
v___x_1266_ = l_Lean_Environment_find_x3f(v_env_1264_, v_constName_1257_, v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___redArg(v_constName_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1267_;
}
else
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_constName_1257_);
v_val_1268_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1266_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v___x_1266_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_val_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object* v_constName_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(v_constName_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23_spec__31___redArg(lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
lean_object* v_ks_1287_; lean_object* v_vs_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1312_; 
v_ks_1287_ = lean_ctor_get(v_x_1283_, 0);
v_vs_1288_ = lean_ctor_get(v_x_1283_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_x_1283_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1290_ = v_x_1283_;
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_vs_1288_);
lean_inc(v_ks_1287_);
lean_dec(v_x_1283_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_array_get_size(v_ks_1287_);
v___x_1293_ = lean_nat_dec_lt(v_x_1284_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_dec(v_x_1284_);
v___x_1294_ = lean_array_push(v_ks_1287_, v_x_1285_);
v___x_1295_ = lean_array_push(v_vs_1288_, v_x_1286_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1295_);
lean_ctor_set(v___x_1290_, 0, v___x_1294_);
v___x_1297_ = v___x_1290_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
else
{
lean_object* v_k_x27_1299_; uint8_t v___x_1300_; 
v_k_x27_1299_ = lean_array_fget_borrowed(v_ks_1287_, v_x_1284_);
v___x_1300_ = l_Lean_instBEqMVarId_beq(v_x_1285_, v_k_x27_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1302_; 
if (v_isShared_1291_ == 0)
{
v___x_1302_ = v___x_1290_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_ks_1287_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_vs_1288_);
v___x_1302_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_nat_add(v_x_1284_, v___x_1303_);
lean_dec(v_x_1284_);
v_x_1283_ = v___x_1302_;
v_x_1284_ = v___x_1304_;
goto _start;
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1307_ = lean_array_fset(v_ks_1287_, v_x_1284_, v_x_1285_);
v___x_1308_ = lean_array_fset(v_vs_1288_, v_x_1284_, v_x_1286_);
lean_dec(v_x_1284_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1308_);
lean_ctor_set(v___x_1290_, 0, v___x_1307_);
v___x_1310_ = v___x_1290_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23___redArg(lean_object* v_n_1313_, lean_object* v_k_1314_, lean_object* v_v_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23_spec__31___redArg(v_n_1313_, v___x_1316_, v_k_1314_, v_v_1315_);
return v___x_1317_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__0(void){
_start:
{
size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; 
v___x_1318_ = ((size_t)5ULL);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_shift_left(v___x_1319_, v___x_1318_);
return v___x_1320_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; 
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__0);
v___x_1323_ = lean_usize_sub(v___x_1322_, v___x_1321_);
return v___x_1323_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg(lean_object* v_x_1325_, size_t v_x_1326_, size_t v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
if (lean_obj_tag(v_x_1325_) == 0)
{
lean_object* v_es_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; lean_object* v_j_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_es_1330_ = lean_ctor_get(v_x_1325_, 0);
v___x_1331_ = ((size_t)5ULL);
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__1);
v___x_1334_ = lean_usize_land(v_x_1326_, v___x_1333_);
v_j_1335_ = lean_usize_to_nat(v___x_1334_);
v___x_1336_ = lean_array_get_size(v_es_1330_);
v___x_1337_ = lean_nat_dec_lt(v_j_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec(v_j_1335_);
lean_dec(v_x_1329_);
lean_dec(v_x_1328_);
return v_x_1325_;
}
else
{
lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1374_; 
lean_inc_ref(v_es_1330_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_x_1325_, 0);
lean_dec(v_unused_1375_);
v___x_1339_ = v_x_1325_;
v_isShared_1340_ = v_isSharedCheck_1374_;
goto v_resetjp_1338_;
}
else
{
lean_dec(v_x_1325_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1374_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_v_1341_; lean_object* v___x_1342_; lean_object* v_xs_x27_1343_; lean_object* v___y_1345_; 
v_v_1341_ = lean_array_fget(v_es_1330_, v_j_1335_);
v___x_1342_ = lean_box(0);
v_xs_x27_1343_ = lean_array_fset(v_es_1330_, v_j_1335_, v___x_1342_);
switch(lean_obj_tag(v_v_1341_))
{
case 0:
{
lean_object* v_key_1350_; lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1361_; 
v_key_1350_ = lean_ctor_get(v_v_1341_, 0);
v_val_1351_ = lean_ctor_get(v_v_1341_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_v_1341_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1353_ = v_v_1341_;
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_inc(v_key_1350_);
lean_dec(v_v_1341_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Lean_instBEqMVarId_beq(v_x_1328_, v_key_1350_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_del_object(v___x_1353_);
v___x_1356_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1350_, v_val_1351_, v_x_1328_, v_x_1329_);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
v___y_1345_ = v___x_1357_;
goto v___jp_1344_;
}
else
{
lean_object* v___x_1359_; 
lean_dec(v_val_1351_);
lean_dec(v_key_1350_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v_x_1329_);
lean_ctor_set(v___x_1353_, 0, v_x_1328_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_x_1328_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_x_1329_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
v___y_1345_ = v___x_1359_;
goto v___jp_1344_;
}
}
}
}
case 1:
{
lean_object* v_node_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1372_; 
v_node_1362_ = lean_ctor_get(v_v_1341_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_v_1341_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1364_ = v_v_1341_;
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_node_1362_);
lean_dec(v_v_1341_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1366_ = lean_usize_shift_right(v_x_1326_, v___x_1331_);
v___x_1367_ = lean_usize_add(v_x_1327_, v___x_1332_);
v___x_1368_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg(v_node_1362_, v___x_1366_, v___x_1367_, v_x_1328_, v_x_1329_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1368_);
v___x_1370_ = v___x_1364_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
v___y_1345_ = v___x_1370_;
goto v___jp_1344_;
}
}
}
default: 
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_x_1328_);
lean_ctor_set(v___x_1373_, 1, v_x_1329_);
v___y_1345_ = v___x_1373_;
goto v___jp_1344_;
}
}
v___jp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_array_fset(v_xs_x27_1343_, v_j_1335_, v___y_1345_);
lean_dec(v_j_1335_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1346_);
v___x_1348_ = v___x_1339_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
else
{
lean_object* v_ks_1376_; lean_object* v_vs_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1397_; 
v_ks_1376_ = lean_ctor_get(v_x_1325_, 0);
v_vs_1377_ = lean_ctor_get(v_x_1325_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1379_ = v_x_1325_;
v_isShared_1380_ = v_isSharedCheck_1397_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_vs_1377_);
lean_inc(v_ks_1376_);
lean_dec(v_x_1325_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1397_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_ks_1376_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_vs_1377_);
v___x_1382_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v_newNode_1383_; uint8_t v___y_1385_; size_t v___x_1391_; uint8_t v___x_1392_; 
v_newNode_1383_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23___redArg(v___x_1382_, v_x_1328_, v_x_1329_);
v___x_1391_ = ((size_t)7ULL);
v___x_1392_ = lean_usize_dec_le(v___x_1391_, v_x_1327_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1383_);
v___x_1394_ = lean_unsigned_to_nat(4u);
v___x_1395_ = lean_nat_dec_lt(v___x_1393_, v___x_1394_);
lean_dec(v___x_1393_);
v___y_1385_ = v___x_1395_;
goto v___jp_1384_;
}
else
{
v___y_1385_ = v___x_1392_;
goto v___jp_1384_;
}
v___jp_1384_:
{
if (v___y_1385_ == 0)
{
lean_object* v_ks_1386_; lean_object* v_vs_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_ks_1386_ = lean_ctor_get(v_newNode_1383_, 0);
lean_inc_ref(v_ks_1386_);
v_vs_1387_ = lean_ctor_get(v_newNode_1383_, 1);
lean_inc_ref(v_vs_1387_);
lean_dec_ref(v_newNode_1383_);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___closed__2);
v___x_1390_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___redArg(v_x_1327_, v_ks_1386_, v_vs_1387_, v___x_1388_, v___x_1389_);
lean_dec_ref(v_vs_1387_);
lean_dec_ref(v_ks_1386_);
return v___x_1390_;
}
else
{
return v_newNode_1383_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___redArg(size_t v_depth_1398_, lean_object* v_keys_1399_, lean_object* v_vals_1400_, lean_object* v_i_1401_, lean_object* v_entries_1402_){
_start:
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_array_get_size(v_keys_1399_);
v___x_1404_ = lean_nat_dec_lt(v_i_1401_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_dec(v_i_1401_);
return v_entries_1402_;
}
else
{
lean_object* v_k_1405_; lean_object* v_v_1406_; uint64_t v___x_1407_; size_t v_h_1408_; size_t v___x_1409_; lean_object* v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; size_t v_h_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_k_1405_ = lean_array_fget_borrowed(v_keys_1399_, v_i_1401_);
v_v_1406_ = lean_array_fget_borrowed(v_vals_1400_, v_i_1401_);
v___x_1407_ = l_Lean_instHashableMVarId_hash(v_k_1405_);
v_h_1408_ = lean_uint64_to_usize(v___x_1407_);
v___x_1409_ = ((size_t)5ULL);
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_sub(v_depth_1398_, v___x_1411_);
v___x_1413_ = lean_usize_mul(v___x_1409_, v___x_1412_);
v_h_1414_ = lean_usize_shift_right(v_h_1408_, v___x_1413_);
v___x_1415_ = lean_nat_add(v_i_1401_, v___x_1410_);
lean_dec(v_i_1401_);
lean_inc(v_v_1406_);
lean_inc(v_k_1405_);
v___x_1416_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg(v_entries_1402_, v_h_1414_, v_depth_1398_, v_k_1405_, v_v_1406_);
v_i_1401_ = v___x_1415_;
v_entries_1402_ = v___x_1416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___redArg___boxed(lean_object* v_depth_1418_, lean_object* v_keys_1419_, lean_object* v_vals_1420_, lean_object* v_i_1421_, lean_object* v_entries_1422_){
_start:
{
size_t v_depth_boxed_1423_; lean_object* v_res_1424_; 
v_depth_boxed_1423_ = lean_unbox_usize(v_depth_1418_);
lean_dec(v_depth_1418_);
v_res_1424_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___redArg(v_depth_boxed_1423_, v_keys_1419_, v_vals_1420_, v_i_1421_, v_entries_1422_);
lean_dec_ref(v_vals_1420_);
lean_dec_ref(v_keys_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg___boxed(lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
size_t v_x_158828__boxed_1430_; size_t v_x_158829__boxed_1431_; lean_object* v_res_1432_; 
v_x_158828__boxed_1430_ = lean_unbox_usize(v_x_1426_);
lean_dec(v_x_1426_);
v_x_158829__boxed_1431_ = lean_unbox_usize(v_x_1427_);
lean_dec(v_x_1427_);
v_res_1432_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg(v_x_1425_, v_x_158828__boxed_1430_, v_x_158829__boxed_1431_, v_x_1428_, v_x_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7___redArg(lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
uint64_t v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = l_Lean_instHashableMVarId_hash(v_x_1434_);
v___x_1437_ = lean_uint64_to_usize(v___x_1436_);
v___x_1438_ = ((size_t)1ULL);
v___x_1439_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg(v_x_1433_, v___x_1437_, v___x_1438_, v_x_1434_, v_x_1435_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(lean_object* v_mvarId_1440_, lean_object* v_val_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v_mctx_1445_; lean_object* v_cache_1446_; lean_object* v_zetaDeltaFVarIds_1447_; lean_object* v_postponed_1448_; lean_object* v_diag_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1477_; 
v___x_1444_ = lean_st_ref_take(v___y_1442_);
v_mctx_1445_ = lean_ctor_get(v___x_1444_, 0);
v_cache_1446_ = lean_ctor_get(v___x_1444_, 1);
v_zetaDeltaFVarIds_1447_ = lean_ctor_get(v___x_1444_, 2);
v_postponed_1448_ = lean_ctor_get(v___x_1444_, 3);
v_diag_1449_ = lean_ctor_get(v___x_1444_, 4);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1451_ = v___x_1444_;
v_isShared_1452_ = v_isSharedCheck_1477_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_diag_1449_);
lean_inc(v_postponed_1448_);
lean_inc(v_zetaDeltaFVarIds_1447_);
lean_inc(v_cache_1446_);
lean_inc(v_mctx_1445_);
lean_dec(v___x_1444_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1477_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_depth_1453_; lean_object* v_levelAssignDepth_1454_; lean_object* v_lmvarCounter_1455_; lean_object* v_mvarCounter_1456_; lean_object* v_lDecls_1457_; lean_object* v_decls_1458_; lean_object* v_userNames_1459_; lean_object* v_lAssignment_1460_; lean_object* v_eAssignment_1461_; lean_object* v_dAssignment_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1476_; 
v_depth_1453_ = lean_ctor_get(v_mctx_1445_, 0);
v_levelAssignDepth_1454_ = lean_ctor_get(v_mctx_1445_, 1);
v_lmvarCounter_1455_ = lean_ctor_get(v_mctx_1445_, 2);
v_mvarCounter_1456_ = lean_ctor_get(v_mctx_1445_, 3);
v_lDecls_1457_ = lean_ctor_get(v_mctx_1445_, 4);
v_decls_1458_ = lean_ctor_get(v_mctx_1445_, 5);
v_userNames_1459_ = lean_ctor_get(v_mctx_1445_, 6);
v_lAssignment_1460_ = lean_ctor_get(v_mctx_1445_, 7);
v_eAssignment_1461_ = lean_ctor_get(v_mctx_1445_, 8);
v_dAssignment_1462_ = lean_ctor_get(v_mctx_1445_, 9);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_mctx_1445_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1464_ = v_mctx_1445_;
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_dAssignment_1462_);
lean_inc(v_eAssignment_1461_);
lean_inc(v_lAssignment_1460_);
lean_inc(v_userNames_1459_);
lean_inc(v_decls_1458_);
lean_inc(v_lDecls_1457_);
lean_inc(v_mvarCounter_1456_);
lean_inc(v_lmvarCounter_1455_);
lean_inc(v_levelAssignDepth_1454_);
lean_inc(v_depth_1453_);
lean_dec(v_mctx_1445_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7___redArg(v_eAssignment_1461_, v_mvarId_1440_, v_val_1441_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 8, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_depth_1453_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_levelAssignDepth_1454_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_lmvarCounter_1455_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_mvarCounter_1456_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_lDecls_1457_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v_decls_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_userNames_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_lAssignment_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 8, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1475_, 9, v_dAssignment_1462_);
v___x_1468_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1468_);
v___x_1470_ = v___x_1451_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_cache_1446_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_zetaDeltaFVarIds_1447_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_postponed_1448_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v_diag_1449_);
v___x_1470_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_st_ref_set(v___y_1442_, v___x_1470_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg___boxed(lean_object* v_mvarId_1478_, lean_object* v_val_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_mvarId_1478_, v_val_1479_, v___y_1480_);
lean_dec(v___y_1480_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(lean_object* v_a_1483_, lean_object* v___x_1484_, uint8_t v___x_1485_, lean_object* v___x_1486_, lean_object* v___f_1487_, lean_object* v_____r_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_box(0);
v___x_1495_ = l_Lean_Meta_mkAuxTheorem(v_a_1483_, v___x_1484_, v___x_1485_, v___x_1494_, v___x_1485_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_1486_, v_a_1496_, v___y_1490_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
v___x_1499_ = lean_apply_6(v___f_1487_, v_a_1498_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, lean_box(0));
return v___x_1499_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v___f_1487_);
v_a_1500_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1497_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1497_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v___f_1487_);
lean_dec(v___x_1486_);
v_a_1508_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1495_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1495_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7___boxed(lean_object* v_a_1516_, lean_object* v___x_1517_, lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v___f_1520_, lean_object* v_____r_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v___x_159049__boxed_1527_; lean_object* v_res_1528_; 
v___x_159049__boxed_1527_ = lean_unbox(v___x_1518_);
v_res_1528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_1516_, v___x_1517_, v___x_159049__boxed_1527_, v___x_1519_, v___f_1520_, v_____r_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(lean_object* v_cls_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_options_1535_; uint8_t v_hasTrace_1536_; 
v_options_1535_ = lean_ctor_get(v___y_1532_, 2);
v_hasTrace_1536_ = lean_ctor_get_uint8(v_options_1535_, sizeof(void*)*1);
if (v_hasTrace_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_cls_1529_);
v___x_1537_ = lean_box(v_hasTrace_1536_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v_inheritedTraceOptions_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_inheritedTraceOptions_1539_ = lean_ctor_get(v___y_1532_, 13);
v___x_1540_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
v___x_1541_ = l_Lean_Name_append(v___x_1540_, v_cls_1529_);
v___x_1542_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1539_, v_options_1535_, v___x_1541_);
lean_dec(v___x_1541_);
v___x_1543_ = lean_box(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0___boxed(lean_object* v_cls_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2(lean_object* v_snd_1552_, lean_object* v_a_1553_, lean_object* v___x_1554_, lean_object* v_____r_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_fieldName_1561_; lean_object* v___x_1562_; 
v_fieldName_1561_ = lean_ctor_get(v_snd_1552_, 0);
lean_inc(v_fieldName_1561_);
lean_dec_ref(v_snd_1552_);
v___x_1562_ = l_Lean_Meta_mkProjection(v_a_1553_, v_fieldName_1561_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_1554_, v_a_1563_, v___y_1557_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v___x_1564_, 0);
lean_dec(v_unused_1573_);
v___x_1566_ = v___x_1564_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v___x_1564_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_box(0);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1564_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1564_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v___x_1554_);
v_a_1582_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1562_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1562_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2___boxed(lean_object* v_snd_1590_, lean_object* v_a_1591_, lean_object* v___x_1592_, lean_object* v_____r_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2(v_snd_1590_, v_a_1591_, v___x_1592_, v_____r_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1599_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__0));
v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
return v___x_1602_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__2));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__4));
v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
return v___x_1608_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__6));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5(lean_object* v_val_1612_, lean_object* v_fst_1613_, lean_object* v_expectedType_1614_, lean_object* v___f_1615_, lean_object* v___f_1616_, lean_object* v___x_1617_, lean_object* v_cls_1618_, lean_object* v_snd_1619_, lean_object* v___x_1620_, lean_object* v_____r_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v_a_1662_; lean_object* v___y_1666_; lean_object* v___x_1679_; 
v___x_1679_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_val_1612_, v_fst_1613_, v_expectedType_1614_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref(v___x_1679_);
if (lean_obj_tag(v_a_1680_) == 1)
{
lean_object* v_val_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_val_1681_ = lean_ctor_get(v_a_1680_, 0);
lean_inc(v_val_1681_);
lean_dec_ref(v_a_1680_);
v___x_1682_ = lean_box(0);
v___x_1683_ = l_Lean_Meta_trySynthInstance(v_val_1681_, v___x_1682_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
if (lean_obj_tag(v_a_1684_) == 1)
{
lean_object* v_options_1685_; lean_object* v_a_1686_; lean_object* v_inheritedTraceOptions_1687_; uint8_t v_hasTrace_1688_; 
v_options_1685_ = lean_ctor_get(v___y_1624_, 2);
v_a_1686_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v_a_1684_);
v_inheritedTraceOptions_1687_ = lean_ctor_get(v___y_1624_, 13);
v_hasTrace_1688_ = lean_ctor_get_uint8(v_options_1685_, sizeof(void*)*1);
if (v_hasTrace_1688_ == 0)
{
goto v___jp_1689_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
lean_inc(v_cls_1618_);
v___x_1692_ = l_Lean_Name_append(v___x_1691_, v_cls_1618_);
v___x_1693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1687_, v_options_1685_, v___x_1692_);
lean_dec(v___x_1692_);
if (v___x_1693_ == 0)
{
goto v___jp_1689_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1694_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5);
lean_inc(v_a_1686_);
v___x_1695_ = l_Lean_MessageData_ofExpr(v_a_1686_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
lean_inc(v_cls_1618_);
v___x_1699_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_1618_, v___x_1698_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2(v_snd_1619_, v_a_1686_, v___x_1620_, v_a_1700_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
v___y_1666_ = v___x_1701_;
goto v___jp_1665_;
}
else
{
lean_object* v_a_1702_; 
lean_dec(v_a_1686_);
lean_dec(v___x_1620_);
lean_dec_ref(v_snd_1619_);
v_a_1702_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1699_);
v_a_1662_ = v_a_1702_;
goto v___jp_1661_;
}
}
}
v___jp_1689_:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2(v_snd_1619_, v_a_1686_, v___x_1620_, v___x_1617_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
v___y_1666_ = v___x_1690_;
goto v___jp_1665_;
}
}
else
{
lean_object* v___x_1703_; 
lean_dec(v_a_1684_);
lean_dec(v___x_1620_);
lean_dec_ref(v_snd_1619_);
lean_inc_ref(v___f_1615_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1703_ = lean_apply_5(v___f_1615_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; uint8_t v___x_1705_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = lean_unbox(v_a_1704_);
lean_dec(v_a_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_cls_1618_);
lean_dec_ref(v___f_1615_);
lean_dec(v_fst_1613_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1706_ = lean_apply_6(v___f_1616_, v___x_1617_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1707_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7);
lean_inc(v_fst_1613_);
v___x_1708_ = l_Lean_MessageData_ofName(v_fst_1613_);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
lean_inc(v_cls_1618_);
v___x_1712_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_1618_, v___x_1711_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
lean_dec(v_cls_1618_);
lean_dec_ref(v___f_1615_);
lean_dec(v_fst_1613_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1712_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1714_ = lean_apply_6(v___f_1616_, v_a_1713_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; 
v_a_1715_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1715_);
lean_dec_ref(v___x_1712_);
v_a_1662_ = v_a_1715_;
goto v___jp_1661_;
}
}
}
else
{
lean_object* v_a_1716_; 
v_a_1716_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1703_);
v_a_1662_ = v_a_1716_;
goto v___jp_1661_;
}
}
}
else
{
lean_object* v_a_1717_; 
lean_dec(v___x_1620_);
lean_dec_ref(v_snd_1619_);
v_a_1717_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1717_);
lean_dec_ref(v___x_1683_);
v_a_1662_ = v_a_1717_;
goto v___jp_1661_;
}
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_a_1680_);
lean_dec(v___x_1620_);
lean_dec_ref(v_snd_1619_);
lean_dec(v_cls_1618_);
lean_dec_ref(v___f_1615_);
lean_dec(v_fst_1613_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1718_ = lean_apply_6(v___f_1616_, v___x_1617_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1718_;
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v___x_1620_);
lean_dec_ref(v_snd_1619_);
lean_dec(v_cls_1618_);
lean_dec_ref(v___f_1616_);
lean_dec_ref(v___f_1615_);
lean_dec(v_fst_1613_);
v_a_1719_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1679_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1679_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
v___jp_1627_:
{
if (v___y_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1630_ = lean_apply_5(v___f_1615_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; uint8_t v___x_1632_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref(v___x_1630_);
v___x_1632_ = lean_unbox(v_a_1631_);
lean_dec(v_a_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v___y_1628_);
lean_dec(v_cls_1618_);
lean_dec(v_fst_1613_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1633_ = lean_apply_6(v___f_1616_, v___x_1617_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1634_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1);
v___x_1635_ = l_Lean_MessageData_ofName(v_fst_1613_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_Exception_toMessageData(v___y_1628_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_1618_, v___x_1640_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1643_ = lean_apply_6(v___f_1616_, v_a_1642_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1643_;
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v___f_1616_);
v_a_1644_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1641_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1641_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___y_1628_);
lean_dec(v_cls_1618_);
lean_dec_ref(v___f_1616_);
lean_dec(v_fst_1613_);
v_a_1652_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1630_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1630_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v___x_1660_; 
lean_dec(v_cls_1618_);
lean_dec_ref(v___f_1616_);
lean_dec_ref(v___f_1615_);
lean_dec(v_fst_1613_);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___y_1628_);
return v___x_1660_;
}
}
v___jp_1661_:
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Lean_Exception_isInterrupt(v_a_1662_);
if (v___x_1663_ == 0)
{
uint8_t v___x_1664_; 
lean_inc_ref(v_a_1662_);
v___x_1664_ = l_Lean_Exception_isRuntime(v_a_1662_);
v___y_1628_ = v_a_1662_;
v___y_1629_ = v___x_1664_;
goto v___jp_1627_;
}
else
{
v___y_1628_ = v_a_1662_;
v___y_1629_ = v___x_1663_;
goto v___jp_1627_;
}
}
v___jp_1665_:
{
if (lean_obj_tag(v___y_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_cls_1618_);
lean_dec_ref(v___f_1615_);
lean_dec(v_fst_1613_);
v_a_1667_ = lean_ctor_get(v___y_1666_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___y_1666_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1669_ = v___y_1666_;
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___y_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
if (lean_obj_tag(v_a_1667_) == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
lean_dec_ref(v___f_1616_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1617_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1671_);
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1676_; 
lean_del_object(v___x_1669_);
v_a_1675_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_a_1675_);
lean_dec_ref(v_a_1667_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1676_ = lean_apply_6(v___f_1616_, v_a_1675_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1678_; 
v_a_1678_ = lean_ctor_get(v___y_1666_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___y_1666_);
v_a_1662_ = v_a_1678_;
goto v___jp_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___boxed(lean_object* v_val_1727_, lean_object* v_fst_1728_, lean_object* v_expectedType_1729_, lean_object* v___f_1730_, lean_object* v___f_1731_, lean_object* v___x_1732_, lean_object* v_cls_1733_, lean_object* v_snd_1734_, lean_object* v___x_1735_, lean_object* v_____r_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5(v_val_1727_, v_fst_1728_, v_expectedType_1729_, v___f_1730_, v___f_1731_, v___x_1732_, v_cls_1733_, v_snd_1734_, v___x_1735_, v_____r_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1742_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1746_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__2);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__3);
v___x_1752_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
lean_ctor_set(v___x_1752_, 2, v___x_1751_);
lean_ctor_set(v___x_1752_, 3, v___x_1751_);
lean_ctor_set(v___x_1752_, 4, v___x_1751_);
lean_ctor_set(v___x_1752_, 5, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(lean_object* v___x_1753_, lean_object* v___x_1754_, lean_object* v___x_1755_, lean_object* v_a_1756_, uint8_t v___x_1757_, uint8_t v___x_1758_, uint8_t v_compile_1759_, uint8_t v_logCompileErrors_1760_, uint8_t v_isMeta_1761_, lean_object* v_____r_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_options_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_options_1768_ = lean_ctor_get(v___y_1765_, 2);
v___x_1769_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1770_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_a_1756_);
v___x_1771_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_1753_, v___x_1754_, v___y_1764_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1779_; 
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1780_);
v___x_1773_ = v___x_1771_;
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
else
{
lean_dec(v___x_1771_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1755_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
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
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1771_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1771_);
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
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1789_; 
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc_ref(v___x_1754_);
v___x_1789_ = lean_infer_type(v___x_1754_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1791_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
lean_inc_ref(v_a_1756_);
v___x_1791_ = l_Lean_Meta_isExprDefEq(v_a_1756_, v_a_1790_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; uint8_t v___x_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = lean_unbox(v_a_1792_);
lean_dec(v_a_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_1795_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_1794_, v___y_1766_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___x_1833_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc_n(v_a_1796_, 2);
lean_dec_ref(v___x_1795_);
v___x_1833_ = l_Lean_Meta_mkAuxDefinition(v_a_1796_, v_a_1756_, v___x_1754_, v___x_1757_, v___x_1757_, v___x_1758_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_1753_, v_a_1834_, v___y_1764_);
if (lean_obj_tag(v___x_1835_) == 0)
{
uint8_t v___x_1836_; lean_object* v___x_1837_; 
lean_dec_ref(v___x_1835_);
v___x_1836_ = 0;
lean_inc(v_a_1796_);
v___x_1837_ = l_Lean_Meta_setInlineAttribute(v_a_1796_, v___x_1836_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_dec_ref(v___x_1837_);
if (v_isMeta_1761_ == 0)
{
v___y_1819_ = v___y_1765_;
v___y_1820_ = v___y_1766_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1838_; lean_object* v_env_1839_; lean_object* v_nextMacroScope_1840_; lean_object* v_ngen_1841_; lean_object* v_auxDeclNGen_1842_; lean_object* v_traceState_1843_; lean_object* v_messages_1844_; lean_object* v_infoState_1845_; lean_object* v_snapshotTasks_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1871_; 
v___x_1838_ = lean_st_ref_take(v___y_1766_);
v_env_1839_ = lean_ctor_get(v___x_1838_, 0);
v_nextMacroScope_1840_ = lean_ctor_get(v___x_1838_, 1);
v_ngen_1841_ = lean_ctor_get(v___x_1838_, 2);
v_auxDeclNGen_1842_ = lean_ctor_get(v___x_1838_, 3);
v_traceState_1843_ = lean_ctor_get(v___x_1838_, 4);
v_messages_1844_ = lean_ctor_get(v___x_1838_, 6);
v_infoState_1845_ = lean_ctor_get(v___x_1838_, 7);
v_snapshotTasks_1846_ = lean_ctor_get(v___x_1838_, 8);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v___x_1838_, 5);
lean_dec(v_unused_1872_);
v___x_1848_ = v___x_1838_;
v_isShared_1849_ = v_isSharedCheck_1871_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_snapshotTasks_1846_);
lean_inc(v_infoState_1845_);
lean_inc(v_messages_1844_);
lean_inc(v_traceState_1843_);
lean_inc(v_auxDeclNGen_1842_);
lean_inc(v_ngen_1841_);
lean_inc(v_nextMacroScope_1840_);
lean_inc(v_env_1839_);
lean_dec(v___x_1838_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1871_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_inc(v_a_1796_);
v___x_1850_ = l_Lean_markMeta(v_env_1839_, v_a_1796_);
v___x_1851_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 5, v___x_1851_);
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_nextMacroScope_1840_);
lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_ngen_1841_);
lean_ctor_set(v_reuseFailAlloc_1870_, 3, v_auxDeclNGen_1842_);
lean_ctor_set(v_reuseFailAlloc_1870_, 4, v_traceState_1843_);
lean_ctor_set(v_reuseFailAlloc_1870_, 5, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1870_, 6, v_messages_1844_);
lean_ctor_set(v_reuseFailAlloc_1870_, 7, v_infoState_1845_);
lean_ctor_set(v_reuseFailAlloc_1870_, 8, v_snapshotTasks_1846_);
v___x_1853_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v_mctx_1856_; lean_object* v_zetaDeltaFVarIds_1857_; lean_object* v_postponed_1858_; lean_object* v_diag_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
v___x_1854_ = lean_st_ref_set(v___y_1766_, v___x_1853_);
v___x_1855_ = lean_st_ref_take(v___y_1764_);
v_mctx_1856_ = lean_ctor_get(v___x_1855_, 0);
v_zetaDeltaFVarIds_1857_ = lean_ctor_get(v___x_1855_, 2);
v_postponed_1858_ = lean_ctor_get(v___x_1855_, 3);
v_diag_1859_ = lean_ctor_get(v___x_1855_, 4);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v___x_1855_, 1);
lean_dec(v_unused_1869_);
v___x_1861_ = v___x_1855_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_diag_1859_);
lean_inc(v_postponed_1858_);
lean_inc(v_zetaDeltaFVarIds_1857_);
lean_inc(v_mctx_1856_);
lean_dec(v___x_1855_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_mctx_1856_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_zetaDeltaFVarIds_1857_);
lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_postponed_1858_);
lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_diag_1859_);
v___x_1865_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_st_ref_set(v___y_1764_, v___x_1865_);
v___y_1819_ = v___y_1765_;
v___y_1820_ = v___y_1766_;
goto v___jp_1818_;
}
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1796_);
v_a_1873_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1837_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1837_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_a_1796_);
v_a_1881_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1835_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1835_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_a_1796_);
lean_dec(v___x_1753_);
v_a_1889_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1833_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1833_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
v___jp_1797_:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_enableRealizationsForConst(v_a_1796_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1808_; 
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1800_, 0);
lean_dec(v_unused_1809_);
v___x_1802_ = v___x_1800_;
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
else
{
lean_dec(v___x_1800_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1755_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1800_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1800_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
v___jp_1818_:
{
if (v_compile_1759_ == 0)
{
v___y_1798_ = v___y_1819_;
v___y_1799_ = v___y_1820_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = lean_mk_empty_array_with_capacity(v___x_1821_);
lean_inc(v_a_1796_);
v___x_1823_ = lean_array_push(v___x_1822_, v_a_1796_);
v___x_1824_ = l_Lean_compileDecls(v___x_1823_, v_logCompileErrors_1760_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_dec_ref(v___x_1824_);
v___y_1798_ = v___y_1819_;
v___y_1799_ = v___y_1820_;
goto v___jp_1797_;
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_a_1796_);
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v_a_1756_);
lean_dec_ref(v___x_1754_);
lean_dec(v___x_1753_);
v_a_1897_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1795_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1795_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v___x_1905_; 
lean_dec_ref(v_a_1756_);
v___x_1905_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_1753_, v___x_1754_, v___y_1764_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v___x_1905_, 0);
lean_dec(v_unused_1914_);
v___x_1907_ = v___x_1905_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v___x_1905_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1755_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1905_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1905_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_a_1756_);
lean_dec_ref(v___x_1754_);
lean_dec(v___x_1753_);
v_a_1923_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1791_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1791_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_a_1756_);
lean_dec_ref(v___x_1754_);
lean_dec(v___x_1753_);
v_a_1931_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1789_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1789_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___boxed(lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v___x_1941_, lean_object* v_a_1942_, lean_object* v___x_1943_, lean_object* v___x_1944_, lean_object* v_compile_1945_, lean_object* v_logCompileErrors_1946_, lean_object* v_isMeta_1947_, lean_object* v_____r_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
uint8_t v___x_159559__boxed_1954_; uint8_t v___x_159560__boxed_1955_; uint8_t v_compile_boxed_1956_; uint8_t v_logCompileErrors_boxed_1957_; uint8_t v_isMeta_boxed_1958_; lean_object* v_res_1959_; 
v___x_159559__boxed_1954_ = lean_unbox(v___x_1943_);
v___x_159560__boxed_1955_ = lean_unbox(v___x_1944_);
v_compile_boxed_1956_ = lean_unbox(v_compile_1945_);
v_logCompileErrors_boxed_1957_ = lean_unbox(v_logCompileErrors_1946_);
v_isMeta_boxed_1958_ = lean_unbox(v_isMeta_1947_);
v_res_1959_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(v___x_1939_, v___x_1940_, v___x_1941_, v_a_1942_, v___x_159559__boxed_1954_, v___x_159560__boxed_1955_, v_compile_boxed_1956_, v_logCompileErrors_boxed_1957_, v_isMeta_boxed_1958_, v_____r_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(lean_object* v___x_1960_, lean_object* v_a_1961_, lean_object* v_____r_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_1960_, v_a_1961_, v___y_1964_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v___x_1968_, 0);
lean_dec(v_unused_1977_);
v___x_1970_ = v___x_1968_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_dec(v___x_1968_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = lean_box(0);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_a_1978_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1968_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1968_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5___boxed(lean_object* v___x_1986_, lean_object* v_a_1987_, lean_object* v_____r_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_1986_, v_a_1987_, v_____r_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6(lean_object* v___x_1995_, lean_object* v_____r_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1995_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6___boxed(lean_object* v___x_2004_, lean_object* v_____r_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6(v___x_2004_, v_____r_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(lean_object* v_val_2012_, lean_object* v_fst_2013_, lean_object* v_expectedType_2014_, lean_object* v___f_2015_, lean_object* v___f_2016_, lean_object* v___x_2017_, lean_object* v_cls_2018_, lean_object* v_snd_2019_, lean_object* v___x_2020_, lean_object* v_____r_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___y_2028_; uint8_t v___y_2029_; lean_object* v_a_2062_; lean_object* v___y_2066_; lean_object* v___x_2079_; 
v___x_2079_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_val_2012_, v_fst_2013_, v_expectedType_2014_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
if (lean_obj_tag(v_a_2080_) == 1)
{
lean_object* v_val_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_val_2081_ = lean_ctor_get(v_a_2080_, 0);
lean_inc(v_val_2081_);
lean_dec_ref(v_a_2080_);
v___x_2082_ = lean_box(0);
v___x_2083_ = l_Lean_Meta_trySynthInstance(v_val_2081_, v___x_2082_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
if (lean_obj_tag(v_a_2084_) == 1)
{
lean_object* v_options_2085_; lean_object* v_a_2086_; lean_object* v_inheritedTraceOptions_2087_; uint8_t v_hasTrace_2088_; 
v_options_2085_ = lean_ctor_get(v___y_2024_, 2);
v_a_2086_ = lean_ctor_get(v_a_2084_, 0);
lean_inc(v_a_2086_);
lean_dec_ref(v_a_2084_);
v_inheritedTraceOptions_2087_ = lean_ctor_get(v___y_2024_, 13);
v_hasTrace_2088_ = lean_ctor_get_uint8(v_options_2085_, sizeof(void*)*1);
if (v_hasTrace_2088_ == 0)
{
goto v___jp_2089_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2091_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
lean_inc(v_cls_2018_);
v___x_2092_ = l_Lean_Name_append(v___x_2091_, v_cls_2018_);
v___x_2093_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2087_, v_options_2085_, v___x_2092_);
lean_dec(v___x_2092_);
if (v___x_2093_ == 0)
{
goto v___jp_2089_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2094_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__5);
lean_inc(v_a_2086_);
v___x_2095_ = l_Lean_MessageData_ofExpr(v_a_2086_);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
lean_inc(v_cls_2018_);
v___x_2099_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_2018_, v___x_2098_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2099_);
v___x_2101_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2(v_snd_2019_, v_a_2086_, v___x_2020_, v_a_2100_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
v___y_2066_ = v___x_2101_;
goto v___jp_2065_;
}
else
{
lean_object* v_a_2102_; 
lean_dec(v_a_2086_);
lean_dec(v___x_2020_);
lean_dec_ref(v_snd_2019_);
v_a_2102_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2099_);
v_a_2062_ = v_a_2102_;
goto v___jp_2061_;
}
}
}
v___jp_2089_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__2(v_snd_2019_, v_a_2086_, v___x_2020_, v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
v___y_2066_ = v___x_2090_;
goto v___jp_2065_;
}
}
else
{
lean_object* v___x_2103_; 
lean_dec(v_a_2084_);
lean_dec(v___x_2020_);
lean_dec_ref(v_snd_2019_);
lean_inc_ref(v___f_2015_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2103_ = lean_apply_5(v___f_2015_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; uint8_t v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v___x_2105_ = lean_unbox(v_a_2104_);
lean_dec(v_a_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec(v_cls_2018_);
lean_dec_ref(v___f_2015_);
lean_dec(v_fst_2013_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2106_ = lean_apply_6(v___f_2016_, v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2107_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__7);
lean_inc(v_fst_2013_);
v___x_2108_ = l_Lean_MessageData_ofName(v_fst_2013_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
lean_inc(v_cls_2018_);
v___x_2112_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_2018_, v___x_2111_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
lean_dec(v_cls_2018_);
lean_dec_ref(v___f_2015_);
lean_dec(v_fst_2013_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2114_ = lean_apply_6(v___f_2016_, v_a_2113_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2114_;
}
else
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2115_);
lean_dec_ref(v___x_2112_);
v_a_2062_ = v_a_2115_;
goto v___jp_2061_;
}
}
}
else
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2103_);
v_a_2062_ = v_a_2116_;
goto v___jp_2061_;
}
}
}
else
{
lean_object* v_a_2117_; 
lean_dec(v___x_2020_);
lean_dec_ref(v_snd_2019_);
v_a_2117_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___x_2083_);
v_a_2062_ = v_a_2117_;
goto v___jp_2061_;
}
}
else
{
lean_object* v___x_2118_; 
lean_dec(v_a_2080_);
lean_dec(v___x_2020_);
lean_dec_ref(v_snd_2019_);
lean_dec(v_cls_2018_);
lean_dec_ref(v___f_2015_);
lean_dec(v_fst_2013_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2118_ = lean_apply_6(v___f_2016_, v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2118_;
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v___x_2020_);
lean_dec_ref(v_snd_2019_);
lean_dec(v_cls_2018_);
lean_dec_ref(v___f_2016_);
lean_dec_ref(v___f_2015_);
lean_dec(v_fst_2013_);
v_a_2119_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2079_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2079_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
v___jp_2027_:
{
if (v___y_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2030_ = lean_apply_5(v___f_2015_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; uint8_t v___x_2032_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = lean_unbox(v_a_2031_);
lean_dec(v_a_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; 
lean_dec_ref(v___y_2028_);
lean_dec(v_cls_2018_);
lean_dec(v_fst_2013_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2033_ = lean_apply_6(v___f_2016_, v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__1);
v___x_2035_ = l_Lean_MessageData_ofName(v_fst_2013_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = l_Lean_Exception_toMessageData(v___y_2028_);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_2018_, v___x_2040_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2043_ = lean_apply_6(v___f_2016_, v_a_2042_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2043_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v___f_2016_);
v_a_2044_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2041_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2041_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v___y_2028_);
lean_dec(v_cls_2018_);
lean_dec_ref(v___f_2016_);
lean_dec(v_fst_2013_);
v_a_2052_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2030_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2030_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v___x_2060_; 
lean_dec(v_cls_2018_);
lean_dec_ref(v___f_2016_);
lean_dec_ref(v___f_2015_);
lean_dec(v_fst_2013_);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2028_);
return v___x_2060_;
}
}
v___jp_2061_:
{
uint8_t v___x_2063_; 
v___x_2063_ = l_Lean_Exception_isInterrupt(v_a_2062_);
if (v___x_2063_ == 0)
{
uint8_t v___x_2064_; 
lean_inc_ref(v_a_2062_);
v___x_2064_ = l_Lean_Exception_isRuntime(v_a_2062_);
v___y_2028_ = v_a_2062_;
v___y_2029_ = v___x_2064_;
goto v___jp_2027_;
}
else
{
v___y_2028_ = v_a_2062_;
v___y_2029_ = v___x_2063_;
goto v___jp_2027_;
}
}
v___jp_2065_:
{
if (lean_obj_tag(v___y_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_cls_2018_);
lean_dec_ref(v___f_2015_);
lean_dec(v_fst_2013_);
v_a_2067_ = lean_ctor_get(v___y_2066_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___y_2066_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2069_ = v___y_2066_;
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___y_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec_ref(v___f_2016_);
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2017_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2076_; 
lean_del_object(v___x_2069_);
v_a_2075_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v_a_2067_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___x_2076_ = lean_apply_6(v___f_2016_, v_a_2075_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2076_;
}
}
}
else
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___y_2066_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___y_2066_);
v_a_2062_ = v_a_2078_;
goto v___jp_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3___boxed(lean_object* v_val_2127_, lean_object* v_fst_2128_, lean_object* v_expectedType_2129_, lean_object* v___f_2130_, lean_object* v___f_2131_, lean_object* v___x_2132_, lean_object* v_cls_2133_, lean_object* v_snd_2134_, lean_object* v___x_2135_, lean_object* v_____r_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(v_val_2127_, v_fst_2128_, v_expectedType_2129_, v___f_2130_, v___f_2131_, v___x_2132_, v_cls_2133_, v_snd_2134_, v___x_2135_, v_____r_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1(lean_object* v___x_2143_, lean_object* v___x_2144_, lean_object* v___x_2145_, lean_object* v_a_2146_, uint8_t v___x_2147_, uint8_t v_compile_2148_, uint8_t v_logCompileErrors_2149_, uint8_t v_isMeta_2150_, lean_object* v_____r_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_options_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_options_2157_ = lean_ctor_get(v___y_2154_, 2);
v___x_2158_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2159_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
lean_dec_ref(v_a_2146_);
v___x_2160_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2143_, v___x_2144_, v___y_2153_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2168_; 
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2160_, 0);
lean_dec(v_unused_2169_);
v___x_2162_ = v___x_2160_;
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
else
{
lean_dec(v___x_2160_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2145_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_a_2170_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2160_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2160_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v___x_2178_; 
lean_inc(v___y_2155_);
lean_inc_ref(v___y_2154_);
lean_inc(v___y_2153_);
lean_inc_ref(v___y_2152_);
lean_inc_ref(v___x_2144_);
v___x_2178_ = lean_infer_type(v___x_2144_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
lean_inc_ref(v_a_2146_);
v___x_2180_ = l_Lean_Meta_isExprDefEq(v_a_2146_, v_a_2179_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; uint8_t v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = lean_unbox(v_a_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_2184_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2183_, v___y_2155_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2208_; lean_object* v___y_2209_; uint8_t v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc_n(v_a_2185_, 2);
lean_dec_ref(v___x_2184_);
v___x_2222_ = lean_unbox(v_a_2181_);
v___x_2223_ = lean_unbox(v_a_2181_);
lean_dec(v_a_2181_);
v___x_2224_ = l_Lean_Meta_mkAuxDefinition(v_a_2185_, v_a_2146_, v___x_2144_, v___x_2222_, v___x_2223_, v___x_2147_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2143_, v_a_2225_, v___y_2153_);
if (lean_obj_tag(v___x_2226_) == 0)
{
uint8_t v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v___x_2226_);
v___x_2227_ = 0;
lean_inc(v_a_2185_);
v___x_2228_ = l_Lean_Meta_setInlineAttribute(v_a_2185_, v___x_2227_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_dec_ref(v___x_2228_);
if (v_isMeta_2150_ == 0)
{
v___y_2208_ = v___y_2154_;
v___y_2209_ = v___y_2155_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2229_; lean_object* v_env_2230_; lean_object* v_nextMacroScope_2231_; lean_object* v_ngen_2232_; lean_object* v_auxDeclNGen_2233_; lean_object* v_traceState_2234_; lean_object* v_messages_2235_; lean_object* v_infoState_2236_; lean_object* v_snapshotTasks_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2262_; 
v___x_2229_ = lean_st_ref_take(v___y_2155_);
v_env_2230_ = lean_ctor_get(v___x_2229_, 0);
v_nextMacroScope_2231_ = lean_ctor_get(v___x_2229_, 1);
v_ngen_2232_ = lean_ctor_get(v___x_2229_, 2);
v_auxDeclNGen_2233_ = lean_ctor_get(v___x_2229_, 3);
v_traceState_2234_ = lean_ctor_get(v___x_2229_, 4);
v_messages_2235_ = lean_ctor_get(v___x_2229_, 6);
v_infoState_2236_ = lean_ctor_get(v___x_2229_, 7);
v_snapshotTasks_2237_ = lean_ctor_get(v___x_2229_, 8);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; 
v_unused_2263_ = lean_ctor_get(v___x_2229_, 5);
lean_dec(v_unused_2263_);
v___x_2239_ = v___x_2229_;
v_isShared_2240_ = v_isSharedCheck_2262_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_snapshotTasks_2237_);
lean_inc(v_infoState_2236_);
lean_inc(v_messages_2235_);
lean_inc(v_traceState_2234_);
lean_inc(v_auxDeclNGen_2233_);
lean_inc(v_ngen_2232_);
lean_inc(v_nextMacroScope_2231_);
lean_inc(v_env_2230_);
lean_dec(v___x_2229_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2262_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
lean_inc(v_a_2185_);
v___x_2241_ = l_Lean_markMeta(v_env_2230_, v_a_2185_);
v___x_2242_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 5, v___x_2242_);
lean_ctor_set(v___x_2239_, 0, v___x_2241_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_nextMacroScope_2231_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v_ngen_2232_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_auxDeclNGen_2233_);
lean_ctor_set(v_reuseFailAlloc_2261_, 4, v_traceState_2234_);
lean_ctor_set(v_reuseFailAlloc_2261_, 5, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2261_, 6, v_messages_2235_);
lean_ctor_set(v_reuseFailAlloc_2261_, 7, v_infoState_2236_);
lean_ctor_set(v_reuseFailAlloc_2261_, 8, v_snapshotTasks_2237_);
v___x_2244_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v_mctx_2247_; lean_object* v_zetaDeltaFVarIds_2248_; lean_object* v_postponed_2249_; lean_object* v_diag_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2259_; 
v___x_2245_ = lean_st_ref_set(v___y_2155_, v___x_2244_);
v___x_2246_ = lean_st_ref_take(v___y_2153_);
v_mctx_2247_ = lean_ctor_get(v___x_2246_, 0);
v_zetaDeltaFVarIds_2248_ = lean_ctor_get(v___x_2246_, 2);
v_postponed_2249_ = lean_ctor_get(v___x_2246_, 3);
v_diag_2250_ = lean_ctor_get(v___x_2246_, 4);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; 
v_unused_2260_ = lean_ctor_get(v___x_2246_, 1);
lean_dec(v_unused_2260_);
v___x_2252_ = v___x_2246_;
v_isShared_2253_ = v_isSharedCheck_2259_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_diag_2250_);
lean_inc(v_postponed_2249_);
lean_inc(v_zetaDeltaFVarIds_2248_);
lean_inc(v_mctx_2247_);
lean_dec(v___x_2246_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2259_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v___x_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_mctx_2247_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_zetaDeltaFVarIds_2248_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_postponed_2249_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_diag_2250_);
v___x_2256_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_st_ref_set(v___y_2153_, v___x_2256_);
v___y_2208_ = v___y_2154_;
v___y_2209_ = v___y_2155_;
goto v___jp_2207_;
}
}
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2185_);
v_a_2264_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2228_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2228_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2185_);
v_a_2272_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2226_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2226_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_a_2185_);
lean_dec(v___x_2143_);
v_a_2280_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2224_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2224_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
v___jp_2186_:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_enableRealizationsForConst(v_a_2185_, v___y_2187_, v___y_2188_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2197_; 
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v___x_2189_, 0);
lean_dec(v_unused_2198_);
v___x_2191_ = v___x_2189_;
v_isShared_2192_ = v_isSharedCheck_2197_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v___x_2189_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2197_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2145_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2193_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
v_a_2199_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2189_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2189_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
v___jp_2207_:
{
if (v_compile_2148_ == 0)
{
v___y_2187_ = v___y_2208_;
v___y_2188_ = v___y_2209_;
goto v___jp_2186_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_mk_empty_array_with_capacity(v___x_2210_);
lean_inc(v_a_2185_);
v___x_2212_ = lean_array_push(v___x_2211_, v_a_2185_);
v___x_2213_ = l_Lean_compileDecls(v___x_2212_, v_logCompileErrors_2149_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_dec_ref(v___x_2213_);
v___y_2187_ = v___y_2208_;
v___y_2188_ = v___y_2209_;
goto v___jp_2186_;
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2185_);
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
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
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2146_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v_a_2288_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2184_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2184_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v___x_2296_; 
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2146_);
v___x_2296_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2143_, v___x_2144_, v___y_2153_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v___x_2296_, 0);
lean_dec(v_unused_2305_);
v___x_2298_ = v___x_2296_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_dec(v___x_2296_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2145_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
v_a_2306_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2296_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2296_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_a_2146_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v_a_2314_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2180_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2180_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v_a_2146_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v_a_2322_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2178_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2178_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1___boxed(lean_object* v___x_2330_, lean_object* v___x_2331_, lean_object* v___x_2332_, lean_object* v_a_2333_, lean_object* v___x_2334_, lean_object* v_compile_2335_, lean_object* v_logCompileErrors_2336_, lean_object* v_isMeta_2337_, lean_object* v_____r_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
uint8_t v___x_160290__boxed_2344_; uint8_t v_compile_boxed_2345_; uint8_t v_logCompileErrors_boxed_2346_; uint8_t v_isMeta_boxed_2347_; lean_object* v_res_2348_; 
v___x_160290__boxed_2344_ = lean_unbox(v___x_2334_);
v_compile_boxed_2345_ = lean_unbox(v_compile_2335_);
v_logCompileErrors_boxed_2346_ = lean_unbox(v_logCompileErrors_2336_);
v_isMeta_boxed_2347_ = lean_unbox(v_isMeta_2337_);
v_res_2348_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1(v___x_2330_, v___x_2331_, v___x_2332_, v_a_2333_, v___x_160290__boxed_2344_, v_compile_boxed_2345_, v_logCompileErrors_boxed_2346_, v_isMeta_boxed_2347_, v_____r_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
if (lean_obj_tag(v_a_2349_) == 0)
{
lean_object* v___x_2351_; 
v___x_2351_ = l_List_reverse___redArg(v_a_2350_);
return v___x_2351_;
}
else
{
lean_object* v_head_2352_; lean_object* v_tail_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2362_; 
v_head_2352_ = lean_ctor_get(v_a_2349_, 0);
v_tail_2353_ = lean_ctor_get(v_a_2349_, 1);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_a_2349_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2355_ = v_a_2349_;
v_isShared_2356_ = v_isSharedCheck_2362_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_tail_2353_);
lean_inc(v_head_2352_);
lean_dec(v_a_2349_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2362_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = l_Lean_MessageData_ofExpr(v_head_2352_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 1, v_a_2350_);
lean_ctor_set(v___x_2355_, 0, v___x_2357_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_a_2350_);
v___x_2359_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
v_a_2349_ = v_tail_2353_;
v_a_2350_ = v___x_2359_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(size_t v_sz_2363_, size_t v_i_2364_, lean_object* v_bs_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = lean_usize_dec_lt(v_i_2364_, v_sz_2363_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_bs_2365_);
return v___x_2372_;
}
else
{
lean_object* v_v_2373_; lean_object* v___x_2374_; 
v_v_2373_ = lean_array_uget_borrowed(v_bs_2365_, v_i_2364_);
lean_inc(v_v_2373_);
v___x_2374_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(v_v_2373_, v___y_2367_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; lean_object* v_bs_x27_2377_; size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = lean_unsigned_to_nat(0u);
v_bs_x27_2377_ = lean_array_uset(v_bs_2365_, v_i_2364_, v___x_2376_);
v___x_2378_ = ((size_t)1ULL);
v___x_2379_ = lean_usize_add(v_i_2364_, v___x_2378_);
v___x_2380_ = lean_array_uset(v_bs_x27_2377_, v_i_2364_, v_a_2375_);
v_i_2364_ = v___x_2379_;
v_bs_2365_ = v___x_2380_;
goto _start;
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_bs_2365_);
v_a_2382_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2374_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2374_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object* v_sz_2390_, lean_object* v_i_2391_, lean_object* v_bs_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
size_t v_sz_boxed_2398_; size_t v_i_boxed_2399_; lean_object* v_res_2400_; 
v_sz_boxed_2398_ = lean_unbox_usize(v_sz_2390_);
lean_dec(v_sz_2390_);
v_i_boxed_2399_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_boxed_2398_, v_i_boxed_2399_, v_bs_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2400_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__14(lean_object* v_e_2401_){
_start:
{
if (lean_obj_tag(v_e_2401_) == 0)
{
uint8_t v___x_2402_; 
v___x_2402_ = 2;
return v___x_2402_;
}
else
{
uint8_t v___x_2403_; 
v___x_2403_ = 0;
return v___x_2403_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__14___boxed(lean_object* v_e_2404_){
_start:
{
uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_res_2405_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__14(v_e_2404_);
lean_dec_ref(v_e_2404_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg(lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v_x_2407_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_x_2407_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v_x_2407_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v_x_2407_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 1);
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2417_ = lean_ctor_get(v_x_2407_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_x_2407_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v_x_2407_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v_x_2407_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
lean_ctor_set_tag(v___x_2419_, 0);
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg___boxed(lean_object* v_x_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg(v_x_2425_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__17(lean_object* v_opts_2428_, lean_object* v_opt_2429_){
_start:
{
lean_object* v_name_2430_; lean_object* v_defValue_2431_; lean_object* v_map_2432_; lean_object* v___x_2433_; 
v_name_2430_ = lean_ctor_get(v_opt_2429_, 0);
v_defValue_2431_ = lean_ctor_get(v_opt_2429_, 1);
v_map_2432_ = lean_ctor_get(v_opts_2428_, 0);
v___x_2433_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2432_, v_name_2430_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_inc(v_defValue_2431_);
return v_defValue_2431_;
}
else
{
lean_object* v_val_2434_; 
v_val_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_val_2434_);
lean_dec_ref(v___x_2433_);
if (lean_obj_tag(v_val_2434_) == 3)
{
lean_object* v_v_2435_; 
v_v_2435_ = lean_ctor_get(v_val_2434_, 0);
lean_inc(v_v_2435_);
lean_dec_ref(v_val_2434_);
return v_v_2435_;
}
else
{
lean_dec(v_val_2434_);
lean_inc(v_defValue_2431_);
return v_defValue_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__17___boxed(lean_object* v_opts_2436_, lean_object* v_opt_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__17(v_opts_2436_, v_opt_2437_);
lean_dec_ref(v_opt_2437_);
lean_dec_ref(v_opts_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15_spec__18(size_t v_sz_2439_, size_t v_i_2440_, lean_object* v_bs_2441_){
_start:
{
uint8_t v___x_2442_; 
v___x_2442_ = lean_usize_dec_lt(v_i_2440_, v_sz_2439_);
if (v___x_2442_ == 0)
{
return v_bs_2441_;
}
else
{
lean_object* v_v_2443_; lean_object* v_msg_2444_; lean_object* v___x_2445_; lean_object* v_bs_x27_2446_; size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v_v_2443_ = lean_array_uget_borrowed(v_bs_2441_, v_i_2440_);
v_msg_2444_ = lean_ctor_get(v_v_2443_, 1);
lean_inc_ref(v_msg_2444_);
v___x_2445_ = lean_unsigned_to_nat(0u);
v_bs_x27_2446_ = lean_array_uset(v_bs_2441_, v_i_2440_, v___x_2445_);
v___x_2447_ = ((size_t)1ULL);
v___x_2448_ = lean_usize_add(v_i_2440_, v___x_2447_);
v___x_2449_ = lean_array_uset(v_bs_x27_2446_, v_i_2440_, v_msg_2444_);
v_i_2440_ = v___x_2448_;
v_bs_2441_ = v___x_2449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15_spec__18___boxed(lean_object* v_sz_2451_, lean_object* v_i_2452_, lean_object* v_bs_2453_){
_start:
{
size_t v_sz_boxed_2454_; size_t v_i_boxed_2455_; lean_object* v_res_2456_; 
v_sz_boxed_2454_ = lean_unbox_usize(v_sz_2451_);
lean_dec(v_sz_2451_);
v_i_boxed_2455_ = lean_unbox_usize(v_i_2452_);
lean_dec(v_i_2452_);
v_res_2456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15_spec__18(v_sz_boxed_2454_, v_i_boxed_2455_, v_bs_2453_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15(lean_object* v_oldTraces_2457_, lean_object* v_data_2458_, lean_object* v_ref_2459_, lean_object* v_msg_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_fileName_2466_; lean_object* v_fileMap_2467_; lean_object* v_options_2468_; lean_object* v_currRecDepth_2469_; lean_object* v_maxRecDepth_2470_; lean_object* v_ref_2471_; lean_object* v_currNamespace_2472_; lean_object* v_openDecls_2473_; lean_object* v_initHeartbeats_2474_; lean_object* v_maxHeartbeats_2475_; lean_object* v_quotContext_2476_; lean_object* v_currMacroScope_2477_; uint8_t v_diag_2478_; lean_object* v_cancelTk_x3f_2479_; uint8_t v_suppressElabErrors_2480_; lean_object* v_inheritedTraceOptions_2481_; lean_object* v___x_2482_; lean_object* v_traceState_2483_; lean_object* v_traces_2484_; lean_object* v_ref_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; size_t v_sz_2488_; size_t v___x_2489_; lean_object* v___x_2490_; lean_object* v_msg_2491_; lean_object* v___x_2492_; lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2530_; 
v_fileName_2466_ = lean_ctor_get(v___y_2463_, 0);
v_fileMap_2467_ = lean_ctor_get(v___y_2463_, 1);
v_options_2468_ = lean_ctor_get(v___y_2463_, 2);
v_currRecDepth_2469_ = lean_ctor_get(v___y_2463_, 3);
v_maxRecDepth_2470_ = lean_ctor_get(v___y_2463_, 4);
v_ref_2471_ = lean_ctor_get(v___y_2463_, 5);
v_currNamespace_2472_ = lean_ctor_get(v___y_2463_, 6);
v_openDecls_2473_ = lean_ctor_get(v___y_2463_, 7);
v_initHeartbeats_2474_ = lean_ctor_get(v___y_2463_, 8);
v_maxHeartbeats_2475_ = lean_ctor_get(v___y_2463_, 9);
v_quotContext_2476_ = lean_ctor_get(v___y_2463_, 10);
v_currMacroScope_2477_ = lean_ctor_get(v___y_2463_, 11);
v_diag_2478_ = lean_ctor_get_uint8(v___y_2463_, sizeof(void*)*14);
v_cancelTk_x3f_2479_ = lean_ctor_get(v___y_2463_, 12);
v_suppressElabErrors_2480_ = lean_ctor_get_uint8(v___y_2463_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2481_ = lean_ctor_get(v___y_2463_, 13);
v___x_2482_ = lean_st_ref_get(v___y_2464_);
v_traceState_2483_ = lean_ctor_get(v___x_2482_, 4);
lean_inc_ref(v_traceState_2483_);
lean_dec(v___x_2482_);
v_traces_2484_ = lean_ctor_get(v_traceState_2483_, 0);
lean_inc_ref(v_traces_2484_);
lean_dec_ref(v_traceState_2483_);
v_ref_2485_ = l_Lean_replaceRef(v_ref_2459_, v_ref_2471_);
lean_inc_ref(v_inheritedTraceOptions_2481_);
lean_inc(v_cancelTk_x3f_2479_);
lean_inc(v_currMacroScope_2477_);
lean_inc(v_quotContext_2476_);
lean_inc(v_maxHeartbeats_2475_);
lean_inc(v_initHeartbeats_2474_);
lean_inc(v_openDecls_2473_);
lean_inc(v_currNamespace_2472_);
lean_inc(v_maxRecDepth_2470_);
lean_inc(v_currRecDepth_2469_);
lean_inc_ref(v_options_2468_);
lean_inc_ref(v_fileMap_2467_);
lean_inc_ref(v_fileName_2466_);
v___x_2486_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2486_, 0, v_fileName_2466_);
lean_ctor_set(v___x_2486_, 1, v_fileMap_2467_);
lean_ctor_set(v___x_2486_, 2, v_options_2468_);
lean_ctor_set(v___x_2486_, 3, v_currRecDepth_2469_);
lean_ctor_set(v___x_2486_, 4, v_maxRecDepth_2470_);
lean_ctor_set(v___x_2486_, 5, v_ref_2485_);
lean_ctor_set(v___x_2486_, 6, v_currNamespace_2472_);
lean_ctor_set(v___x_2486_, 7, v_openDecls_2473_);
lean_ctor_set(v___x_2486_, 8, v_initHeartbeats_2474_);
lean_ctor_set(v___x_2486_, 9, v_maxHeartbeats_2475_);
lean_ctor_set(v___x_2486_, 10, v_quotContext_2476_);
lean_ctor_set(v___x_2486_, 11, v_currMacroScope_2477_);
lean_ctor_set(v___x_2486_, 12, v_cancelTk_x3f_2479_);
lean_ctor_set(v___x_2486_, 13, v_inheritedTraceOptions_2481_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*14, v_diag_2478_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*14 + 1, v_suppressElabErrors_2480_);
v___x_2487_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2484_);
lean_dec_ref(v_traces_2484_);
v_sz_2488_ = lean_array_size(v___x_2487_);
v___x_2489_ = ((size_t)0ULL);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15_spec__18(v_sz_2488_, v___x_2489_, v___x_2487_);
v_msg_2491_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2491_, 0, v_data_2458_);
lean_ctor_set(v_msg_2491_, 1, v_msg_2460_);
lean_ctor_set(v_msg_2491_, 2, v___x_2490_);
v___x_2492_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_2491_, v___y_2461_, v___y_2462_, v___x_2486_, v___y_2464_);
lean_dec_ref(v___x_2486_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2530_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2530_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v_traceState_2498_; lean_object* v_env_2499_; lean_object* v_nextMacroScope_2500_; lean_object* v_ngen_2501_; lean_object* v_auxDeclNGen_2502_; lean_object* v_cache_2503_; lean_object* v_messages_2504_; lean_object* v_infoState_2505_; lean_object* v_snapshotTasks_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2529_; 
v___x_2497_ = lean_st_ref_take(v___y_2464_);
v_traceState_2498_ = lean_ctor_get(v___x_2497_, 4);
v_env_2499_ = lean_ctor_get(v___x_2497_, 0);
v_nextMacroScope_2500_ = lean_ctor_get(v___x_2497_, 1);
v_ngen_2501_ = lean_ctor_get(v___x_2497_, 2);
v_auxDeclNGen_2502_ = lean_ctor_get(v___x_2497_, 3);
v_cache_2503_ = lean_ctor_get(v___x_2497_, 5);
v_messages_2504_ = lean_ctor_get(v___x_2497_, 6);
v_infoState_2505_ = lean_ctor_get(v___x_2497_, 7);
v_snapshotTasks_2506_ = lean_ctor_get(v___x_2497_, 8);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2508_ = v___x_2497_;
v_isShared_2509_ = v_isSharedCheck_2529_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_snapshotTasks_2506_);
lean_inc(v_infoState_2505_);
lean_inc(v_messages_2504_);
lean_inc(v_cache_2503_);
lean_inc(v_traceState_2498_);
lean_inc(v_auxDeclNGen_2502_);
lean_inc(v_ngen_2501_);
lean_inc(v_nextMacroScope_2500_);
lean_inc(v_env_2499_);
lean_dec(v___x_2497_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2529_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
uint64_t v_tid_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2527_; 
v_tid_2510_ = lean_ctor_get_uint64(v_traceState_2498_, sizeof(void*)*1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_traceState_2498_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; 
v_unused_2528_ = lean_ctor_get(v_traceState_2498_, 0);
lean_dec(v_unused_2528_);
v___x_2512_ = v_traceState_2498_;
v_isShared_2513_ = v_isSharedCheck_2527_;
goto v_resetjp_2511_;
}
else
{
lean_dec(v_traceState_2498_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2527_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v_ref_2459_);
lean_ctor_set(v___x_2514_, 1, v_a_2493_);
v___x_2515_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2457_, v___x_2514_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2515_);
v___x_2517_ = v___x_2512_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2515_);
lean_ctor_set_uint64(v_reuseFailAlloc_2526_, sizeof(void*)*1, v_tid_2510_);
v___x_2517_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2519_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 4, v___x_2517_);
v___x_2519_ = v___x_2508_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_env_2499_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_nextMacroScope_2500_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_ngen_2501_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_auxDeclNGen_2502_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2525_, 5, v_cache_2503_);
lean_ctor_set(v_reuseFailAlloc_2525_, 6, v_messages_2504_);
lean_ctor_set(v_reuseFailAlloc_2525_, 7, v_infoState_2505_);
lean_ctor_set(v_reuseFailAlloc_2525_, 8, v_snapshotTasks_2506_);
v___x_2519_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2520_ = lean_st_ref_set(v___y_2464_, v___x_2519_);
v___x_2521_ = lean_box(0);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2521_);
v___x_2523_ = v___x_2495_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15___boxed(lean_object* v_oldTraces_2531_, lean_object* v_data_2532_, lean_object* v_ref_2533_, lean_object* v_msg_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15(v_oldTraces_2531_, v_data_2532_, v_ref_2533_, v_msg_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2540_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__1(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__0));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__3(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__2));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2547_; double v___x_2548_; 
v___x_2547_ = lean_unsigned_to_nat(1000u);
v___x_2548_ = lean_float_of_nat(v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11(lean_object* v_cls_2549_, uint8_t v_collapsed_2550_, lean_object* v_tag_2551_, lean_object* v_opts_2552_, uint8_t v_clsEnabled_2553_, lean_object* v_oldTraces_2554_, lean_object* v_msg_2555_, lean_object* v_resStartStop_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_fst_2562_; lean_object* v_snd_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2661_; 
v_fst_2562_ = lean_ctor_get(v_resStartStop_2556_, 0);
v_snd_2563_ = lean_ctor_get(v_resStartStop_2556_, 1);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_resStartStop_2556_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2565_ = v_resStartStop_2556_;
v_isShared_2566_ = v_isSharedCheck_2661_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_snd_2563_);
lean_inc(v_fst_2562_);
lean_dec(v_resStartStop_2556_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2661_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v_data_2570_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2660_; 
v_fst_2581_ = lean_ctor_get(v_snd_2563_, 0);
v_snd_2582_ = lean_ctor_get(v_snd_2563_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_snd_2563_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2584_ = v_snd_2563_;
v_isShared_2585_ = v_isSharedCheck_2660_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snd_2582_);
lean_inc(v_fst_2581_);
lean_dec(v_snd_2563_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2660_;
goto v_resetjp_2583_;
}
v___jp_2567_:
{
lean_object* v___x_2571_; 
lean_inc(v___y_2569_);
v___x_2571_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__15(v_oldTraces_2554_, v_data_2570_, v___y_2569_, v___y_2568_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref(v___x_2571_);
v___x_2572_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg(v_fst_2562_);
return v___x_2572_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_fst_2562_);
v_a_2573_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2571_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2571_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; uint8_t v___x_2587_; lean_object* v___y_2589_; lean_object* v_a_2590_; uint8_t v___y_2614_; double v___y_2645_; 
v___x_2586_ = l_Lean_trace_profiler;
v___x_2587_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2552_, v___x_2586_);
if (v___x_2587_ == 0)
{
v___y_2614_ = v___x_2587_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2651_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2552_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; double v___x_2654_; double v___x_2655_; double v___x_2656_; 
v___x_2652_ = l_Lean_trace_profiler_threshold;
v___x_2653_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__17(v_opts_2552_, v___x_2652_);
v___x_2654_ = lean_float_of_nat(v___x_2653_);
v___x_2655_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__4);
v___x_2656_ = lean_float_div(v___x_2654_, v___x_2655_);
v___y_2645_ = v___x_2656_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; double v___x_2659_; 
v___x_2657_ = l_Lean_trace_profiler_threshold;
v___x_2658_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__17(v_opts_2552_, v___x_2657_);
v___x_2659_ = lean_float_of_nat(v___x_2658_);
v___y_2645_ = v___x_2659_;
goto v___jp_2644_;
}
}
v___jp_2588_:
{
uint8_t v_result_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v_result_2591_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__14(v_fst_2562_);
v___x_2592_ = l_Lean_TraceResult_toEmoji(v_result_2591_);
v___x_2593_ = l_Lean_stringToMessageData(v___x_2592_);
v___x_2594_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__1);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 7);
lean_ctor_set(v___x_2584_, 1, v___x_2594_);
lean_ctor_set(v___x_2584_, 0, v___x_2593_);
v___x_2596_ = v___x_2584_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v_m_2598_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 7);
lean_ctor_set(v___x_2565_, 1, v_a_2590_);
lean_ctor_set(v___x_2565_, 0, v___x_2596_);
v_m_2598_ = v___x_2565_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_a_2590_);
v_m_2598_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; double v___x_2601_; lean_object* v_data_2602_; 
v___x_2599_ = lean_box(v_result_2591_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
v___x_2601_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
lean_inc_ref(v_tag_2551_);
lean_inc_ref(v___x_2600_);
lean_inc(v_cls_2549_);
v_data_2602_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2602_, 0, v_cls_2549_);
lean_ctor_set(v_data_2602_, 1, v___x_2600_);
lean_ctor_set(v_data_2602_, 2, v_tag_2551_);
lean_ctor_set_float(v_data_2602_, sizeof(void*)*3, v___x_2601_);
lean_ctor_set_float(v_data_2602_, sizeof(void*)*3 + 8, v___x_2601_);
lean_ctor_set_uint8(v_data_2602_, sizeof(void*)*3 + 16, v_collapsed_2550_);
if (v___x_2587_ == 0)
{
lean_dec_ref(v___x_2600_);
lean_dec(v_snd_2582_);
lean_dec(v_fst_2581_);
lean_dec_ref(v_tag_2551_);
lean_dec(v_cls_2549_);
v___y_2568_ = v_m_2598_;
v___y_2569_ = v___y_2589_;
v_data_2570_ = v_data_2602_;
goto v___jp_2567_;
}
else
{
lean_object* v_data_2603_; double v___x_2604_; double v___x_2605_; 
lean_dec_ref(v_data_2602_);
v_data_2603_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2603_, 0, v_cls_2549_);
lean_ctor_set(v_data_2603_, 1, v___x_2600_);
lean_ctor_set(v_data_2603_, 2, v_tag_2551_);
v___x_2604_ = lean_unbox_float(v_fst_2581_);
lean_dec(v_fst_2581_);
lean_ctor_set_float(v_data_2603_, sizeof(void*)*3, v___x_2604_);
v___x_2605_ = lean_unbox_float(v_snd_2582_);
lean_dec(v_snd_2582_);
lean_ctor_set_float(v_data_2603_, sizeof(void*)*3 + 8, v___x_2605_);
lean_ctor_set_uint8(v_data_2603_, sizeof(void*)*3 + 16, v_collapsed_2550_);
v___y_2568_ = v_m_2598_;
v___y_2569_ = v___y_2589_;
v_data_2570_ = v_data_2603_;
goto v___jp_2567_;
}
}
}
}
v___jp_2608_:
{
lean_object* v_ref_2609_; lean_object* v___x_2610_; 
v_ref_2609_ = lean_ctor_get(v___y_2559_, 5);
lean_inc(v___y_2560_);
lean_inc_ref(v___y_2559_);
lean_inc(v___y_2558_);
lean_inc_ref(v___y_2557_);
lean_inc(v_fst_2562_);
v___x_2610_ = lean_apply_6(v_msg_2555_, v_fst_2562_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, lean_box(0));
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2610_);
v___y_2589_ = v_ref_2609_;
v_a_2590_ = v_a_2611_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2612_; 
lean_dec_ref(v___x_2610_);
v___x_2612_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___closed__3);
v___y_2589_ = v_ref_2609_;
v_a_2590_ = v___x_2612_;
goto v___jp_2588_;
}
}
v___jp_2613_:
{
if (v_clsEnabled_2553_ == 0)
{
if (v___y_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v_traceState_2616_; lean_object* v_env_2617_; lean_object* v_nextMacroScope_2618_; lean_object* v_ngen_2619_; lean_object* v_auxDeclNGen_2620_; lean_object* v_cache_2621_; lean_object* v_messages_2622_; lean_object* v_infoState_2623_; lean_object* v_snapshotTasks_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2643_; 
lean_del_object(v___x_2584_);
lean_dec(v_snd_2582_);
lean_dec(v_fst_2581_);
lean_del_object(v___x_2565_);
lean_dec_ref(v_msg_2555_);
lean_dec_ref(v_tag_2551_);
lean_dec(v_cls_2549_);
v___x_2615_ = lean_st_ref_take(v___y_2560_);
v_traceState_2616_ = lean_ctor_get(v___x_2615_, 4);
v_env_2617_ = lean_ctor_get(v___x_2615_, 0);
v_nextMacroScope_2618_ = lean_ctor_get(v___x_2615_, 1);
v_ngen_2619_ = lean_ctor_get(v___x_2615_, 2);
v_auxDeclNGen_2620_ = lean_ctor_get(v___x_2615_, 3);
v_cache_2621_ = lean_ctor_get(v___x_2615_, 5);
v_messages_2622_ = lean_ctor_get(v___x_2615_, 6);
v_infoState_2623_ = lean_ctor_get(v___x_2615_, 7);
v_snapshotTasks_2624_ = lean_ctor_get(v___x_2615_, 8);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2626_ = v___x_2615_;
v_isShared_2627_ = v_isSharedCheck_2643_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snapshotTasks_2624_);
lean_inc(v_infoState_2623_);
lean_inc(v_messages_2622_);
lean_inc(v_cache_2621_);
lean_inc(v_traceState_2616_);
lean_inc(v_auxDeclNGen_2620_);
lean_inc(v_ngen_2619_);
lean_inc(v_nextMacroScope_2618_);
lean_inc(v_env_2617_);
lean_dec(v___x_2615_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2643_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
uint64_t v_tid_2628_; lean_object* v_traces_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2642_; 
v_tid_2628_ = lean_ctor_get_uint64(v_traceState_2616_, sizeof(void*)*1);
v_traces_2629_ = lean_ctor_get(v_traceState_2616_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_traceState_2616_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2631_ = v_traceState_2616_;
v_isShared_2632_ = v_isSharedCheck_2642_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_traces_2629_);
lean_dec(v_traceState_2616_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2642_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2554_, v_traces_2629_);
lean_dec_ref(v_traces_2629_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2633_);
v___x_2635_ = v___x_2631_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2633_);
lean_ctor_set_uint64(v_reuseFailAlloc_2641_, sizeof(void*)*1, v_tid_2628_);
v___x_2635_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2637_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 4, v___x_2635_);
v___x_2637_ = v___x_2626_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_env_2617_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_nextMacroScope_2618_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_ngen_2619_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_auxDeclNGen_2620_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2640_, 5, v_cache_2621_);
lean_ctor_set(v_reuseFailAlloc_2640_, 6, v_messages_2622_);
lean_ctor_set(v_reuseFailAlloc_2640_, 7, v_infoState_2623_);
lean_ctor_set(v_reuseFailAlloc_2640_, 8, v_snapshotTasks_2624_);
v___x_2637_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_st_ref_set(v___y_2560_, v___x_2637_);
v___x_2639_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg(v_fst_2562_);
return v___x_2639_;
}
}
}
}
}
else
{
goto v___jp_2608_;
}
}
else
{
goto v___jp_2608_;
}
}
v___jp_2644_:
{
double v___x_2646_; double v___x_2647_; double v___x_2648_; uint8_t v___x_2649_; 
v___x_2646_ = lean_unbox_float(v_snd_2582_);
v___x_2647_ = lean_unbox_float(v_fst_2581_);
v___x_2648_ = lean_float_sub(v___x_2646_, v___x_2647_);
v___x_2649_ = lean_float_decLt(v___y_2645_, v___x_2648_);
v___y_2614_ = v___x_2649_;
goto v___jp_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object* v_cls_2662_, lean_object* v_collapsed_2663_, lean_object* v_tag_2664_, lean_object* v_opts_2665_, lean_object* v_clsEnabled_2666_, lean_object* v_oldTraces_2667_, lean_object* v_msg_2668_, lean_object* v_resStartStop_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v_collapsed_boxed_2675_; uint8_t v_clsEnabled_boxed_2676_; lean_object* v_res_2677_; 
v_collapsed_boxed_2675_ = lean_unbox(v_collapsed_2663_);
v_clsEnabled_boxed_2676_ = lean_unbox(v_clsEnabled_2666_);
v_res_2677_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11(v_cls_2662_, v_collapsed_boxed_2675_, v_tag_2664_, v_opts_2665_, v_clsEnabled_boxed_2676_, v_oldTraces_2667_, v_msg_2668_, v_resStartStop_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec_ref(v_opts_2665_);
return v_res_2677_;
}
}
static uint64_t _init_l_Lean_Meta_wrapInstance___closed__0(void){
_start:
{
uint8_t v___x_2678_; uint64_t v___x_2679_; 
v___x_2678_ = 3;
v___x_2679_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2678_);
return v___x_2679_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__0));
v___x_2682_ = l_Lean_stringToMessageData(v___x_2681_);
return v___x_2682_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__3));
v___x_2687_ = l_Lean_stringToMessageData(v___x_2686_);
return v___x_2687_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__5));
v___x_2690_ = l_Lean_stringToMessageData(v___x_2689_);
return v___x_2690_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__1));
v___x_2693_ = l_Lean_stringToMessageData(v___x_2692_);
return v___x_2693_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__8));
v___x_2698_ = l_Lean_stringToMessageData(v___x_2697_);
return v___x_2698_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__10));
v___x_2701_ = l_Lean_stringToMessageData(v___x_2700_);
return v___x_2701_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__12));
v___x_2704_ = l_Lean_stringToMessageData(v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__14));
v___x_2707_ = l_Lean_stringToMessageData(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object* v_upperBound_2708_, lean_object* v_fst_2709_, lean_object* v_args_2710_, uint8_t v_compile_2711_, uint8_t v_logCompileErrors_2712_, uint8_t v___x_2713_, uint8_t v_isMeta_2714_, lean_object* v_val_2715_, lean_object* v_expectedType_2716_, lean_object* v_a_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_a_2725_; lean_object* v___y_2730_; uint8_t v___x_2749_; 
v___x_2749_ = lean_nat_dec_lt(v_a_2717_, v_upperBound_2708_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_b_2718_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2751_ = lean_array_fget_borrowed(v_fst_2709_, v_a_2717_);
v___x_2752_ = l_Lean_Expr_mvarId_x21(v___x_2751_);
lean_inc(v___x_2752_);
v___x_2753_ = l_Lean_MVarId_getDecl(v___x_2752_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v_userName_2755_; lean_object* v_type_2756_; lean_object* v___x_2757_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref(v___x_2753_);
v_userName_2755_ = lean_ctor_get(v_a_2754_, 0);
lean_inc(v_userName_2755_);
v_type_2756_ = lean_ctor_get(v_a_2754_, 2);
lean_inc_ref(v_type_2756_);
lean_dec(v_a_2754_);
v___x_2757_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(v_type_2756_, v___y_2720_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2759_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_n(v_a_2758_, 2);
lean_dec_ref(v___x_2757_);
v___x_2759_ = l_Lean_Meta_isProp(v_a_2758_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; lean_object* v_cls_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_box(0);
v_cls_2762_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_2763_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__0));
v___x_2764_ = lean_array_fget_borrowed(v_args_2710_, v_a_2717_);
v___x_2765_ = lean_unbox(v_a_2760_);
lean_dec(v_a_2760_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
lean_inc(v_a_2758_);
v___x_2766_ = l_Lean_Meta_isClass_x3f(v_a_2758_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2865_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2865_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2865_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
if (lean_obj_tag(v_a_2767_) == 0)
{
lean_object* v_options_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___f_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
lean_del_object(v___x_2769_);
v_options_2771_ = lean_ctor_get(v___y_2721_, 2);
v___x_2772_ = lean_box(v___x_2713_);
v___x_2773_ = lean_box(v___x_2749_);
v___x_2774_ = lean_box(v_compile_2711_);
v___x_2775_ = lean_box(v_logCompileErrors_2712_);
v___x_2776_ = lean_box(v_isMeta_2714_);
lean_inc(v_a_2758_);
lean_inc(v___x_2764_);
lean_inc(v___x_2752_);
v___f_2777_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_2777_, 0, v___x_2752_);
lean_closure_set(v___f_2777_, 1, v___x_2764_);
lean_closure_set(v___f_2777_, 2, v___x_2761_);
lean_closure_set(v___f_2777_, 3, v_a_2758_);
lean_closure_set(v___f_2777_, 4, v___x_2772_);
lean_closure_set(v___f_2777_, 5, v___x_2773_);
lean_closure_set(v___f_2777_, 6, v___x_2774_);
lean_closure_set(v___f_2777_, 7, v___x_2775_);
lean_closure_set(v___f_2777_, 8, v___x_2776_);
v___x_2778_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2779_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2771_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_dec_ref(v___f_2777_);
lean_dec(v_userName_2755_);
lean_inc(v___x_2764_);
v___x_2780_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(v___x_2752_, v___x_2764_, v___x_2761_, v_a_2758_, v___x_2713_, v___x_2749_, v_compile_2711_, v_logCompileErrors_2712_, v_isMeta_2714_, v___x_2761_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2780_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2781_; 
lean_inc(v_userName_2755_);
lean_inc(v_val_2715_);
v___x_2781_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_2715_, v_userName_2755_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2817_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___x_2781_);
v_fst_2785_ = lean_ctor_get(v_a_2782_, 0);
v_snd_2786_ = lean_ctor_get(v_a_2782_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_a_2782_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2788_ = v_a_2782_;
v_isShared_2789_ = v_isSharedCheck_2817_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_snd_2786_);
lean_inc(v_fst_2785_);
lean_dec(v_a_2782_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2817_;
goto v_resetjp_2787_;
}
v___jp_2783_:
{
lean_object* v___x_2784_; 
lean_inc(v___x_2764_);
v___x_2784_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(v___x_2752_, v___x_2764_, v___x_2761_, v_a_2758_, v___x_2713_, v___x_2749_, v_compile_2711_, v_logCompileErrors_2712_, v_isMeta_2714_, v___x_2761_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2784_;
goto v___jp_2729_;
}
v_resetjp_2787_:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_name_eq(v_fst_2785_, v_val_2715_);
if (v___x_2790_ == 0)
{
if (v___x_2779_ == 0)
{
lean_del_object(v___x_2788_);
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_dec_ref(v___f_2777_);
lean_dec(v_userName_2755_);
goto v___jp_2783_;
}
else
{
lean_object* v___x_2791_; 
lean_dec(v_a_2758_);
v___x_2791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_2762_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; uint8_t v___x_2793_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref(v___x_2791_);
v___x_2793_ = lean_unbox(v_a_2792_);
lean_dec(v_a_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; 
lean_del_object(v___x_2788_);
lean_dec(v_userName_2755_);
lean_inc_ref(v_expectedType_2716_);
lean_inc(v_val_2715_);
v___x_2794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(v_val_2715_, v_fst_2785_, v_expectedType_2716_, v___f_2763_, v___f_2777_, v___x_2761_, v_cls_2762_, v_snd_2786_, v___x_2752_, v___x_2761_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2794_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2795_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4);
v___x_2796_ = l_Lean_MessageData_ofName(v_userName_2755_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set_tag(v___x_2788_, 7);
lean_ctor_set(v___x_2788_, 1, v___x_2796_);
lean_ctor_set(v___x_2788_, 0, v___x_2795_);
v___x_2798_ = v___x_2788_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2799_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_inc(v_fst_2785_);
v___x_2801_ = l_Lean_MessageData_ofName(v_fst_2785_);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_2762_, v___x_2804_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
lean_inc_ref(v_expectedType_2716_);
lean_inc(v_val_2715_);
v___x_2807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(v_val_2715_, v_fst_2785_, v_expectedType_2716_, v___f_2763_, v___f_2777_, v___x_2761_, v_cls_2762_, v_snd_2786_, v___x_2752_, v_a_2806_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2807_;
goto v___jp_2729_;
}
else
{
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_dec_ref(v___f_2777_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
return v___x_2805_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_del_object(v___x_2788_);
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_dec_ref(v___f_2777_);
lean_dec(v_userName_2755_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2809_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2791_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2791_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_del_object(v___x_2788_);
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_dec_ref(v___f_2777_);
lean_dec(v_userName_2755_);
goto v___jp_2783_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v___f_2777_);
lean_dec(v_a_2758_);
lean_dec(v_userName_2755_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2818_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2781_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2781_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
else
{
lean_object* v_options_2826_; lean_object* v_a_2828_; lean_object* v___y_2831_; uint8_t v___y_2832_; lean_object* v_a_2837_; lean_object* v___y_2841_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
lean_dec_ref(v_a_2767_);
lean_dec(v_userName_2755_);
v_options_2826_ = lean_ctor_get(v___y_2721_, 2);
v___x_2845_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2846_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2826_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; 
lean_del_object(v___x_2769_);
lean_inc(v___x_2764_);
v___x_2847_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_2764_, v_a_2758_, v_compile_2711_, v_logCompileErrors_2712_, v_isMeta_2714_, v___x_2752_, v___x_2761_, v___x_2761_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2847_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_box(0);
lean_inc(v_a_2758_);
v___x_2849_ = l_Lean_Meta_trySynthInstance(v_a_2758_, v___x_2848_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
if (lean_obj_tag(v_a_2850_) == 1)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v_a_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v_a_2850_);
v___x_2852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_2762_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; uint8_t v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2852_);
v___x_2854_ = lean_unbox(v_a_2853_);
lean_dec(v_a_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_inc(v___x_2752_);
v___x_2855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_2752_, v_a_2851_, v___x_2761_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2841_ = v___x_2855_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2856_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2);
lean_inc(v_a_2851_);
v___x_2857_ = l_Lean_MessageData_ofExpr(v_a_2851_);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_2762_, v___x_2858_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref(v___x_2859_);
lean_inc(v___x_2752_);
v___x_2861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_2752_, v_a_2851_, v_a_2860_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2841_ = v___x_2861_;
goto v___jp_2840_;
}
else
{
lean_object* v_a_2862_; 
lean_dec(v_a_2851_);
v_a_2862_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2859_);
v_a_2837_ = v_a_2862_;
goto v___jp_2836_;
}
}
}
else
{
lean_object* v_a_2863_; 
lean_dec(v_a_2851_);
v_a_2863_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2852_);
v_a_2837_ = v_a_2863_;
goto v___jp_2836_;
}
}
else
{
lean_dec(v_a_2850_);
lean_del_object(v___x_2769_);
v_a_2828_ = v___x_2761_;
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_2864_; 
v_a_2864_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2849_);
v_a_2837_ = v_a_2864_;
goto v___jp_2836_;
}
}
v___jp_2827_:
{
lean_object* v___x_2829_; 
lean_inc(v___x_2764_);
v___x_2829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_2764_, v_a_2758_, v_compile_2711_, v_logCompileErrors_2712_, v_isMeta_2714_, v___x_2752_, v___x_2761_, v_a_2828_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2829_;
goto v___jp_2729_;
}
v___jp_2830_:
{
if (v___y_2832_ == 0)
{
lean_dec_ref(v___y_2831_);
lean_del_object(v___x_2769_);
v_a_2828_ = v___x_2761_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2834_; 
lean_dec(v_a_2758_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set_tag(v___x_2769_, 1);
lean_ctor_set(v___x_2769_, 0, v___y_2831_);
v___x_2834_ = v___x_2769_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___y_2831_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
v___jp_2836_:
{
uint8_t v___x_2838_; 
v___x_2838_ = l_Lean_Exception_isInterrupt(v_a_2837_);
if (v___x_2838_ == 0)
{
uint8_t v___x_2839_; 
lean_inc_ref(v_a_2837_);
v___x_2839_ = l_Lean_Exception_isRuntime(v_a_2837_);
v___y_2831_ = v_a_2837_;
v___y_2832_ = v___x_2839_;
goto v___jp_2830_;
}
else
{
v___y_2831_ = v_a_2837_;
v___y_2832_ = v___x_2838_;
goto v___jp_2830_;
}
}
v___jp_2840_:
{
if (lean_obj_tag(v___y_2841_) == 0)
{
lean_object* v_a_2842_; 
lean_del_object(v___x_2769_);
v_a_2842_ = lean_ctor_get(v___y_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___y_2841_);
if (lean_obj_tag(v_a_2842_) == 0)
{
lean_dec(v_a_2758_);
lean_dec(v___x_2752_);
v_a_2725_ = v___x_2761_;
goto v___jp_2724_;
}
else
{
lean_object* v_a_2843_; 
v_a_2843_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref(v_a_2842_);
v_a_2828_ = v_a_2843_;
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_2844_; 
v_a_2844_ = lean_ctor_get(v___y_2841_, 0);
lean_inc(v_a_2844_);
lean_dec_ref(v___y_2841_);
v_a_2837_ = v_a_2844_;
goto v___jp_2836_;
}
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2758_);
lean_dec(v_userName_2755_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2866_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2766_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2766_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_userName_2755_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___x_2764_);
v___x_2874_ = lean_infer_type(v___x_2764_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc_n(v_a_2875_, 2);
lean_dec_ref(v___x_2874_);
lean_inc(v_a_2758_);
v___x_2876_ = l_Lean_Meta_isExprDefEq(v_a_2758_, v_a_2875_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___f_2878_; uint8_t v___x_2879_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
v___f_2878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__7));
v___x_2879_ = lean_unbox(v_a_2877_);
lean_dec(v_a_2877_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; 
v___x_2880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_2762_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; uint8_t v___x_2882_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v___x_2882_ = lean_unbox(v_a_2881_);
lean_dec(v_a_2881_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; 
lean_dec(v_a_2875_);
lean_inc(v___x_2764_);
v___x_2883_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_2758_, v___x_2764_, v___x_2749_, v___x_2752_, v___f_2878_, v___x_2761_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2883_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2884_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9);
lean_inc(v_a_2717_);
v___x_2885_ = l_Nat_reprFast(v_a_2717_);
v___x_2886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
v___x_2887_ = l_Lean_MessageData_ofFormat(v___x_2886_);
v___x_2888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2884_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_inc(v_a_2758_);
v___x_2891_ = l_Lean_MessageData_ofExpr(v_a_2758_);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13);
v___x_2894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = l_Lean_MessageData_ofExpr(v_a_2875_);
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
lean_inc(v___x_2764_);
v___x_2899_ = l_Lean_MessageData_ofExpr(v___x_2764_);
v___x_2900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_2762_, v___x_2900_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
lean_inc(v___x_2764_);
v___x_2903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_2758_, v___x_2764_, v___x_2749_, v___x_2752_, v___f_2878_, v_a_2902_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2903_;
goto v___jp_2729_;
}
else
{
lean_dec(v_a_2758_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
return v___x_2901_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_a_2875_);
lean_dec(v_a_2758_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2904_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2880_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2880_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v___x_2912_; 
lean_dec(v_a_2875_);
lean_dec(v_a_2758_);
lean_inc(v___x_2764_);
v___x_2912_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2752_, v___x_2764_, v___y_2720_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6(v___x_2761_, v_a_2913_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2914_;
goto v___jp_2729_;
}
else
{
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_a_2875_);
lean_dec(v_a_2758_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2915_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2876_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2876_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_a_2758_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2923_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2874_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2874_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_a_2758_);
lean_dec(v_userName_2755_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2931_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2759_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2759_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
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
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v_userName_2755_);
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2939_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2757_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2757_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v___x_2752_);
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2947_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2753_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2753_);
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
v___jp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_add(v_a_2717_, v___x_2726_);
lean_dec(v_a_2717_);
v_a_2717_ = v___x_2727_;
v_b_2718_ = v_a_2725_;
goto _start;
}
v___jp_2729_:
{
if (lean_obj_tag(v___y_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2740_; 
v_a_2731_ = lean_ctor_get(v___y_2730_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___y_2730_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2733_ = v___y_2730_;
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___y_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
if (lean_obj_tag(v_a_2731_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2735_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v_a_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v_a_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
else
{
lean_object* v_a_2739_; 
lean_del_object(v___x_2733_);
v_a_2739_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_a_2739_);
lean_dec_ref(v_a_2731_);
v_a_2725_ = v_a_2739_;
goto v___jp_2724_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_expectedType_2716_);
lean_dec(v_val_2715_);
v_a_2741_ = lean_ctor_get(v___y_2730_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___y_2730_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___y_2730_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___y_2730_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__2));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__4));
v___x_2960_ = l_Lean_stringToMessageData(v___x_2959_);
return v___x_2960_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__6));
v___x_2963_ = l_Lean_stringToMessageData(v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__11(lean_object* v_inst_2964_, lean_object* v_expectedType_2965_, uint8_t v___x_2966_, uint8_t v_compile_2967_, uint8_t v_logCompileErrors_2968_, uint8_t v_isMeta_2969_, lean_object* v_val_2970_, lean_object* v_x_2971_, lean_object* v_x_2972_, lean_object* v_x_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; 
if (lean_obj_tag(v_x_2971_) == 5)
{
lean_object* v_fn_3018_; lean_object* v_arg_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_fn_3018_ = lean_ctor_get(v_x_2971_, 0);
lean_inc_ref(v_fn_3018_);
v_arg_3019_ = lean_ctor_get(v_x_2971_, 1);
lean_inc_ref(v_arg_3019_);
lean_dec_ref(v_x_2971_);
v___x_3020_ = lean_array_set(v_x_2972_, v_x_2973_, v_arg_3019_);
v___x_3021_ = lean_unsigned_to_nat(1u);
v___x_3022_ = lean_nat_sub(v_x_2973_, v___x_3021_);
lean_dec(v_x_2973_);
v_x_2971_ = v_fn_3018_;
v_x_2972_ = v___x_3020_;
v_x_2973_ = v___x_3022_;
goto _start;
}
else
{
uint8_t v___x_3024_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v_options_3029_; lean_object* v___y_3030_; lean_object* v_cls_3095_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___x_3118_; 
lean_dec(v_x_2973_);
v___x_3024_ = 1;
v_cls_3095_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3118_ = l_Lean_Expr_constName_x3f(v_x_2971_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2971_);
lean_dec(v_val_2970_);
v___y_3097_ = v___y_2974_;
v___y_3098_ = v___y_2975_;
v___y_3099_ = v___y_2976_;
v___y_3100_ = v___y_2977_;
goto v___jp_3096_;
}
else
{
lean_object* v_val_3119_; lean_object* v___x_3120_; 
v_val_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_val_3119_);
lean_dec_ref(v___x_3118_);
v___x_3120_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(v_val_3119_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3120_);
if (lean_obj_tag(v_a_3121_) == 6)
{
lean_object* v_val_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v_inst_2964_);
v_val_3122_ = lean_ctor_get(v_a_3121_, 0);
lean_inc_ref(v_val_3122_);
lean_dec_ref(v_a_3121_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc_ref(v_x_2971_);
v___x_3123_ = lean_infer_type(v_x_2971_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___x_3123_);
v___x_3125_ = 0;
v___x_3126_ = l_Lean_Meta_forallMetaTelescope(v_a_3124_, v___x_3125_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v_snd_3128_; lean_object* v_fst_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3228_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v_snd_3128_ = lean_ctor_get(v_a_3127_, 1);
v_fst_3129_ = lean_ctor_get(v_a_3127_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_a_3127_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3131_ = v_a_3127_;
v_isShared_3132_ = v_isSharedCheck_3228_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_snd_3128_);
lean_inc(v_fst_3129_);
lean_dec(v_a_3127_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3228_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v_snd_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3226_; 
v_snd_3133_ = lean_ctor_get(v_snd_3128_, 1);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_snd_3128_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v_snd_3128_, 0);
lean_dec(v_unused_3227_);
v___x_3135_ = v_snd_3128_;
v_isShared_3136_ = v_isSharedCheck_3226_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_snd_3133_);
lean_dec(v_snd_3128_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3226_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3137_ = lean_array_get_size(v_x_2972_);
v___x_3174_ = lean_array_get_size(v_fst_3129_);
v___x_3175_ = lean_nat_dec_eq(v___x_3137_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
lean_dec(v_snd_3133_);
lean_dec(v_fst_3129_);
lean_dec_ref(v_val_3122_);
lean_dec(v_val_2970_);
lean_dec_ref(v_expectedType_2965_);
v___x_3176_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3);
v___x_3177_ = l_Lean_MessageData_ofExpr(v_x_2971_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 7);
lean_ctor_set(v___x_3135_, 1, v___x_3177_);
lean_ctor_set(v___x_3135_, 0, v___x_3176_);
v___x_3179_ = v___x_3135_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 7);
lean_ctor_set(v___x_3131_, 1, v___x_3180_);
lean_ctor_set(v___x_3131_, 0, v___x_3179_);
v___x_3182_ = v___x_3131_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3183_ = lean_array_to_list(v_x_2972_);
v___x_3184_ = lean_box(0);
v___x_3185_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_3183_, v___x_3184_);
v___x_3186_ = l_Lean_MessageData_ofList(v___x_3185_);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3182_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3187_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
return v___x_3188_;
}
}
}
else
{
lean_object* v___x_3191_; 
lean_inc_ref(v_expectedType_2965_);
v___x_3191_ = l_Lean_Meta_isExprDefEq(v_expectedType_2965_, v_snd_3133_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; uint8_t v___x_3193_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref(v___x_3191_);
v___x_3193_ = lean_unbox(v_a_3192_);
lean_dec(v_a_3192_);
if (v___x_3193_ == 0)
{
lean_object* v_toConstantVal_3194_; lean_object* v_name_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_dec(v_fst_3129_);
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2971_);
lean_dec(v_val_2970_);
v_toConstantVal_3194_ = lean_ctor_get(v_val_3122_, 0);
lean_inc_ref(v_toConstantVal_3194_);
lean_dec_ref(v_val_3122_);
v_name_3195_ = lean_ctor_get(v_toConstantVal_3194_, 0);
lean_inc(v_name_3195_);
lean_dec_ref(v_toConstantVal_3194_);
v___x_3196_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5);
v___x_3197_ = l_Lean_MessageData_ofExpr(v_expectedType_2965_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 7);
lean_ctor_set(v___x_3135_, 1, v___x_3197_);
lean_ctor_set(v___x_3135_, 0, v___x_3196_);
v___x_3199_ = v___x_3135_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3200_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7);
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 7);
lean_ctor_set(v___x_3131_, 1, v___x_3200_);
lean_ctor_set(v___x_3131_, 0, v___x_3199_);
v___x_3202_ = v___x_3131_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
v___x_3203_ = l_Lean_MessageData_ofConstName(v_name_3195_, v___x_2966_);
v___x_3204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3202_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3204_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3206_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
else
{
lean_del_object(v___x_3135_);
lean_del_object(v___x_3131_);
v___y_3139_ = v___y_2974_;
v___y_3140_ = v___y_2975_;
v___y_3141_ = v___y_2976_;
v___y_3142_ = v___y_2977_;
goto v___jp_3138_;
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_del_object(v___x_3135_);
lean_del_object(v___x_3131_);
lean_dec(v_fst_3129_);
lean_dec_ref(v_val_3122_);
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2971_);
lean_dec(v_val_2970_);
lean_dec_ref(v_expectedType_2965_);
v_a_3218_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3191_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3191_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
v___jp_3138_:
{
lean_object* v_numParams_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_numParams_3143_ = lean_ctor_get(v_val_3122_, 3);
lean_inc(v_numParams_3143_);
lean_dec_ref(v_val_3122_);
v___x_3144_ = lean_box(0);
v___x_3145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3137_, v_fst_3129_, v_x_2972_, v_compile_2967_, v_logCompileErrors_2968_, v___x_2966_, v_isMeta_2969_, v_val_2970_, v_expectedType_2965_, v_numParams_3143_, v___x_3144_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec_ref(v_x_2972_);
if (lean_obj_tag(v___x_3145_) == 0)
{
size_t v_sz_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
lean_dec_ref(v___x_3145_);
v_sz_3146_ = lean_array_size(v_fst_3129_);
v___x_3147_ = ((size_t)0ULL);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_3146_, v___x_3147_, v_fst_3129_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3157_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3151_ = v___x_3148_;
v_isShared_3152_ = v_isSharedCheck_3157_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3157_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = l_Lean_mkAppN(v_x_2971_, v_a_3149_);
lean_dec(v_a_3149_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3155_ = v___x_3151_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref(v_x_2971_);
v_a_3158_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3148_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3148_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_fst_3129_);
lean_dec_ref(v_x_2971_);
v_a_3166_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3145_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3145_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec_ref(v_val_3122_);
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2971_);
lean_dec(v_val_2970_);
lean_dec_ref(v_expectedType_2965_);
v_a_3229_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3126_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3126_);
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
else
{
lean_dec_ref(v_val_3122_);
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2971_);
lean_dec(v_val_2970_);
lean_dec_ref(v_expectedType_2965_);
return v___x_3123_;
}
}
else
{
lean_dec(v_a_3121_);
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2971_);
lean_dec(v_val_2970_);
v___y_3097_ = v___y_2974_;
v___y_3098_ = v___y_2975_;
v___y_3099_ = v___y_2976_;
v___y_3100_ = v___y_2977_;
goto v___jp_3096_;
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2971_);
lean_dec(v_val_2970_);
lean_dec_ref(v_expectedType_2965_);
lean_dec_ref(v_inst_2964_);
v_a_3237_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3120_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3120_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
v___jp_3025_:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3032_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3029_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
lean_dec_ref(v_expectedType_2965_);
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_inst_2964_);
return v___x_3033_;
}
else
{
lean_object* v___x_3034_; 
lean_inc(v___y_3030_);
lean_inc_ref(v___y_3028_);
lean_inc(v___y_3027_);
lean_inc_ref(v___y_3026_);
lean_inc_ref(v_inst_2964_);
v___x_3034_ = lean_infer_type(v_inst_2964_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3030_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
lean_inc_ref(v_expectedType_2965_);
v___x_3036_ = l_Lean_Meta_isExprDefEq(v_expectedType_2965_, v_a_3035_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3030_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3086_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3086_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3086_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
uint8_t v___x_3041_; 
v___x_3041_ = lean_unbox(v_a_3037_);
lean_dec(v_a_3037_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v_a_3044_; lean_object* v___x_3045_; 
lean_del_object(v___x_3039_);
v___x_3042_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_3043_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3042_, v___y_3030_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc_n(v_a_3044_, 2);
lean_dec_ref(v___x_3043_);
v___x_3045_ = l_Lean_Meta_mkAuxDefinition(v_a_3044_, v_expectedType_2965_, v_inst_2964_, v___x_2966_, v___x_2966_, v___x_3024_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3030_);
if (lean_obj_tag(v___x_3045_) == 0)
{
if (v_isMeta_2969_ == 0)
{
lean_object* v_a_3046_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref(v___x_3045_);
v___y_3002_ = v_a_3044_;
v___y_3003_ = v_a_3046_;
v___y_3004_ = v___y_3028_;
v___y_3005_ = v___y_3030_;
goto v___jp_3001_;
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v_env_3049_; lean_object* v_nextMacroScope_3050_; lean_object* v_ngen_3051_; lean_object* v_auxDeclNGen_3052_; lean_object* v_traceState_3053_; lean_object* v_messages_3054_; lean_object* v_infoState_3055_; lean_object* v_snapshotTasks_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3081_; 
v_a_3047_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3045_);
v___x_3048_ = lean_st_ref_take(v___y_3030_);
v_env_3049_ = lean_ctor_get(v___x_3048_, 0);
v_nextMacroScope_3050_ = lean_ctor_get(v___x_3048_, 1);
v_ngen_3051_ = lean_ctor_get(v___x_3048_, 2);
v_auxDeclNGen_3052_ = lean_ctor_get(v___x_3048_, 3);
v_traceState_3053_ = lean_ctor_get(v___x_3048_, 4);
v_messages_3054_ = lean_ctor_get(v___x_3048_, 6);
v_infoState_3055_ = lean_ctor_get(v___x_3048_, 7);
v_snapshotTasks_3056_ = lean_ctor_get(v___x_3048_, 8);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3048_, 5);
lean_dec(v_unused_3082_);
v___x_3058_ = v___x_3048_;
v_isShared_3059_ = v_isSharedCheck_3081_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_snapshotTasks_3056_);
lean_inc(v_infoState_3055_);
lean_inc(v_messages_3054_);
lean_inc(v_traceState_3053_);
lean_inc(v_auxDeclNGen_3052_);
lean_inc(v_ngen_3051_);
lean_inc(v_nextMacroScope_3050_);
lean_inc(v_env_3049_);
lean_dec(v___x_3048_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3081_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_inc(v_a_3044_);
v___x_3060_ = l_Lean_markMeta(v_env_3049_, v_a_3044_);
v___x_3061_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 5, v___x_3061_);
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3063_ = v___x_3058_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_nextMacroScope_3050_);
lean_ctor_set(v_reuseFailAlloc_3080_, 2, v_ngen_3051_);
lean_ctor_set(v_reuseFailAlloc_3080_, 3, v_auxDeclNGen_3052_);
lean_ctor_set(v_reuseFailAlloc_3080_, 4, v_traceState_3053_);
lean_ctor_set(v_reuseFailAlloc_3080_, 5, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3080_, 6, v_messages_3054_);
lean_ctor_set(v_reuseFailAlloc_3080_, 7, v_infoState_3055_);
lean_ctor_set(v_reuseFailAlloc_3080_, 8, v_snapshotTasks_3056_);
v___x_3063_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v_mctx_3066_; lean_object* v_zetaDeltaFVarIds_3067_; lean_object* v_postponed_3068_; lean_object* v_diag_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3078_; 
v___x_3064_ = lean_st_ref_set(v___y_3030_, v___x_3063_);
v___x_3065_ = lean_st_ref_take(v___y_3027_);
v_mctx_3066_ = lean_ctor_get(v___x_3065_, 0);
v_zetaDeltaFVarIds_3067_ = lean_ctor_get(v___x_3065_, 2);
v_postponed_3068_ = lean_ctor_get(v___x_3065_, 3);
v_diag_3069_ = lean_ctor_get(v___x_3065_, 4);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v___x_3065_, 1);
lean_dec(v_unused_3079_);
v___x_3071_ = v___x_3065_;
v_isShared_3072_ = v_isSharedCheck_3078_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_diag_3069_);
lean_inc(v_postponed_3068_);
lean_inc(v_zetaDeltaFVarIds_3067_);
lean_inc(v_mctx_3066_);
lean_dec(v___x_3065_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3078_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 1, v___x_3073_);
v___x_3075_ = v___x_3071_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_mctx_3066_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_zetaDeltaFVarIds_3067_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_postponed_3068_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v_diag_3069_);
v___x_3075_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_st_ref_set(v___y_3027_, v___x_3075_);
v___y_3002_ = v_a_3044_;
v___y_3003_ = v_a_3047_;
v___y_3004_ = v___y_3028_;
v___y_3005_ = v___y_3030_;
goto v___jp_3001_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3044_);
return v___x_3045_;
}
}
else
{
lean_object* v___x_3084_; 
lean_dec_ref(v_expectedType_2965_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v_inst_2964_);
v___x_3084_ = v___x_3039_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_inst_2964_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v_expectedType_2965_);
lean_dec_ref(v_inst_2964_);
v_a_3087_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3036_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3036_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2965_);
lean_dec_ref(v_inst_2964_);
return v___x_3034_;
}
}
}
v___jp_3096_:
{
lean_object* v_options_3101_; uint8_t v_hasTrace_3102_; 
v_options_3101_ = lean_ctor_get(v___y_3099_, 2);
v_hasTrace_3102_ = lean_ctor_get_uint8(v_options_3101_, sizeof(void*)*1);
if (v_hasTrace_3102_ == 0)
{
v___y_3026_ = v___y_3097_;
v___y_3027_ = v___y_3098_;
v___y_3028_ = v___y_3099_;
v_options_3029_ = v_options_3101_;
v___y_3030_ = v___y_3100_;
goto v___jp_3025_;
}
else
{
lean_object* v_inheritedTraceOptions_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v_inheritedTraceOptions_3103_ = lean_ctor_get(v___y_3099_, 13);
v___x_3104_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_3105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3103_, v_options_3101_, v___x_3104_);
if (v___x_3105_ == 0)
{
v___y_3026_ = v___y_3097_;
v___y_3027_ = v___y_3098_;
v___y_3028_ = v___y_3099_;
v_options_3029_ = v_options_3101_;
v___y_3030_ = v___y_3100_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3106_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1);
lean_inc_ref(v_inst_2964_);
v___x_3107_ = l_Lean_MessageData_ofExpr(v_inst_2964_);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3095_, v___x_3108_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_dec_ref(v___x_3109_);
v___y_3026_ = v___y_3097_;
v___y_3027_ = v___y_3098_;
v___y_3028_ = v___y_3099_;
v_options_3029_ = v_options_3101_;
v___y_3030_ = v___y_3100_;
goto v___jp_3025_;
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v_expectedType_2965_);
lean_dec_ref(v_inst_2964_);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
}
}
v___jp_2979_:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_enableRealizationsForConst(v___y_2981_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v___x_2984_, 0);
lean_dec(v_unused_2992_);
v___x_2986_ = v___x_2984_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_dec(v___x_2984_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___y_2980_);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___y_2980_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref(v___y_2980_);
v_a_2993_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2984_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2984_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
v___jp_3001_:
{
if (v_compile_2967_ == 0)
{
v___y_2980_ = v___y_3003_;
v___y_2981_ = v___y_3002_;
v___y_2982_ = v___y_3004_;
v___y_2983_ = v___y_3005_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3006_ = lean_unsigned_to_nat(1u);
v___x_3007_ = lean_mk_empty_array_with_capacity(v___x_3006_);
lean_inc(v___y_3002_);
v___x_3008_ = lean_array_push(v___x_3007_, v___y_3002_);
v___x_3009_ = l_Lean_compileDecls(v___x_3008_, v_logCompileErrors_2968_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_dec_ref(v___x_3009_);
v___y_2980_ = v___y_3003_;
v___y_2981_ = v___y_3002_;
v___y_2982_ = v___y_3004_;
v___y_2983_ = v___y_3005_;
goto v___jp_2979_;
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(lean_object* v_inst_3245_, lean_object* v_expectedType_3246_, uint8_t v___x_3247_, uint8_t v_compile_3248_, uint8_t v_logCompileErrors_3249_, uint8_t v_isMeta_3250_, lean_object* v_val_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; 
if (lean_obj_tag(v_x_3252_) == 5)
{
lean_object* v_fn_3299_; lean_object* v_arg_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_fn_3299_ = lean_ctor_get(v_x_3252_, 0);
lean_inc_ref(v_fn_3299_);
v_arg_3300_ = lean_ctor_get(v_x_3252_, 1);
lean_inc_ref(v_arg_3300_);
lean_dec_ref(v_x_3252_);
v___x_3301_ = lean_array_set(v_x_3253_, v_x_3254_, v_arg_3300_);
v___x_3302_ = lean_unsigned_to_nat(1u);
v___x_3303_ = lean_nat_sub(v_x_3254_, v___x_3302_);
v___x_3304_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__11(v_inst_3245_, v_expectedType_3246_, v___x_3247_, v_compile_3248_, v_logCompileErrors_3249_, v_isMeta_3250_, v_val_3251_, v_fn_3299_, v___x_3301_, v___x_3303_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
return v___x_3304_;
}
else
{
uint8_t v___x_3305_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v_options_3310_; lean_object* v___y_3311_; lean_object* v_cls_3376_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___x_3399_; 
v___x_3305_ = 1;
v_cls_3376_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3399_ = l_Lean_Expr_constName_x3f(v_x_3252_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
lean_dec(v_val_3251_);
v___y_3378_ = v___y_3255_;
v___y_3379_ = v___y_3256_;
v___y_3380_ = v___y_3257_;
v___y_3381_ = v___y_3258_;
goto v___jp_3377_;
}
else
{
lean_object* v_val_3400_; lean_object* v___x_3401_; 
v_val_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_val_3400_);
lean_dec_ref(v___x_3399_);
v___x_3401_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(v_val_3400_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v___x_3401_);
if (lean_obj_tag(v_a_3402_) == 6)
{
lean_object* v_val_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v_inst_3245_);
v_val_3403_ = lean_ctor_get(v_a_3402_, 0);
lean_inc_ref(v_val_3403_);
lean_dec_ref(v_a_3402_);
lean_inc(v___y_3258_);
lean_inc_ref(v___y_3257_);
lean_inc(v___y_3256_);
lean_inc_ref(v___y_3255_);
lean_inc_ref(v_x_3252_);
v___x_3404_ = lean_infer_type(v_x_3252_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; uint8_t v___x_3406_; lean_object* v___x_3407_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v___x_3404_);
v___x_3406_ = 0;
v___x_3407_ = l_Lean_Meta_forallMetaTelescope(v_a_3405_, v___x_3406_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v_snd_3409_; lean_object* v_fst_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3509_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref(v___x_3407_);
v_snd_3409_ = lean_ctor_get(v_a_3408_, 1);
v_fst_3410_ = lean_ctor_get(v_a_3408_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3408_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3412_ = v_a_3408_;
v_isShared_3413_ = v_isSharedCheck_3509_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_snd_3409_);
lean_inc(v_fst_3410_);
lean_dec(v_a_3408_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3509_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v_snd_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3507_; 
v_snd_3414_ = lean_ctor_get(v_snd_3409_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_snd_3409_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; 
v_unused_3508_ = lean_ctor_get(v_snd_3409_, 0);
lean_dec(v_unused_3508_);
v___x_3416_ = v_snd_3409_;
v_isShared_3417_ = v_isSharedCheck_3507_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_snd_3414_);
lean_dec(v_snd_3409_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3507_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3418_ = lean_array_get_size(v_x_3253_);
v___x_3455_ = lean_array_get_size(v_fst_3410_);
v___x_3456_ = lean_nat_dec_eq(v___x_3418_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
lean_dec(v_snd_3414_);
lean_dec(v_fst_3410_);
lean_dec_ref(v_val_3403_);
lean_dec(v_val_3251_);
lean_dec_ref(v_expectedType_3246_);
v___x_3457_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3);
v___x_3458_ = l_Lean_MessageData_ofExpr(v_x_3252_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 7);
lean_ctor_set(v___x_3416_, 1, v___x_3458_);
lean_ctor_set(v___x_3416_, 0, v___x_3457_);
v___x_3460_ = v___x_3416_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 7);
lean_ctor_set(v___x_3412_, 1, v___x_3461_);
lean_ctor_set(v___x_3412_, 0, v___x_3460_);
v___x_3463_ = v___x_3412_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3464_ = lean_array_to_list(v_x_3253_);
v___x_3465_ = lean_box(0);
v___x_3466_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_3464_, v___x_3465_);
v___x_3467_ = l_Lean_MessageData_ofList(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3463_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3468_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
return v___x_3469_;
}
}
}
else
{
lean_object* v___x_3472_; 
lean_inc_ref(v_expectedType_3246_);
v___x_3472_ = l_Lean_Meta_isExprDefEq(v_expectedType_3246_, v_snd_3414_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; uint8_t v___x_3474_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v___x_3472_);
v___x_3474_ = lean_unbox(v_a_3473_);
lean_dec(v_a_3473_);
if (v___x_3474_ == 0)
{
lean_object* v_toConstantVal_3475_; lean_object* v_name_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
lean_dec(v_fst_3410_);
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
lean_dec(v_val_3251_);
v_toConstantVal_3475_ = lean_ctor_get(v_val_3403_, 0);
lean_inc_ref(v_toConstantVal_3475_);
lean_dec_ref(v_val_3403_);
v_name_3476_ = lean_ctor_get(v_toConstantVal_3475_, 0);
lean_inc(v_name_3476_);
lean_dec_ref(v_toConstantVal_3475_);
v___x_3477_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5);
v___x_3478_ = l_Lean_MessageData_ofExpr(v_expectedType_3246_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 7);
lean_ctor_set(v___x_3416_, 1, v___x_3478_);
lean_ctor_set(v___x_3416_, 0, v___x_3477_);
v___x_3480_ = v___x_3416_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3481_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7);
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 7);
lean_ctor_set(v___x_3412_, 1, v___x_3481_);
lean_ctor_set(v___x_3412_, 0, v___x_3480_);
v___x_3483_ = v___x_3412_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
v___x_3484_ = l_Lean_MessageData_ofConstName(v_name_3476_, v___x_3247_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3487_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
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
else
{
lean_del_object(v___x_3416_);
lean_del_object(v___x_3412_);
v___y_3420_ = v___y_3255_;
v___y_3421_ = v___y_3256_;
v___y_3422_ = v___y_3257_;
v___y_3423_ = v___y_3258_;
goto v___jp_3419_;
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_del_object(v___x_3416_);
lean_del_object(v___x_3412_);
lean_dec(v_fst_3410_);
lean_dec_ref(v_val_3403_);
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
lean_dec(v_val_3251_);
lean_dec_ref(v_expectedType_3246_);
v_a_3499_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3472_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3472_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
v___jp_3419_:
{
lean_object* v_numParams_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_numParams_3424_ = lean_ctor_get(v_val_3403_, 3);
lean_inc(v_numParams_3424_);
lean_dec_ref(v_val_3403_);
v___x_3425_ = lean_box(0);
v___x_3426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3418_, v_fst_3410_, v_x_3253_, v_compile_3248_, v_logCompileErrors_3249_, v___x_3247_, v_isMeta_3250_, v_val_3251_, v_expectedType_3246_, v_numParams_3424_, v___x_3425_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec_ref(v_x_3253_);
if (lean_obj_tag(v___x_3426_) == 0)
{
size_t v_sz_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref(v___x_3426_);
v_sz_3427_ = lean_array_size(v_fst_3410_);
v___x_3428_ = ((size_t)0ULL);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_3427_, v___x_3428_, v_fst_3410_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3438_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3432_ = v___x_3429_;
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3434_ = l_Lean_mkAppN(v_x_3252_, v_a_3430_);
lean_dec(v_a_3430_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v___x_3434_);
v___x_3436_ = v___x_3432_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec_ref(v_x_3252_);
v_a_3439_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3429_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3429_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_fst_3410_);
lean_dec_ref(v_x_3252_);
v_a_3447_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3426_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3426_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v_val_3403_);
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
lean_dec(v_val_3251_);
lean_dec_ref(v_expectedType_3246_);
v_a_3510_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3407_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3407_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_dec_ref(v_val_3403_);
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
lean_dec(v_val_3251_);
lean_dec_ref(v_expectedType_3246_);
return v___x_3404_;
}
}
else
{
lean_dec(v_a_3402_);
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
lean_dec(v_val_3251_);
v___y_3378_ = v___y_3255_;
v___y_3379_ = v___y_3256_;
v___y_3380_ = v___y_3257_;
v___y_3381_ = v___y_3258_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
lean_dec(v_val_3251_);
lean_dec_ref(v_expectedType_3246_);
lean_dec_ref(v_inst_3245_);
v_a_3518_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3401_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3401_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
v___jp_3306_:
{
lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3312_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3313_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3310_, v___x_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_dec_ref(v_expectedType_3246_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_inst_3245_);
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; 
lean_inc(v___y_3311_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
lean_inc_ref(v_inst_3245_);
v___x_3315_ = lean_infer_type(v_inst_3245_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3311_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3317_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref(v___x_3315_);
lean_inc_ref(v_expectedType_3246_);
v___x_3317_ = l_Lean_Meta_isExprDefEq(v_expectedType_3246_, v_a_3316_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3311_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3367_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3367_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3367_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_unbox(v_a_3318_);
lean_dec(v_a_3318_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v_a_3325_; lean_object* v___x_3326_; 
lean_del_object(v___x_3320_);
v___x_3323_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_3324_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3323_, v___y_3311_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc_n(v_a_3325_, 2);
lean_dec_ref(v___x_3324_);
v___x_3326_ = l_Lean_Meta_mkAuxDefinition(v_a_3325_, v_expectedType_3246_, v_inst_3245_, v___x_3247_, v___x_3247_, v___x_3305_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3311_);
if (lean_obj_tag(v___x_3326_) == 0)
{
if (v_isMeta_3250_ == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v___y_3283_ = v_a_3327_;
v___y_3284_ = v_a_3325_;
v___y_3285_ = v___y_3309_;
v___y_3286_ = v___y_3311_;
goto v___jp_3282_;
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3329_; lean_object* v_env_3330_; lean_object* v_nextMacroScope_3331_; lean_object* v_ngen_3332_; lean_object* v_auxDeclNGen_3333_; lean_object* v_traceState_3334_; lean_object* v_messages_3335_; lean_object* v_infoState_3336_; lean_object* v_snapshotTasks_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3362_; 
v_a_3328_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3328_);
lean_dec_ref(v___x_3326_);
v___x_3329_ = lean_st_ref_take(v___y_3311_);
v_env_3330_ = lean_ctor_get(v___x_3329_, 0);
v_nextMacroScope_3331_ = lean_ctor_get(v___x_3329_, 1);
v_ngen_3332_ = lean_ctor_get(v___x_3329_, 2);
v_auxDeclNGen_3333_ = lean_ctor_get(v___x_3329_, 3);
v_traceState_3334_ = lean_ctor_get(v___x_3329_, 4);
v_messages_3335_ = lean_ctor_get(v___x_3329_, 6);
v_infoState_3336_ = lean_ctor_get(v___x_3329_, 7);
v_snapshotTasks_3337_ = lean_ctor_get(v___x_3329_, 8);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v___x_3329_, 5);
lean_dec(v_unused_3363_);
v___x_3339_ = v___x_3329_;
v_isShared_3340_ = v_isSharedCheck_3362_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snapshotTasks_3337_);
lean_inc(v_infoState_3336_);
lean_inc(v_messages_3335_);
lean_inc(v_traceState_3334_);
lean_inc(v_auxDeclNGen_3333_);
lean_inc(v_ngen_3332_);
lean_inc(v_nextMacroScope_3331_);
lean_inc(v_env_3330_);
lean_dec(v___x_3329_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3362_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_inc(v_a_3325_);
v___x_3341_ = l_Lean_markMeta(v_env_3330_, v_a_3325_);
v___x_3342_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 5, v___x_3342_);
lean_ctor_set(v___x_3339_, 0, v___x_3341_);
v___x_3344_ = v___x_3339_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_nextMacroScope_3331_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_ngen_3332_);
lean_ctor_set(v_reuseFailAlloc_3361_, 3, v_auxDeclNGen_3333_);
lean_ctor_set(v_reuseFailAlloc_3361_, 4, v_traceState_3334_);
lean_ctor_set(v_reuseFailAlloc_3361_, 5, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3361_, 6, v_messages_3335_);
lean_ctor_set(v_reuseFailAlloc_3361_, 7, v_infoState_3336_);
lean_ctor_set(v_reuseFailAlloc_3361_, 8, v_snapshotTasks_3337_);
v___x_3344_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v_mctx_3347_; lean_object* v_zetaDeltaFVarIds_3348_; lean_object* v_postponed_3349_; lean_object* v_diag_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3359_; 
v___x_3345_ = lean_st_ref_set(v___y_3311_, v___x_3344_);
v___x_3346_ = lean_st_ref_take(v___y_3308_);
v_mctx_3347_ = lean_ctor_get(v___x_3346_, 0);
v_zetaDeltaFVarIds_3348_ = lean_ctor_get(v___x_3346_, 2);
v_postponed_3349_ = lean_ctor_get(v___x_3346_, 3);
v_diag_3350_ = lean_ctor_get(v___x_3346_, 4);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; 
v_unused_3360_ = lean_ctor_get(v___x_3346_, 1);
lean_dec(v_unused_3360_);
v___x_3352_ = v___x_3346_;
v_isShared_3353_ = v_isSharedCheck_3359_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_diag_3350_);
lean_inc(v_postponed_3349_);
lean_inc(v_zetaDeltaFVarIds_3348_);
lean_inc(v_mctx_3347_);
lean_dec(v___x_3346_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3359_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3354_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v___x_3354_);
v___x_3356_ = v___x_3352_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_mctx_3347_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3358_, 2, v_zetaDeltaFVarIds_3348_);
lean_ctor_set(v_reuseFailAlloc_3358_, 3, v_postponed_3349_);
lean_ctor_set(v_reuseFailAlloc_3358_, 4, v_diag_3350_);
v___x_3356_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_st_ref_set(v___y_3308_, v___x_3356_);
v___y_3283_ = v_a_3328_;
v___y_3284_ = v_a_3325_;
v___y_3285_ = v___y_3309_;
v___y_3286_ = v___y_3311_;
goto v___jp_3282_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3325_);
return v___x_3326_;
}
}
else
{
lean_object* v___x_3365_; 
lean_dec_ref(v_expectedType_3246_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_inst_3245_);
v___x_3365_ = v___x_3320_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_inst_3245_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec_ref(v_expectedType_3246_);
lean_dec_ref(v_inst_3245_);
v_a_3368_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3317_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3317_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3246_);
lean_dec_ref(v_inst_3245_);
return v___x_3315_;
}
}
}
v___jp_3377_:
{
lean_object* v_options_3382_; uint8_t v_hasTrace_3383_; 
v_options_3382_ = lean_ctor_get(v___y_3380_, 2);
v_hasTrace_3383_ = lean_ctor_get_uint8(v_options_3382_, sizeof(void*)*1);
if (v_hasTrace_3383_ == 0)
{
v___y_3307_ = v___y_3378_;
v___y_3308_ = v___y_3379_;
v___y_3309_ = v___y_3380_;
v_options_3310_ = v_options_3382_;
v___y_3311_ = v___y_3381_;
goto v___jp_3306_;
}
else
{
lean_object* v_inheritedTraceOptions_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_inheritedTraceOptions_3384_ = lean_ctor_get(v___y_3380_, 13);
v___x_3385_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_3386_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3384_, v_options_3382_, v___x_3385_);
if (v___x_3386_ == 0)
{
v___y_3307_ = v___y_3378_;
v___y_3308_ = v___y_3379_;
v___y_3309_ = v___y_3380_;
v_options_3310_ = v_options_3382_;
v___y_3311_ = v___y_3381_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3387_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1);
lean_inc_ref(v_inst_3245_);
v___x_3388_ = l_Lean_MessageData_ofExpr(v_inst_3245_);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3376_, v___x_3389_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_dec_ref(v___x_3390_);
v___y_3307_ = v___y_3378_;
v___y_3308_ = v___y_3379_;
v___y_3309_ = v___y_3380_;
v_options_3310_ = v_options_3382_;
v___y_3311_ = v___y_3381_;
goto v___jp_3306_;
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v_expectedType_3246_);
lean_dec_ref(v_inst_3245_);
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
}
}
v___jp_3260_:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_enableRealizationsForConst(v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; 
v_unused_3273_ = lean_ctor_get(v___x_3265_, 0);
lean_dec(v_unused_3273_);
v___x_3267_ = v___x_3265_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_dec(v___x_3265_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v___y_3261_);
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___y_3261_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref(v___y_3261_);
v_a_3274_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3265_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3265_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
v___jp_3282_:
{
if (v_compile_3248_ == 0)
{
v___y_3261_ = v___y_3283_;
v___y_3262_ = v___y_3284_;
v___y_3263_ = v___y_3285_;
v___y_3264_ = v___y_3286_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3287_ = lean_unsigned_to_nat(1u);
v___x_3288_ = lean_mk_empty_array_with_capacity(v___x_3287_);
lean_inc(v___y_3284_);
v___x_3289_ = lean_array_push(v___x_3288_, v___y_3284_);
v___x_3290_ = l_Lean_compileDecls(v___x_3289_, v_logCompileErrors_3249_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_dec_ref(v___x_3290_);
v___y_3261_ = v___y_3283_;
v___y_3262_ = v___y_3284_;
v___y_3263_ = v___y_3285_;
v___y_3264_ = v___y_3286_;
goto v___jp_3260_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
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
lean_object* v___x_3526_; double v___x_3527_; 
v___x_3526_ = lean_unsigned_to_nat(1000000000u);
v___x_3527_ = lean_float_of_nat(v___x_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___redArg(lean_object* v_upperBound_3528_, lean_object* v_fst_3529_, lean_object* v_args_3530_, uint8_t v___x_3531_, uint8_t v_compile_3532_, uint8_t v_logCompileErrors_3533_, uint8_t v___x_3534_, uint8_t v_isMeta_3535_, lean_object* v_val_3536_, lean_object* v_expectedType_3537_, lean_object* v_a_3538_, lean_object* v_b_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_a_3546_; lean_object* v___y_3551_; uint8_t v___x_3570_; 
v___x_3570_ = lean_nat_dec_lt(v_a_3538_, v_upperBound_3528_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_b_3539_);
return v___x_3571_;
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3572_ = lean_array_fget_borrowed(v_fst_3529_, v_a_3538_);
v___x_3573_ = l_Lean_Expr_mvarId_x21(v___x_3572_);
lean_inc(v___x_3573_);
v___x_3574_ = l_Lean_MVarId_getDecl(v___x_3573_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v_userName_3576_; lean_object* v_type_3577_; lean_object* v___x_3578_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref(v___x_3574_);
v_userName_3576_ = lean_ctor_get(v_a_3575_, 0);
lean_inc(v_userName_3576_);
v_type_3577_ = lean_ctor_get(v_a_3575_, 2);
lean_inc_ref(v_type_3577_);
lean_dec(v_a_3575_);
v___x_3578_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(v_type_3577_, v___y_3541_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3580_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc_n(v_a_3579_, 2);
lean_dec_ref(v___x_3578_);
v___x_3580_ = l_Lean_Meta_isProp(v_a_3579_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3582_; lean_object* v_cls_3583_; lean_object* v___f_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = lean_box(0);
v_cls_3583_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__0));
v___x_3585_ = lean_array_fget_borrowed(v_args_3530_, v_a_3538_);
v___x_3586_ = lean_unbox(v_a_3581_);
lean_dec(v_a_3581_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; 
lean_inc(v_a_3579_);
v___x_3587_ = l_Lean_Meta_isClass_x3f(v_a_3579_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3686_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3686_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3686_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v_a_3593_; lean_object* v___y_3596_; uint8_t v___y_3597_; lean_object* v_a_3602_; lean_object* v___y_3606_; 
if (lean_obj_tag(v_a_3588_) == 0)
{
if (v___x_3534_ == 0)
{
lean_object* v_options_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
lean_del_object(v___x_3590_);
v_options_3632_ = lean_ctor_get(v___y_3542_, 2);
v___x_3633_ = lean_box(v___x_3534_);
v___x_3634_ = lean_box(v___x_3531_);
v___x_3635_ = lean_box(v_compile_3532_);
v___x_3636_ = lean_box(v_logCompileErrors_3533_);
v___x_3637_ = lean_box(v_isMeta_3535_);
lean_inc(v_a_3579_);
lean_inc(v___x_3585_);
lean_inc(v___x_3573_);
v___f_3638_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3638_, 0, v___x_3573_);
lean_closure_set(v___f_3638_, 1, v___x_3585_);
lean_closure_set(v___f_3638_, 2, v___x_3582_);
lean_closure_set(v___f_3638_, 3, v_a_3579_);
lean_closure_set(v___f_3638_, 4, v___x_3633_);
lean_closure_set(v___f_3638_, 5, v___x_3634_);
lean_closure_set(v___f_3638_, 6, v___x_3635_);
lean_closure_set(v___f_3638_, 7, v___x_3636_);
lean_closure_set(v___f_3638_, 8, v___x_3637_);
v___x_3639_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3640_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3632_, v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
lean_dec_ref(v___f_3638_);
lean_dec(v_userName_3576_);
lean_inc(v___x_3585_);
v___x_3641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(v___x_3573_, v___x_3585_, v___x_3582_, v_a_3579_, v___x_3534_, v___x_3531_, v_compile_3532_, v_logCompileErrors_3533_, v_isMeta_3535_, v___x_3582_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3641_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3642_; 
lean_inc(v_userName_3576_);
lean_inc(v_val_3536_);
v___x_3642_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_3536_, v_userName_3576_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3677_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
v_fst_3644_ = lean_ctor_get(v_a_3643_, 0);
v_snd_3645_ = lean_ctor_get(v_a_3643_, 1);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3647_ = v_a_3643_;
v_isShared_3648_ = v_isSharedCheck_3677_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_snd_3645_);
lean_inc(v_fst_3644_);
lean_dec(v_a_3643_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3677_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_name_eq(v_fst_3644_, v_val_3536_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
lean_dec(v_a_3579_);
v___x_3650_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_3583_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; uint8_t v___x_3652_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = lean_unbox(v_a_3651_);
lean_dec(v_a_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; 
lean_del_object(v___x_3647_);
lean_dec(v_userName_3576_);
lean_inc_ref(v_expectedType_3537_);
lean_inc(v_val_3536_);
v___x_3653_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(v_val_3536_, v_fst_3644_, v_expectedType_3537_, v___f_3584_, v___f_3638_, v___x_3582_, v_cls_3583_, v_snd_3645_, v___x_3573_, v___x_3582_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3653_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3654_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4);
v___x_3655_ = l_Lean_MessageData_ofName(v_userName_3576_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set_tag(v___x_3647_, 7);
lean_ctor_set(v___x_3647_, 1, v___x_3655_);
lean_ctor_set(v___x_3647_, 0, v___x_3654_);
v___x_3657_ = v___x_3647_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3658_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
lean_inc(v_fst_3644_);
v___x_3660_ = l_Lean_MessageData_ofName(v_fst_3644_);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3583_, v___x_3663_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3666_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___x_3664_);
lean_inc_ref(v_expectedType_3537_);
lean_inc(v_val_3536_);
v___x_3666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(v_val_3536_, v_fst_3644_, v_expectedType_3537_, v___f_3584_, v___f_3638_, v___x_3582_, v_cls_3583_, v_snd_3645_, v___x_3573_, v_a_3665_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3666_;
goto v___jp_3550_;
}
else
{
lean_dec(v_snd_3645_);
lean_dec(v_fst_3644_);
lean_dec_ref(v___f_3638_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_del_object(v___x_3647_);
lean_dec(v_snd_3645_);
lean_dec(v_fst_3644_);
lean_dec_ref(v___f_3638_);
lean_dec(v_userName_3576_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3668_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3650_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3650_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v___x_3676_; 
lean_del_object(v___x_3647_);
lean_dec(v_snd_3645_);
lean_dec(v_fst_3644_);
lean_dec_ref(v___f_3638_);
lean_dec(v_userName_3576_);
lean_inc(v___x_3585_);
v___x_3676_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(v___x_3573_, v___x_3585_, v___x_3582_, v_a_3579_, v___x_3534_, v___x_3531_, v_compile_3532_, v_logCompileErrors_3533_, v_isMeta_3535_, v___x_3582_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3676_;
goto v___jp_3550_;
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec_ref(v___f_3638_);
lean_dec(v_a_3579_);
lean_dec(v_userName_3576_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3678_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3642_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3642_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
else
{
lean_dec(v_userName_3576_);
goto v___jp_3610_;
}
}
else
{
lean_dec_ref(v_a_3588_);
lean_dec(v_userName_3576_);
goto v___jp_3610_;
}
v___jp_3592_:
{
lean_object* v___x_3594_; 
lean_inc(v___x_3585_);
v___x_3594_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_3585_, v_a_3579_, v_compile_3532_, v_logCompileErrors_3533_, v_isMeta_3535_, v___x_3573_, v___x_3582_, v_a_3593_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3594_;
goto v___jp_3550_;
}
v___jp_3595_:
{
if (v___y_3597_ == 0)
{
lean_dec_ref(v___y_3596_);
lean_del_object(v___x_3590_);
v_a_3593_ = v___x_3582_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3599_; 
lean_dec(v_a_3579_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 1);
lean_ctor_set(v___x_3590_, 0, v___y_3596_);
v___x_3599_ = v___x_3590_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___y_3596_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
v___jp_3601_:
{
uint8_t v___x_3603_; 
v___x_3603_ = l_Lean_Exception_isInterrupt(v_a_3602_);
if (v___x_3603_ == 0)
{
uint8_t v___x_3604_; 
lean_inc_ref(v_a_3602_);
v___x_3604_ = l_Lean_Exception_isRuntime(v_a_3602_);
v___y_3596_ = v_a_3602_;
v___y_3597_ = v___x_3604_;
goto v___jp_3595_;
}
else
{
v___y_3596_ = v_a_3602_;
v___y_3597_ = v___x_3603_;
goto v___jp_3595_;
}
}
v___jp_3605_:
{
if (lean_obj_tag(v___y_3606_) == 0)
{
lean_object* v_a_3607_; 
lean_del_object(v___x_3590_);
v_a_3607_ = lean_ctor_get(v___y_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref(v___y_3606_);
if (lean_obj_tag(v_a_3607_) == 0)
{
lean_dec(v_a_3579_);
lean_dec(v___x_3573_);
v_a_3546_ = v___x_3582_;
goto v___jp_3545_;
}
else
{
lean_object* v_a_3608_; 
v_a_3608_ = lean_ctor_get(v_a_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref(v_a_3607_);
v_a_3593_ = v_a_3608_;
goto v___jp_3592_;
}
}
else
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___y_3606_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v___y_3606_);
v_a_3602_ = v_a_3609_;
goto v___jp_3601_;
}
}
v___jp_3610_:
{
lean_object* v_options_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v_options_3611_ = lean_ctor_get(v___y_3542_, 2);
v___x_3612_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3613_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3611_, v___x_3612_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; 
lean_del_object(v___x_3590_);
lean_inc(v___x_3585_);
v___x_3614_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_3585_, v_a_3579_, v_compile_3532_, v_logCompileErrors_3533_, v_isMeta_3535_, v___x_3573_, v___x_3582_, v___x_3582_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3614_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_box(0);
lean_inc(v_a_3579_);
v___x_3616_ = l_Lean_Meta_trySynthInstance(v_a_3579_, v___x_3615_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref(v___x_3616_);
if (lean_obj_tag(v_a_3617_) == 1)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; 
v_a_3618_ = lean_ctor_get(v_a_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v_a_3617_);
v___x_3619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_3583_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; uint8_t v___x_3621_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3619_);
v___x_3621_ = lean_unbox(v_a_3620_);
lean_dec(v_a_3620_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; 
lean_inc(v___x_3573_);
v___x_3622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_3573_, v_a_3618_, v___x_3582_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3606_ = v___x_3622_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3623_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2);
lean_inc(v_a_3618_);
v___x_3624_ = l_Lean_MessageData_ofExpr(v_a_3618_);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3583_, v___x_3625_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3628_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref(v___x_3626_);
lean_inc(v___x_3573_);
v___x_3628_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_3573_, v_a_3618_, v_a_3627_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3606_ = v___x_3628_;
goto v___jp_3605_;
}
else
{
lean_object* v_a_3629_; 
lean_dec(v_a_3618_);
v_a_3629_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3629_);
lean_dec_ref(v___x_3626_);
v_a_3602_ = v_a_3629_;
goto v___jp_3601_;
}
}
}
else
{
lean_object* v_a_3630_; 
lean_dec(v_a_3618_);
v_a_3630_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3619_);
v_a_3602_ = v_a_3630_;
goto v___jp_3601_;
}
}
else
{
lean_dec(v_a_3617_);
lean_del_object(v___x_3590_);
v_a_3593_ = v___x_3582_;
goto v___jp_3592_;
}
}
else
{
lean_object* v_a_3631_; 
v_a_3631_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3631_);
lean_dec_ref(v___x_3616_);
v_a_3602_ = v_a_3631_;
goto v___jp_3601_;
}
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_a_3579_);
lean_dec(v_userName_3576_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3687_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3587_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3587_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v___x_3695_; 
lean_dec(v_userName_3576_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
lean_inc(v___x_3585_);
v___x_3695_ = lean_infer_type(v___x_3585_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc_n(v_a_3696_, 2);
lean_dec_ref(v___x_3695_);
lean_inc(v_a_3579_);
v___x_3697_ = l_Lean_Meta_isExprDefEq(v_a_3579_, v_a_3696_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___f_3699_; uint8_t v___x_3700_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref(v___x_3697_);
v___f_3699_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__7));
v___x_3700_ = lean_unbox(v_a_3698_);
lean_dec(v_a_3698_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; 
v___x_3701_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_3583_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; uint8_t v___x_3703_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref(v___x_3701_);
v___x_3703_ = lean_unbox(v_a_3702_);
lean_dec(v_a_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; 
lean_dec(v_a_3696_);
lean_inc(v___x_3585_);
v___x_3704_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_3579_, v___x_3585_, v___x_3531_, v___x_3573_, v___f_3699_, v___x_3582_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3704_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3705_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9);
lean_inc(v_a_3538_);
v___x_3706_ = l_Nat_reprFast(v_a_3538_);
v___x_3707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
v___x_3708_ = l_Lean_MessageData_ofFormat(v___x_3707_);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3705_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11);
v___x_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
lean_inc(v_a_3579_);
v___x_3712_ = l_Lean_MessageData_ofExpr(v_a_3579_);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = l_Lean_MessageData_ofExpr(v_a_3696_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
lean_inc(v___x_3585_);
v___x_3720_ = l_Lean_MessageData_ofExpr(v___x_3585_);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3583_, v___x_3721_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
lean_inc(v___x_3585_);
v___x_3724_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_3579_, v___x_3585_, v___x_3531_, v___x_3573_, v___f_3699_, v_a_3723_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3724_;
goto v___jp_3550_;
}
else
{
lean_dec(v_a_3579_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
return v___x_3722_;
}
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec(v_a_3696_);
lean_dec(v_a_3579_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3725_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3701_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3701_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v___x_3733_; 
lean_dec(v_a_3696_);
lean_dec(v_a_3579_);
lean_inc(v___x_3585_);
v___x_3733_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_3573_, v___x_3585_, v___y_3541_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___x_3733_);
v___x_3735_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6(v___x_3582_, v_a_3734_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3735_;
goto v___jp_3550_;
}
else
{
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
return v___x_3733_;
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_a_3696_);
lean_dec(v_a_3579_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3736_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3697_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3697_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec(v_a_3579_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3744_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3695_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3695_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_a_3579_);
lean_dec(v_userName_3576_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3752_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3580_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3580_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec(v_userName_3576_);
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3760_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3578_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3578_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v___x_3573_);
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3768_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3574_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3574_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
v___jp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_add(v_a_3538_, v___x_3547_);
lean_dec(v_a_3538_);
v_a_3538_ = v___x_3548_;
v_b_3539_ = v_a_3546_;
goto _start;
}
v___jp_3550_:
{
if (lean_obj_tag(v___y_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3561_; 
v_a_3552_ = lean_ctor_get(v___y_3551_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___y_3551_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3554_ = v___y_3551_;
v_isShared_3555_ = v_isSharedCheck_3561_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___y_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3561_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
if (lean_obj_tag(v_a_3552_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; 
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3556_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v_a_3552_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_a_3556_);
v___x_3558_ = v___x_3554_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
else
{
lean_object* v_a_3560_; 
lean_del_object(v___x_3554_);
v_a_3560_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3560_);
lean_dec_ref(v_a_3552_);
v_a_3546_ = v_a_3560_;
goto v___jp_3545_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_a_3538_);
lean_dec_ref(v_expectedType_3537_);
lean_dec(v_val_3536_);
v_a_3562_ = lean_ctor_get(v___y_3551_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___y_3551_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___y_3551_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___y_3551_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg(lean_object* v_upperBound_3776_, lean_object* v_fst_3777_, lean_object* v_args_3778_, uint8_t v___x_3779_, uint8_t v_compile_3780_, uint8_t v_logCompileErrors_3781_, uint8_t v___x_3782_, uint8_t v_isMeta_3783_, lean_object* v_val_3784_, lean_object* v_expectedType_3785_, lean_object* v_a_3786_, lean_object* v_b_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_a_3794_; lean_object* v___y_3799_; uint8_t v___x_3818_; 
v___x_3818_ = lean_nat_dec_lt(v_a_3786_, v_upperBound_3776_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; 
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v_b_3787_);
return v___x_3819_;
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = lean_array_fget_borrowed(v_fst_3777_, v_a_3786_);
v___x_3821_ = l_Lean_Expr_mvarId_x21(v___x_3820_);
lean_inc(v___x_3821_);
v___x_3822_ = l_Lean_MVarId_getDecl(v___x_3821_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v_userName_3824_; lean_object* v_type_3825_; lean_object* v___x_3826_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref(v___x_3822_);
v_userName_3824_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_userName_3824_);
v_type_3825_ = lean_ctor_get(v_a_3823_, 2);
lean_inc_ref(v_type_3825_);
lean_dec(v_a_3823_);
v___x_3826_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(v_type_3825_, v___y_3789_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3828_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc_n(v_a_3827_, 2);
lean_dec_ref(v___x_3826_);
v___x_3828_ = l_Lean_Meta_isProp(v_a_3827_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; lean_object* v_cls_3831_; lean_object* v___f_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
v___x_3830_ = lean_box(0);
v_cls_3831_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3832_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__0));
v___x_3833_ = lean_array_fget_borrowed(v_args_3778_, v_a_3786_);
v___x_3834_ = lean_unbox(v_a_3829_);
lean_dec(v_a_3829_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; 
lean_inc(v_a_3827_);
v___x_3835_ = l_Lean_Meta_isClass_x3f(v_a_3827_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3934_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3838_ = v___x_3835_;
v_isShared_3839_ = v_isSharedCheck_3934_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3835_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3934_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v_a_3841_; lean_object* v___y_3844_; uint8_t v___y_3845_; lean_object* v_a_3850_; lean_object* v___y_3854_; 
if (lean_obj_tag(v_a_3836_) == 0)
{
if (v___x_3782_ == 0)
{
lean_object* v_options_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___f_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
lean_del_object(v___x_3838_);
v_options_3880_ = lean_ctor_get(v___y_3790_, 2);
v___x_3881_ = lean_box(v___x_3782_);
v___x_3882_ = lean_box(v___x_3779_);
v___x_3883_ = lean_box(v_compile_3780_);
v___x_3884_ = lean_box(v_logCompileErrors_3781_);
v___x_3885_ = lean_box(v_isMeta_3783_);
lean_inc(v_a_3827_);
lean_inc(v___x_3833_);
lean_inc(v___x_3821_);
v___f_3886_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3886_, 0, v___x_3821_);
lean_closure_set(v___f_3886_, 1, v___x_3833_);
lean_closure_set(v___f_3886_, 2, v___x_3830_);
lean_closure_set(v___f_3886_, 3, v_a_3827_);
lean_closure_set(v___f_3886_, 4, v___x_3881_);
lean_closure_set(v___f_3886_, 5, v___x_3882_);
lean_closure_set(v___f_3886_, 6, v___x_3883_);
lean_closure_set(v___f_3886_, 7, v___x_3884_);
lean_closure_set(v___f_3886_, 8, v___x_3885_);
v___x_3887_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3888_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3880_, v___x_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
lean_dec_ref(v___f_3886_);
lean_dec(v_userName_3824_);
lean_inc(v___x_3833_);
v___x_3889_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(v___x_3821_, v___x_3833_, v___x_3830_, v_a_3827_, v___x_3782_, v___x_3779_, v_compile_3780_, v_logCompileErrors_3781_, v_isMeta_3783_, v___x_3830_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3889_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3890_; 
lean_inc(v_userName_3824_);
lean_inc(v_val_3784_);
v___x_3890_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_3784_, v_userName_3824_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v_fst_3892_; lean_object* v_snd_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3925_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref(v___x_3890_);
v_fst_3892_ = lean_ctor_get(v_a_3891_, 0);
v_snd_3893_ = lean_ctor_get(v_a_3891_, 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_a_3891_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3895_ = v_a_3891_;
v_isShared_3896_ = v_isSharedCheck_3925_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_snd_3893_);
lean_inc(v_fst_3892_);
lean_dec(v_a_3891_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3925_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
uint8_t v___x_3897_; 
v___x_3897_ = lean_name_eq(v_fst_3892_, v_val_3784_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; 
lean_dec(v_a_3827_);
v___x_3898_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_3831_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; uint8_t v___x_3900_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = lean_unbox(v_a_3899_);
lean_dec(v_a_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
lean_del_object(v___x_3895_);
lean_dec(v_userName_3824_);
lean_inc_ref(v_expectedType_3785_);
lean_inc(v_val_3784_);
v___x_3901_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5(v_val_3784_, v_fst_3892_, v_expectedType_3785_, v___f_3832_, v___f_3886_, v___x_3830_, v_cls_3831_, v_snd_3893_, v___x_3821_, v___x_3830_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3901_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3902_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4);
v___x_3903_ = l_Lean_MessageData_ofName(v_userName_3824_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set_tag(v___x_3895_, 7);
lean_ctor_set(v___x_3895_, 1, v___x_3903_);
lean_ctor_set(v___x_3895_, 0, v___x_3902_);
v___x_3905_ = v___x_3895_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3906_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
lean_inc(v_fst_3892_);
v___x_3908_ = l_Lean_MessageData_ofName(v_fst_3892_);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3831_, v___x_3911_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref(v___x_3912_);
lean_inc_ref(v_expectedType_3785_);
lean_inc(v_val_3784_);
v___x_3914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5(v_val_3784_, v_fst_3892_, v_expectedType_3785_, v___f_3832_, v___f_3886_, v___x_3830_, v_cls_3831_, v_snd_3893_, v___x_3821_, v_a_3913_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3914_;
goto v___jp_3798_;
}
else
{
lean_dec(v_snd_3893_);
lean_dec(v_fst_3892_);
lean_dec_ref(v___f_3886_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_del_object(v___x_3895_);
lean_dec(v_snd_3893_);
lean_dec(v_fst_3892_);
lean_dec_ref(v___f_3886_);
lean_dec(v_userName_3824_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3916_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3898_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3898_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v___x_3924_; 
lean_del_object(v___x_3895_);
lean_dec(v_snd_3893_);
lean_dec(v_fst_3892_);
lean_dec_ref(v___f_3886_);
lean_dec(v_userName_3824_);
lean_inc(v___x_3833_);
v___x_3924_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1(v___x_3821_, v___x_3833_, v___x_3830_, v_a_3827_, v___x_3782_, v___x_3779_, v_compile_3780_, v_logCompileErrors_3781_, v_isMeta_3783_, v___x_3830_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3924_;
goto v___jp_3798_;
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec_ref(v___f_3886_);
lean_dec(v_a_3827_);
lean_dec(v_userName_3824_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3926_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3890_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3890_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
else
{
lean_dec(v_userName_3824_);
goto v___jp_3858_;
}
}
else
{
lean_dec_ref(v_a_3836_);
lean_dec(v_userName_3824_);
goto v___jp_3858_;
}
v___jp_3840_:
{
lean_object* v___x_3842_; 
lean_inc(v___x_3833_);
v___x_3842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_3833_, v_a_3827_, v_compile_3780_, v_logCompileErrors_3781_, v_isMeta_3783_, v___x_3821_, v___x_3830_, v_a_3841_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3842_;
goto v___jp_3798_;
}
v___jp_3843_:
{
if (v___y_3845_ == 0)
{
lean_dec_ref(v___y_3844_);
lean_del_object(v___x_3838_);
v_a_3841_ = v___x_3830_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3847_; 
lean_dec(v_a_3827_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set_tag(v___x_3838_, 1);
lean_ctor_set(v___x_3838_, 0, v___y_3844_);
v___x_3847_ = v___x_3838_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___y_3844_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
v___jp_3849_:
{
uint8_t v___x_3851_; 
v___x_3851_ = l_Lean_Exception_isInterrupt(v_a_3850_);
if (v___x_3851_ == 0)
{
uint8_t v___x_3852_; 
lean_inc_ref(v_a_3850_);
v___x_3852_ = l_Lean_Exception_isRuntime(v_a_3850_);
v___y_3844_ = v_a_3850_;
v___y_3845_ = v___x_3852_;
goto v___jp_3843_;
}
else
{
v___y_3844_ = v_a_3850_;
v___y_3845_ = v___x_3851_;
goto v___jp_3843_;
}
}
v___jp_3853_:
{
if (lean_obj_tag(v___y_3854_) == 0)
{
lean_object* v_a_3855_; 
lean_del_object(v___x_3838_);
v_a_3855_ = lean_ctor_get(v___y_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___y_3854_);
if (lean_obj_tag(v_a_3855_) == 0)
{
lean_dec(v_a_3827_);
lean_dec(v___x_3821_);
v_a_3794_ = v___x_3830_;
goto v___jp_3793_;
}
else
{
lean_object* v_a_3856_; 
v_a_3856_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref(v_a_3855_);
v_a_3841_ = v_a_3856_;
goto v___jp_3840_;
}
}
else
{
lean_object* v_a_3857_; 
v_a_3857_ = lean_ctor_get(v___y_3854_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___y_3854_);
v_a_3850_ = v_a_3857_;
goto v___jp_3849_;
}
}
v___jp_3858_:
{
lean_object* v_options_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
v_options_3859_ = lean_ctor_get(v___y_3790_, 2);
v___x_3860_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3861_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3859_, v___x_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; 
lean_del_object(v___x_3838_);
lean_inc(v___x_3833_);
v___x_3862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_3833_, v_a_3827_, v_compile_3780_, v_logCompileErrors_3781_, v_isMeta_3783_, v___x_3821_, v___x_3830_, v___x_3830_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3862_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_box(0);
lean_inc(v_a_3827_);
v___x_3864_ = l_Lean_Meta_trySynthInstance(v_a_3827_, v___x_3863_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref(v___x_3864_);
if (lean_obj_tag(v_a_3865_) == 1)
{
lean_object* v_a_3866_; lean_object* v___x_3867_; 
v_a_3866_ = lean_ctor_get(v_a_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v_a_3865_);
v___x_3867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_3831_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; uint8_t v___x_3869_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3867_);
v___x_3869_ = lean_unbox(v_a_3868_);
lean_dec(v_a_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; 
lean_inc(v___x_3821_);
v___x_3870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_3821_, v_a_3866_, v___x_3830_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3854_ = v___x_3870_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3871_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2);
lean_inc(v_a_3866_);
v___x_3872_ = l_Lean_MessageData_ofExpr(v_a_3866_);
v___x_3873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3831_, v___x_3873_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
lean_inc(v___x_3821_);
v___x_3876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_3821_, v_a_3866_, v_a_3875_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3854_ = v___x_3876_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3877_; 
lean_dec(v_a_3866_);
v_a_3877_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3877_);
lean_dec_ref(v___x_3874_);
v_a_3850_ = v_a_3877_;
goto v___jp_3849_;
}
}
}
else
{
lean_object* v_a_3878_; 
lean_dec(v_a_3866_);
v_a_3878_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3878_);
lean_dec_ref(v___x_3867_);
v_a_3850_ = v_a_3878_;
goto v___jp_3849_;
}
}
else
{
lean_dec(v_a_3865_);
lean_del_object(v___x_3838_);
v_a_3841_ = v___x_3830_;
goto v___jp_3840_;
}
}
else
{
lean_object* v_a_3879_; 
v_a_3879_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3879_);
lean_dec_ref(v___x_3864_);
v_a_3850_ = v_a_3879_;
goto v___jp_3849_;
}
}
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec(v_a_3827_);
lean_dec(v_userName_3824_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3935_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3835_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3835_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v___x_3943_; 
lean_dec(v_userName_3824_);
lean_inc(v___y_3791_);
lean_inc_ref(v___y_3790_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
lean_inc(v___x_3833_);
v___x_3943_ = lean_infer_type(v___x_3833_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc_n(v_a_3944_, 2);
lean_dec_ref(v___x_3943_);
lean_inc(v_a_3827_);
v___x_3945_ = l_Lean_Meta_isExprDefEq(v_a_3827_, v_a_3944_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___f_3947_; uint8_t v___x_3948_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref(v___x_3945_);
v___f_3947_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__7));
v___x_3948_ = lean_unbox(v_a_3946_);
lean_dec(v_a_3946_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
v___x_3949_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_3831_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; uint8_t v___x_3951_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref(v___x_3949_);
v___x_3951_ = lean_unbox(v_a_3950_);
lean_dec(v_a_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; 
lean_dec(v_a_3944_);
lean_inc(v___x_3833_);
v___x_3952_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_3827_, v___x_3833_, v___x_3779_, v___x_3821_, v___f_3947_, v___x_3830_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3952_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3953_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9);
lean_inc(v_a_3786_);
v___x_3954_ = l_Nat_reprFast(v_a_3786_);
v___x_3955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
v___x_3956_ = l_Lean_MessageData_ofFormat(v___x_3955_);
v___x_3957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3953_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11);
v___x_3959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
lean_inc(v_a_3827_);
v___x_3960_ = l_Lean_MessageData_ofExpr(v_a_3827_);
v___x_3961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13);
v___x_3963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3961_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = l_Lean_MessageData_ofExpr(v_a_3944_);
v___x_3965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3963_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15);
v___x_3967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
lean_inc(v___x_3833_);
v___x_3968_ = l_Lean_MessageData_ofExpr(v___x_3833_);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_3831_, v___x_3969_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3972_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___x_3970_);
lean_inc(v___x_3833_);
v___x_3972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_3827_, v___x_3833_, v___x_3779_, v___x_3821_, v___f_3947_, v_a_3971_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3972_;
goto v___jp_3798_;
}
else
{
lean_dec(v_a_3827_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
return v___x_3970_;
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec(v_a_3944_);
lean_dec(v_a_3827_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3973_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3949_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3949_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v___x_3981_; 
lean_dec(v_a_3944_);
lean_dec(v_a_3827_);
lean_inc(v___x_3833_);
v___x_3981_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_3821_, v___x_3833_, v___y_3789_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref(v___x_3981_);
v___x_3983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6(v___x_3830_, v_a_3982_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v___y_3799_ = v___x_3983_;
goto v___jp_3798_;
}
else
{
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
return v___x_3981_;
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v_a_3944_);
lean_dec(v_a_3827_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3984_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3945_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3945_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v_a_3827_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3992_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3943_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3943_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_a_3827_);
lean_dec(v_userName_3824_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_4000_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3828_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3828_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v_userName_3824_);
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_4008_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3826_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3826_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v___x_3821_);
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_4016_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3822_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3822_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
v___jp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_unsigned_to_nat(1u);
v___x_3796_ = lean_nat_add(v_a_3786_, v___x_3795_);
lean_dec(v_a_3786_);
v___x_3797_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___redArg(v_upperBound_3776_, v_fst_3777_, v_args_3778_, v___x_3779_, v_compile_3780_, v_logCompileErrors_3781_, v___x_3782_, v_isMeta_3783_, v_val_3784_, v_expectedType_3785_, v___x_3796_, v_a_3794_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
return v___x_3797_;
}
v___jp_3798_:
{
if (lean_obj_tag(v___y_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3809_; 
v_a_3800_ = lean_ctor_get(v___y_3799_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___y_3799_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3802_ = v___y_3799_;
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___y_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
if (lean_obj_tag(v_a_3800_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; 
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3804_ = lean_ctor_get(v_a_3800_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v_a_3800_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v_a_3804_);
v___x_3806_ = v___x_3802_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
else
{
lean_object* v_a_3808_; 
lean_del_object(v___x_3802_);
v_a_3808_ = lean_ctor_get(v_a_3800_, 0);
lean_inc(v_a_3808_);
lean_dec_ref(v_a_3800_);
v_a_3794_ = v_a_3808_;
goto v___jp_3793_;
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v_a_3786_);
lean_dec_ref(v_expectedType_3785_);
lean_dec(v_val_3784_);
v_a_3810_ = lean_ctor_get(v___y_3799_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___y_3799_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___y_3799_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___y_3799_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21(lean_object* v_inst_4024_, lean_object* v_expectedType_4025_, uint8_t v___x_4026_, uint8_t v___x_4027_, uint8_t v_compile_4028_, uint8_t v_logCompileErrors_4029_, uint8_t v_isMeta_4030_, lean_object* v_val_4031_, lean_object* v_x_4032_, lean_object* v_x_4033_, lean_object* v_x_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v_options_4083_; lean_object* v___y_4084_; 
if (lean_obj_tag(v_x_4032_) == 5)
{
lean_object* v_fn_4149_; lean_object* v_arg_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_fn_4149_ = lean_ctor_get(v_x_4032_, 0);
lean_inc_ref(v_fn_4149_);
v_arg_4150_ = lean_ctor_get(v_x_4032_, 1);
lean_inc_ref(v_arg_4150_);
lean_dec_ref(v_x_4032_);
v___x_4151_ = lean_array_set(v_x_4033_, v_x_4034_, v_arg_4150_);
v___x_4152_ = lean_unsigned_to_nat(1u);
v___x_4153_ = lean_nat_sub(v_x_4034_, v___x_4152_);
lean_dec(v_x_4034_);
v_x_4032_ = v_fn_4149_;
v_x_4033_ = v___x_4151_;
v_x_4034_ = v___x_4153_;
goto _start;
}
else
{
lean_object* v_cls_4155_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___x_4178_; 
lean_dec(v_x_4034_);
v_cls_4155_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4178_ = l_Lean_Expr_constName_x3f(v_x_4032_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_dec_ref(v_x_4033_);
lean_dec_ref(v_x_4032_);
lean_dec(v_val_4031_);
v___y_4157_ = v___y_4035_;
v___y_4158_ = v___y_4036_;
v___y_4159_ = v___y_4037_;
v___y_4160_ = v___y_4038_;
goto v___jp_4156_;
}
else
{
lean_object* v_val_4179_; lean_object* v___x_4180_; 
v_val_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_val_4179_);
lean_dec_ref(v___x_4178_);
v___x_4180_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(v_val_4179_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref(v___x_4180_);
if (lean_obj_tag(v_a_4181_) == 6)
{
lean_object* v_val_4182_; lean_object* v___x_4183_; 
lean_dec_ref(v_inst_4024_);
v_val_4182_ = lean_ctor_get(v_a_4181_, 0);
lean_inc_ref(v_val_4182_);
lean_dec_ref(v_a_4181_);
lean_inc(v___y_4038_);
lean_inc_ref(v___y_4037_);
lean_inc(v___y_4036_);
lean_inc_ref(v___y_4035_);
lean_inc_ref(v_x_4032_);
v___x_4183_ = lean_infer_type(v_x_4032_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; uint8_t v___x_4185_; lean_object* v___x_4186_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref(v___x_4183_);
v___x_4185_ = 0;
v___x_4186_ = l_Lean_Meta_forallMetaTelescope(v_a_4184_, v___x_4185_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v_snd_4188_; lean_object* v_fst_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4288_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref(v___x_4186_);
v_snd_4188_ = lean_ctor_get(v_a_4187_, 1);
v_fst_4189_ = lean_ctor_get(v_a_4187_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_a_4187_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4191_ = v_a_4187_;
v_isShared_4192_ = v_isSharedCheck_4288_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_snd_4188_);
lean_inc(v_fst_4189_);
lean_dec(v_a_4187_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4288_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v_snd_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4286_; 
v_snd_4193_ = lean_ctor_get(v_snd_4188_, 1);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_snd_4188_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; 
v_unused_4287_ = lean_ctor_get(v_snd_4188_, 0);
lean_dec(v_unused_4287_);
v___x_4195_ = v_snd_4188_;
v_isShared_4196_ = v_isSharedCheck_4286_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_snd_4193_);
lean_dec(v_snd_4188_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4286_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___x_4234_; uint8_t v___x_4235_; 
v___x_4197_ = lean_array_get_size(v_x_4033_);
v___x_4234_ = lean_array_get_size(v_fst_4189_);
v___x_4235_ = lean_nat_dec_eq(v___x_4197_, v___x_4234_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
lean_dec(v_snd_4193_);
lean_dec(v_fst_4189_);
lean_dec_ref(v_val_4182_);
lean_dec(v_val_4031_);
lean_dec_ref(v_expectedType_4025_);
v___x_4236_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3);
v___x_4237_ = l_Lean_MessageData_ofExpr(v_x_4032_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 7);
lean_ctor_set(v___x_4195_, 1, v___x_4237_);
lean_ctor_set(v___x_4195_, 0, v___x_4236_);
v___x_4239_ = v___x_4195_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4236_);
lean_ctor_set(v_reuseFailAlloc_4250_, 1, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4242_; 
v___x_4240_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
if (v_isShared_4192_ == 0)
{
lean_ctor_set_tag(v___x_4191_, 7);
lean_ctor_set(v___x_4191_, 1, v___x_4240_);
lean_ctor_set(v___x_4191_, 0, v___x_4239_);
v___x_4242_ = v___x_4191_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4243_ = lean_array_to_list(v_x_4033_);
v___x_4244_ = lean_box(0);
v___x_4245_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_4243_, v___x_4244_);
v___x_4246_ = l_Lean_MessageData_ofList(v___x_4245_);
v___x_4247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4242_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4247_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4248_;
}
}
}
else
{
lean_object* v___x_4251_; 
lean_inc_ref(v_expectedType_4025_);
v___x_4251_ = l_Lean_Meta_isExprDefEq(v_expectedType_4025_, v_snd_4193_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; uint8_t v___x_4253_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref(v___x_4251_);
v___x_4253_ = lean_unbox(v_a_4252_);
lean_dec(v_a_4252_);
if (v___x_4253_ == 0)
{
lean_object* v_toConstantVal_4254_; lean_object* v_name_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4259_; 
lean_dec(v_fst_4189_);
lean_dec_ref(v_x_4033_);
lean_dec_ref(v_x_4032_);
lean_dec(v_val_4031_);
v_toConstantVal_4254_ = lean_ctor_get(v_val_4182_, 0);
lean_inc_ref(v_toConstantVal_4254_);
lean_dec_ref(v_val_4182_);
v_name_4255_ = lean_ctor_get(v_toConstantVal_4254_, 0);
lean_inc(v_name_4255_);
lean_dec_ref(v_toConstantVal_4254_);
v___x_4256_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5);
v___x_4257_ = l_Lean_MessageData_ofExpr(v_expectedType_4025_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 7);
lean_ctor_set(v___x_4195_, 1, v___x_4257_);
lean_ctor_set(v___x_4195_, 0, v___x_4256_);
v___x_4259_ = v___x_4195_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4256_);
lean_ctor_set(v_reuseFailAlloc_4277_, 1, v___x_4257_);
v___x_4259_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4260_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7);
if (v_isShared_4192_ == 0)
{
lean_ctor_set_tag(v___x_4191_, 7);
lean_ctor_set(v___x_4191_, 1, v___x_4260_);
lean_ctor_set(v___x_4191_, 0, v___x_4259_);
v___x_4262_ = v___x_4191_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4276_, 1, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
v___x_4263_ = l_Lean_MessageData_ofConstName(v_name_4255_, v___x_4026_);
v___x_4264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4264_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4266_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4267_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4267_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
else
{
lean_del_object(v___x_4195_);
lean_del_object(v___x_4191_);
v___y_4199_ = v___y_4035_;
v___y_4200_ = v___y_4036_;
v___y_4201_ = v___y_4037_;
v___y_4202_ = v___y_4038_;
goto v___jp_4198_;
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_del_object(v___x_4195_);
lean_del_object(v___x_4191_);
lean_dec(v_fst_4189_);
lean_dec_ref(v_val_4182_);
lean_dec_ref(v_x_4033_);
lean_dec_ref(v_x_4032_);
lean_dec(v_val_4031_);
lean_dec_ref(v_expectedType_4025_);
v_a_4278_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4251_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4251_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
v___jp_4198_:
{
lean_object* v_numParams_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_numParams_4203_ = lean_ctor_get(v_val_4182_, 3);
lean_inc(v_numParams_4203_);
lean_dec_ref(v_val_4182_);
v___x_4204_ = lean_box(0);
v___x_4205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg(v___x_4197_, v_fst_4189_, v_x_4033_, v___x_4027_, v_compile_4028_, v_logCompileErrors_4029_, v___x_4026_, v_isMeta_4030_, v_val_4031_, v_expectedType_4025_, v_numParams_4203_, v___x_4204_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec_ref(v_x_4033_);
if (lean_obj_tag(v___x_4205_) == 0)
{
size_t v_sz_4206_; size_t v___x_4207_; lean_object* v___x_4208_; 
lean_dec_ref(v___x_4205_);
v_sz_4206_ = lean_array_size(v_fst_4189_);
v___x_4207_ = ((size_t)0ULL);
v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_4206_, v___x_4207_, v_fst_4189_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4217_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4217_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4217_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
v___x_4213_ = l_Lean_mkAppN(v_x_4032_, v_a_4209_);
lean_dec(v_a_4209_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4213_);
v___x_4215_ = v___x_4211_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_dec_ref(v_x_4032_);
v_a_4218_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4208_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4208_);
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
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec(v_fst_4189_);
lean_dec_ref(v_x_4032_);
v_a_4226_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4205_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4205_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec_ref(v_val_4182_);
lean_dec_ref(v_x_4033_);
lean_dec_ref(v_x_4032_);
lean_dec(v_val_4031_);
lean_dec_ref(v_expectedType_4025_);
v_a_4289_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4186_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4186_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_dec_ref(v_val_4182_);
lean_dec_ref(v_x_4033_);
lean_dec_ref(v_x_4032_);
lean_dec(v_val_4031_);
lean_dec_ref(v_expectedType_4025_);
return v___x_4183_;
}
}
else
{
lean_dec(v_a_4181_);
lean_dec_ref(v_x_4033_);
lean_dec_ref(v_x_4032_);
lean_dec(v_val_4031_);
v___y_4157_ = v___y_4035_;
v___y_4158_ = v___y_4036_;
v___y_4159_ = v___y_4037_;
v___y_4160_ = v___y_4038_;
goto v___jp_4156_;
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec_ref(v_x_4033_);
lean_dec_ref(v_x_4032_);
lean_dec(v_val_4031_);
lean_dec_ref(v_expectedType_4025_);
lean_dec_ref(v_inst_4024_);
v_a_4297_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4180_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4180_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
v___jp_4156_:
{
lean_object* v_options_4161_; uint8_t v_hasTrace_4162_; 
v_options_4161_ = lean_ctor_get(v___y_4159_, 2);
v_hasTrace_4162_ = lean_ctor_get_uint8(v_options_4161_, sizeof(void*)*1);
if (v_hasTrace_4162_ == 0)
{
v___y_4080_ = v___y_4157_;
v___y_4081_ = v___y_4158_;
v___y_4082_ = v___y_4159_;
v_options_4083_ = v_options_4161_;
v___y_4084_ = v___y_4160_;
goto v___jp_4079_;
}
else
{
lean_object* v_inheritedTraceOptions_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v_inheritedTraceOptions_4163_ = lean_ctor_get(v___y_4159_, 13);
v___x_4164_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_4165_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4163_, v_options_4161_, v___x_4164_);
if (v___x_4165_ == 0)
{
v___y_4080_ = v___y_4157_;
v___y_4081_ = v___y_4158_;
v___y_4082_ = v___y_4159_;
v_options_4083_ = v_options_4161_;
v___y_4084_ = v___y_4160_;
goto v___jp_4079_;
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4166_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1);
lean_inc_ref(v_inst_4024_);
v___x_4167_ = l_Lean_MessageData_ofExpr(v_inst_4024_);
v___x_4168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_4155_, v___x_4168_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_dec_ref(v___x_4169_);
v___y_4080_ = v___y_4157_;
v___y_4081_ = v___y_4158_;
v___y_4082_ = v___y_4159_;
v_options_4083_ = v_options_4161_;
v___y_4084_ = v___y_4160_;
goto v___jp_4079_;
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v_expectedType_4025_);
lean_dec_ref(v_inst_4024_);
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
}
}
v___jp_4040_:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_enableRealizationsForConst(v___y_4042_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4052_ == 0)
{
lean_object* v_unused_4053_; 
v_unused_4053_ = lean_ctor_get(v___x_4045_, 0);
lean_dec(v_unused_4053_);
v___x_4047_ = v___x_4045_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_dec(v___x_4045_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___y_4041_);
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___y_4041_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec_ref(v___y_4041_);
v_a_4054_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4045_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4045_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
v___jp_4062_:
{
if (v_compile_4028_ == 0)
{
v___y_4041_ = v___y_4063_;
v___y_4042_ = v___y_4064_;
v___y_4043_ = v___y_4065_;
v___y_4044_ = v___y_4066_;
goto v___jp_4040_;
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4067_ = lean_unsigned_to_nat(1u);
v___x_4068_ = lean_mk_empty_array_with_capacity(v___x_4067_);
lean_inc(v___y_4064_);
v___x_4069_ = lean_array_push(v___x_4068_, v___y_4064_);
v___x_4070_ = l_Lean_compileDecls(v___x_4069_, v_logCompileErrors_4029_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_dec_ref(v___x_4070_);
v___y_4041_ = v___y_4063_;
v___y_4042_ = v___y_4064_;
v___y_4043_ = v___y_4065_;
v___y_4044_ = v___y_4066_;
goto v___jp_4040_;
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4070_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4070_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
v___jp_4079_:
{
lean_object* v___x_4085_; uint8_t v___x_4086_; 
v___x_4085_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4086_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4083_, v___x_4085_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; 
lean_dec_ref(v_expectedType_4025_);
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v_inst_4024_);
return v___x_4087_;
}
else
{
lean_object* v___x_4088_; 
lean_inc(v___y_4084_);
lean_inc_ref(v___y_4082_);
lean_inc(v___y_4081_);
lean_inc_ref(v___y_4080_);
lean_inc_ref(v_inst_4024_);
v___x_4088_ = lean_infer_type(v_inst_4024_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4084_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4090_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref(v___x_4088_);
lean_inc_ref(v_expectedType_4025_);
v___x_4090_ = l_Lean_Meta_isExprDefEq(v_expectedType_4025_, v_a_4089_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4084_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4140_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4140_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4140_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
uint8_t v___x_4095_; 
v___x_4095_ = lean_unbox(v_a_4091_);
lean_dec(v_a_4091_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v_a_4098_; lean_object* v___x_4099_; 
lean_del_object(v___x_4093_);
v___x_4096_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_4097_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4096_, v___y_4084_);
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc_n(v_a_4098_, 2);
lean_dec_ref(v___x_4097_);
v___x_4099_ = l_Lean_Meta_mkAuxDefinition(v_a_4098_, v_expectedType_4025_, v_inst_4024_, v___x_4026_, v___x_4026_, v___x_4027_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4084_);
if (lean_obj_tag(v___x_4099_) == 0)
{
if (v_isMeta_4030_ == 0)
{
lean_object* v_a_4100_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v___x_4099_);
v___y_4063_ = v_a_4100_;
v___y_4064_ = v_a_4098_;
v___y_4065_ = v___y_4082_;
v___y_4066_ = v___y_4084_;
goto v___jp_4062_;
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4102_; lean_object* v_env_4103_; lean_object* v_nextMacroScope_4104_; lean_object* v_ngen_4105_; lean_object* v_auxDeclNGen_4106_; lean_object* v_traceState_4107_; lean_object* v_messages_4108_; lean_object* v_infoState_4109_; lean_object* v_snapshotTasks_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4135_; 
v_a_4101_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4101_);
lean_dec_ref(v___x_4099_);
v___x_4102_ = lean_st_ref_take(v___y_4084_);
v_env_4103_ = lean_ctor_get(v___x_4102_, 0);
v_nextMacroScope_4104_ = lean_ctor_get(v___x_4102_, 1);
v_ngen_4105_ = lean_ctor_get(v___x_4102_, 2);
v_auxDeclNGen_4106_ = lean_ctor_get(v___x_4102_, 3);
v_traceState_4107_ = lean_ctor_get(v___x_4102_, 4);
v_messages_4108_ = lean_ctor_get(v___x_4102_, 6);
v_infoState_4109_ = lean_ctor_get(v___x_4102_, 7);
v_snapshotTasks_4110_ = lean_ctor_get(v___x_4102_, 8);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; 
v_unused_4136_ = lean_ctor_get(v___x_4102_, 5);
lean_dec(v_unused_4136_);
v___x_4112_ = v___x_4102_;
v_isShared_4113_ = v_isSharedCheck_4135_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_snapshotTasks_4110_);
lean_inc(v_infoState_4109_);
lean_inc(v_messages_4108_);
lean_inc(v_traceState_4107_);
lean_inc(v_auxDeclNGen_4106_);
lean_inc(v_ngen_4105_);
lean_inc(v_nextMacroScope_4104_);
lean_inc(v_env_4103_);
lean_dec(v___x_4102_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4135_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4117_; 
lean_inc(v_a_4098_);
v___x_4114_ = l_Lean_markMeta(v_env_4103_, v_a_4098_);
v___x_4115_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 5, v___x_4115_);
lean_ctor_set(v___x_4112_, 0, v___x_4114_);
v___x_4117_ = v___x_4112_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4114_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_nextMacroScope_4104_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_ngen_4105_);
lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_auxDeclNGen_4106_);
lean_ctor_set(v_reuseFailAlloc_4134_, 4, v_traceState_4107_);
lean_ctor_set(v_reuseFailAlloc_4134_, 5, v___x_4115_);
lean_ctor_set(v_reuseFailAlloc_4134_, 6, v_messages_4108_);
lean_ctor_set(v_reuseFailAlloc_4134_, 7, v_infoState_4109_);
lean_ctor_set(v_reuseFailAlloc_4134_, 8, v_snapshotTasks_4110_);
v___x_4117_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v_mctx_4120_; lean_object* v_zetaDeltaFVarIds_4121_; lean_object* v_postponed_4122_; lean_object* v_diag_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4132_; 
v___x_4118_ = lean_st_ref_set(v___y_4084_, v___x_4117_);
v___x_4119_ = lean_st_ref_take(v___y_4081_);
v_mctx_4120_ = lean_ctor_get(v___x_4119_, 0);
v_zetaDeltaFVarIds_4121_ = lean_ctor_get(v___x_4119_, 2);
v_postponed_4122_ = lean_ctor_get(v___x_4119_, 3);
v_diag_4123_ = lean_ctor_get(v___x_4119_, 4);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; 
v_unused_4133_ = lean_ctor_get(v___x_4119_, 1);
lean_dec(v_unused_4133_);
v___x_4125_ = v___x_4119_;
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_diag_4123_);
lean_inc(v_postponed_4122_);
lean_inc(v_zetaDeltaFVarIds_4121_);
lean_inc(v_mctx_4120_);
lean_dec(v___x_4119_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4129_; 
v___x_4127_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___x_4127_);
v___x_4129_ = v___x_4125_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_mctx_4120_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_zetaDeltaFVarIds_4121_);
lean_ctor_set(v_reuseFailAlloc_4131_, 3, v_postponed_4122_);
lean_ctor_set(v_reuseFailAlloc_4131_, 4, v_diag_4123_);
v___x_4129_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_st_ref_set(v___y_4081_, v___x_4129_);
v___y_4063_ = v_a_4101_;
v___y_4064_ = v_a_4098_;
v___y_4065_ = v___y_4082_;
v___y_4066_ = v___y_4084_;
goto v___jp_4062_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4098_);
return v___x_4099_;
}
}
else
{
lean_object* v___x_4138_; 
lean_dec_ref(v_expectedType_4025_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 0, v_inst_4024_);
v___x_4138_ = v___x_4093_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_inst_4024_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v_expectedType_4025_);
lean_dec_ref(v_inst_4024_);
v_a_4141_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4090_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4090_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4025_);
lean_dec_ref(v_inst_4024_);
return v___x_4088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13(lean_object* v_inst_4305_, lean_object* v_expectedType_4306_, uint8_t v___x_4307_, uint8_t v___x_4308_, uint8_t v_compile_4309_, uint8_t v_logCompileErrors_4310_, uint8_t v_isMeta_4311_, lean_object* v_val_4312_, lean_object* v_x_4313_, lean_object* v_x_4314_, lean_object* v_x_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v_options_4364_; lean_object* v___y_4365_; 
if (lean_obj_tag(v_x_4313_) == 5)
{
lean_object* v_fn_4430_; lean_object* v_arg_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_fn_4430_ = lean_ctor_get(v_x_4313_, 0);
lean_inc_ref(v_fn_4430_);
v_arg_4431_ = lean_ctor_get(v_x_4313_, 1);
lean_inc_ref(v_arg_4431_);
lean_dec_ref(v_x_4313_);
v___x_4432_ = lean_array_set(v_x_4314_, v_x_4315_, v_arg_4431_);
v___x_4433_ = lean_unsigned_to_nat(1u);
v___x_4434_ = lean_nat_sub(v_x_4315_, v___x_4433_);
v___x_4435_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21(v_inst_4305_, v_expectedType_4306_, v___x_4307_, v___x_4308_, v_compile_4309_, v_logCompileErrors_4310_, v_isMeta_4311_, v_val_4312_, v_fn_4430_, v___x_4432_, v___x_4434_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
return v___x_4435_;
}
else
{
lean_object* v_cls_4436_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___x_4459_; 
v_cls_4436_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4459_ = l_Lean_Expr_constName_x3f(v_x_4313_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_dec_ref(v_x_4314_);
lean_dec_ref(v_x_4313_);
lean_dec(v_val_4312_);
v___y_4438_ = v___y_4316_;
v___y_4439_ = v___y_4317_;
v___y_4440_ = v___y_4318_;
v___y_4441_ = v___y_4319_;
goto v___jp_4437_;
}
else
{
lean_object* v_val_4460_; lean_object* v___x_4461_; 
v_val_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_val_4460_);
lean_dec_ref(v___x_4459_);
v___x_4461_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(v_val_4460_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref(v___x_4461_);
if (lean_obj_tag(v_a_4462_) == 6)
{
lean_object* v_val_4463_; lean_object* v___x_4464_; 
lean_dec_ref(v_inst_4305_);
v_val_4463_ = lean_ctor_get(v_a_4462_, 0);
lean_inc_ref(v_val_4463_);
lean_dec_ref(v_a_4462_);
lean_inc(v___y_4319_);
lean_inc_ref(v___y_4318_);
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
lean_inc_ref(v_x_4313_);
v___x_4464_ = lean_infer_type(v_x_4313_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v_a_4465_; uint8_t v___x_4466_; lean_object* v___x_4467_; 
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4465_);
lean_dec_ref(v___x_4464_);
v___x_4466_ = 0;
v___x_4467_ = l_Lean_Meta_forallMetaTelescope(v_a_4465_, v___x_4466_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v_snd_4469_; lean_object* v_fst_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4569_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref(v___x_4467_);
v_snd_4469_ = lean_ctor_get(v_a_4468_, 1);
v_fst_4470_ = lean_ctor_get(v_a_4468_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_a_4468_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4472_ = v_a_4468_;
v_isShared_4473_ = v_isSharedCheck_4569_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_snd_4469_);
lean_inc(v_fst_4470_);
lean_dec(v_a_4468_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4569_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v_snd_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4567_; 
v_snd_4474_ = lean_ctor_get(v_snd_4469_, 1);
v_isSharedCheck_4567_ = !lean_is_exclusive(v_snd_4469_);
if (v_isSharedCheck_4567_ == 0)
{
lean_object* v_unused_4568_; 
v_unused_4568_ = lean_ctor_get(v_snd_4469_, 0);
lean_dec(v_unused_4568_);
v___x_4476_ = v_snd_4469_;
v_isShared_4477_ = v_isSharedCheck_4567_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_snd_4474_);
lean_dec(v_snd_4469_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4567_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4478_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4478_ = lean_array_get_size(v_x_4314_);
v___x_4515_ = lean_array_get_size(v_fst_4470_);
v___x_4516_ = lean_nat_dec_eq(v___x_4478_, v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
lean_dec(v_snd_4474_);
lean_dec(v_fst_4470_);
lean_dec_ref(v_val_4463_);
lean_dec(v_val_4312_);
lean_dec_ref(v_expectedType_4306_);
v___x_4517_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3);
v___x_4518_ = l_Lean_MessageData_ofExpr(v_x_4313_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set_tag(v___x_4476_, 7);
lean_ctor_set(v___x_4476_, 1, v___x_4518_);
lean_ctor_set(v___x_4476_, 0, v___x_4517_);
v___x_4520_ = v___x_4476_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4517_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v___x_4518_);
v___x_4520_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
if (v_isShared_4473_ == 0)
{
lean_ctor_set_tag(v___x_4472_, 7);
lean_ctor_set(v___x_4472_, 1, v___x_4521_);
lean_ctor_set(v___x_4472_, 0, v___x_4520_);
v___x_4523_ = v___x_4472_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4530_, 1, v___x_4521_);
v___x_4523_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4524_ = lean_array_to_list(v_x_4314_);
v___x_4525_ = lean_box(0);
v___x_4526_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_4524_, v___x_4525_);
v___x_4527_ = l_Lean_MessageData_ofList(v___x_4526_);
v___x_4528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4523_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4528_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
return v___x_4529_;
}
}
}
else
{
lean_object* v___x_4532_; 
lean_inc_ref(v_expectedType_4306_);
v___x_4532_ = l_Lean_Meta_isExprDefEq(v_expectedType_4306_, v_snd_4474_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; uint8_t v___x_4534_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref(v___x_4532_);
v___x_4534_ = lean_unbox(v_a_4533_);
lean_dec(v_a_4533_);
if (v___x_4534_ == 0)
{
lean_object* v_toConstantVal_4535_; lean_object* v_name_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4540_; 
lean_dec(v_fst_4470_);
lean_dec_ref(v_x_4314_);
lean_dec_ref(v_x_4313_);
lean_dec(v_val_4312_);
v_toConstantVal_4535_ = lean_ctor_get(v_val_4463_, 0);
lean_inc_ref(v_toConstantVal_4535_);
lean_dec_ref(v_val_4463_);
v_name_4536_ = lean_ctor_get(v_toConstantVal_4535_, 0);
lean_inc(v_name_4536_);
lean_dec_ref(v_toConstantVal_4535_);
v___x_4537_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5);
v___x_4538_ = l_Lean_MessageData_ofExpr(v_expectedType_4306_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set_tag(v___x_4476_, 7);
lean_ctor_set(v___x_4476_, 1, v___x_4538_);
lean_ctor_set(v___x_4476_, 0, v___x_4537_);
v___x_4540_ = v___x_4476_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v___x_4538_);
v___x_4540_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; lean_object* v___x_4543_; 
v___x_4541_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7);
if (v_isShared_4473_ == 0)
{
lean_ctor_set_tag(v___x_4472_, 7);
lean_ctor_set(v___x_4472_, 1, v___x_4541_);
lean_ctor_set(v___x_4472_, 0, v___x_4540_);
v___x_4543_ = v___x_4472_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4540_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v___x_4541_);
v___x_4543_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
v___x_4544_ = l_Lean_MessageData_ofConstName(v_name_4536_, v___x_4307_);
v___x_4545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4543_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
v___x_4546_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4545_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4547_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
else
{
lean_del_object(v___x_4476_);
lean_del_object(v___x_4472_);
v___y_4480_ = v___y_4316_;
v___y_4481_ = v___y_4317_;
v___y_4482_ = v___y_4318_;
v___y_4483_ = v___y_4319_;
goto v___jp_4479_;
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_del_object(v___x_4476_);
lean_del_object(v___x_4472_);
lean_dec(v_fst_4470_);
lean_dec_ref(v_val_4463_);
lean_dec_ref(v_x_4314_);
lean_dec_ref(v_x_4313_);
lean_dec(v_val_4312_);
lean_dec_ref(v_expectedType_4306_);
v_a_4559_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4532_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4532_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
v___jp_4479_:
{
lean_object* v_numParams_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_numParams_4484_ = lean_ctor_get(v_val_4463_, 3);
lean_inc(v_numParams_4484_);
lean_dec_ref(v_val_4463_);
v___x_4485_ = lean_box(0);
v___x_4486_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg(v___x_4478_, v_fst_4470_, v_x_4314_, v___x_4308_, v_compile_4309_, v_logCompileErrors_4310_, v___x_4307_, v_isMeta_4311_, v_val_4312_, v_expectedType_4306_, v_numParams_4484_, v___x_4485_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec_ref(v_x_4314_);
if (lean_obj_tag(v___x_4486_) == 0)
{
size_t v_sz_4487_; size_t v___x_4488_; lean_object* v___x_4489_; 
lean_dec_ref(v___x_4486_);
v_sz_4487_ = lean_array_size(v_fst_4470_);
v___x_4488_ = ((size_t)0ULL);
v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_4487_, v___x_4488_, v_fst_4470_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4498_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4492_ = v___x_4489_;
v_isShared_4493_ = v_isSharedCheck_4498_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4498_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; lean_object* v___x_4496_; 
v___x_4494_ = l_Lean_mkAppN(v_x_4313_, v_a_4490_);
lean_dec(v_a_4490_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4494_);
v___x_4496_ = v___x_4492_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref(v_x_4313_);
v_a_4499_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4489_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4489_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_dec(v_fst_4470_);
lean_dec_ref(v_x_4313_);
v_a_4507_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4486_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4486_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref(v_val_4463_);
lean_dec_ref(v_x_4314_);
lean_dec_ref(v_x_4313_);
lean_dec(v_val_4312_);
lean_dec_ref(v_expectedType_4306_);
v_a_4570_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4467_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4467_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
else
{
lean_dec_ref(v_val_4463_);
lean_dec_ref(v_x_4314_);
lean_dec_ref(v_x_4313_);
lean_dec(v_val_4312_);
lean_dec_ref(v_expectedType_4306_);
return v___x_4464_;
}
}
else
{
lean_dec(v_a_4462_);
lean_dec_ref(v_x_4314_);
lean_dec_ref(v_x_4313_);
lean_dec(v_val_4312_);
v___y_4438_ = v___y_4316_;
v___y_4439_ = v___y_4317_;
v___y_4440_ = v___y_4318_;
v___y_4441_ = v___y_4319_;
goto v___jp_4437_;
}
}
else
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
lean_dec_ref(v_x_4314_);
lean_dec_ref(v_x_4313_);
lean_dec(v_val_4312_);
lean_dec_ref(v_expectedType_4306_);
lean_dec_ref(v_inst_4305_);
v_a_4578_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v___x_4461_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4461_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
v___jp_4437_:
{
lean_object* v_options_4442_; uint8_t v_hasTrace_4443_; 
v_options_4442_ = lean_ctor_get(v___y_4440_, 2);
v_hasTrace_4443_ = lean_ctor_get_uint8(v_options_4442_, sizeof(void*)*1);
if (v_hasTrace_4443_ == 0)
{
v___y_4361_ = v___y_4438_;
v___y_4362_ = v___y_4439_;
v___y_4363_ = v___y_4440_;
v_options_4364_ = v_options_4442_;
v___y_4365_ = v___y_4441_;
goto v___jp_4360_;
}
else
{
lean_object* v_inheritedTraceOptions_4444_; lean_object* v___x_4445_; uint8_t v___x_4446_; 
v_inheritedTraceOptions_4444_ = lean_ctor_get(v___y_4440_, 13);
v___x_4445_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_4446_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4444_, v_options_4442_, v___x_4445_);
if (v___x_4446_ == 0)
{
v___y_4361_ = v___y_4438_;
v___y_4362_ = v___y_4439_;
v___y_4363_ = v___y_4440_;
v_options_4364_ = v_options_4442_;
v___y_4365_ = v___y_4441_;
goto v___jp_4360_;
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4447_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1);
lean_inc_ref(v_inst_4305_);
v___x_4448_ = l_Lean_MessageData_ofExpr(v_inst_4305_);
v___x_4449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4447_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_4436_, v___x_4449_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_dec_ref(v___x_4450_);
v___y_4361_ = v___y_4438_;
v___y_4362_ = v___y_4439_;
v___y_4363_ = v___y_4440_;
v_options_4364_ = v_options_4442_;
v___y_4365_ = v___y_4441_;
goto v___jp_4360_;
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec_ref(v_expectedType_4306_);
lean_dec_ref(v_inst_4305_);
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
}
}
v___jp_4321_:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_enableRealizationsForConst(v___y_4323_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; 
v_unused_4334_ = lean_ctor_get(v___x_4326_, 0);
lean_dec(v_unused_4334_);
v___x_4328_ = v___x_4326_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_dec(v___x_4326_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___y_4322_);
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___y_4322_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v___y_4322_);
v_a_4335_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4326_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4326_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
v___jp_4343_:
{
if (v_compile_4309_ == 0)
{
v___y_4322_ = v___y_4344_;
v___y_4323_ = v___y_4345_;
v___y_4324_ = v___y_4346_;
v___y_4325_ = v___y_4347_;
goto v___jp_4321_;
}
else
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4348_ = lean_unsigned_to_nat(1u);
v___x_4349_ = lean_mk_empty_array_with_capacity(v___x_4348_);
lean_inc(v___y_4345_);
v___x_4350_ = lean_array_push(v___x_4349_, v___y_4345_);
v___x_4351_ = l_Lean_compileDecls(v___x_4350_, v_logCompileErrors_4310_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_dec_ref(v___x_4351_);
v___y_4322_ = v___y_4344_;
v___y_4323_ = v___y_4345_;
v___y_4324_ = v___y_4346_;
v___y_4325_ = v___y_4347_;
goto v___jp_4321_;
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
v___jp_4360_:
{
lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4366_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4367_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4364_, v___x_4366_);
if (v___x_4367_ == 0)
{
lean_object* v___x_4368_; 
lean_dec_ref(v_expectedType_4306_);
v___x_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4368_, 0, v_inst_4305_);
return v___x_4368_;
}
else
{
lean_object* v___x_4369_; 
lean_inc(v___y_4365_);
lean_inc_ref(v___y_4363_);
lean_inc(v___y_4362_);
lean_inc_ref(v___y_4361_);
lean_inc_ref(v_inst_4305_);
v___x_4369_ = lean_infer_type(v_inst_4305_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4365_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref(v___x_4369_);
lean_inc_ref(v_expectedType_4306_);
v___x_4371_ = l_Lean_Meta_isExprDefEq(v_expectedType_4306_, v_a_4370_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4365_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4421_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4374_ = v___x_4371_;
v_isShared_4375_ = v_isSharedCheck_4421_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4371_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4421_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
uint8_t v___x_4376_; 
v___x_4376_ = lean_unbox(v_a_4372_);
lean_dec(v_a_4372_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v_a_4379_; lean_object* v___x_4380_; 
lean_del_object(v___x_4374_);
v___x_4377_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_4378_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4377_, v___y_4365_);
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc_n(v_a_4379_, 2);
lean_dec_ref(v___x_4378_);
v___x_4380_ = l_Lean_Meta_mkAuxDefinition(v_a_4379_, v_expectedType_4306_, v_inst_4305_, v___x_4307_, v___x_4307_, v___x_4308_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4365_);
if (lean_obj_tag(v___x_4380_) == 0)
{
if (v_isMeta_4311_ == 0)
{
lean_object* v_a_4381_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref(v___x_4380_);
v___y_4344_ = v_a_4381_;
v___y_4345_ = v_a_4379_;
v___y_4346_ = v___y_4363_;
v___y_4347_ = v___y_4365_;
goto v___jp_4343_;
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4383_; lean_object* v_env_4384_; lean_object* v_nextMacroScope_4385_; lean_object* v_ngen_4386_; lean_object* v_auxDeclNGen_4387_; lean_object* v_traceState_4388_; lean_object* v_messages_4389_; lean_object* v_infoState_4390_; lean_object* v_snapshotTasks_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4416_; 
v_a_4382_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4382_);
lean_dec_ref(v___x_4380_);
v___x_4383_ = lean_st_ref_take(v___y_4365_);
v_env_4384_ = lean_ctor_get(v___x_4383_, 0);
v_nextMacroScope_4385_ = lean_ctor_get(v___x_4383_, 1);
v_ngen_4386_ = lean_ctor_get(v___x_4383_, 2);
v_auxDeclNGen_4387_ = lean_ctor_get(v___x_4383_, 3);
v_traceState_4388_ = lean_ctor_get(v___x_4383_, 4);
v_messages_4389_ = lean_ctor_get(v___x_4383_, 6);
v_infoState_4390_ = lean_ctor_get(v___x_4383_, 7);
v_snapshotTasks_4391_ = lean_ctor_get(v___x_4383_, 8);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; 
v_unused_4417_ = lean_ctor_get(v___x_4383_, 5);
lean_dec(v_unused_4417_);
v___x_4393_ = v___x_4383_;
v_isShared_4394_ = v_isSharedCheck_4416_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_snapshotTasks_4391_);
lean_inc(v_infoState_4390_);
lean_inc(v_messages_4389_);
lean_inc(v_traceState_4388_);
lean_inc(v_auxDeclNGen_4387_);
lean_inc(v_ngen_4386_);
lean_inc(v_nextMacroScope_4385_);
lean_inc(v_env_4384_);
lean_dec(v___x_4383_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4416_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4398_; 
lean_inc(v_a_4379_);
v___x_4395_ = l_Lean_markMeta(v_env_4384_, v_a_4379_);
v___x_4396_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 5, v___x_4396_);
lean_ctor_set(v___x_4393_, 0, v___x_4395_);
v___x_4398_ = v___x_4393_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_nextMacroScope_4385_);
lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_ngen_4386_);
lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_auxDeclNGen_4387_);
lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_traceState_4388_);
lean_ctor_set(v_reuseFailAlloc_4415_, 5, v___x_4396_);
lean_ctor_set(v_reuseFailAlloc_4415_, 6, v_messages_4389_);
lean_ctor_set(v_reuseFailAlloc_4415_, 7, v_infoState_4390_);
lean_ctor_set(v_reuseFailAlloc_4415_, 8, v_snapshotTasks_4391_);
v___x_4398_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v_mctx_4401_; lean_object* v_zetaDeltaFVarIds_4402_; lean_object* v_postponed_4403_; lean_object* v_diag_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4413_; 
v___x_4399_ = lean_st_ref_set(v___y_4365_, v___x_4398_);
v___x_4400_ = lean_st_ref_take(v___y_4362_);
v_mctx_4401_ = lean_ctor_get(v___x_4400_, 0);
v_zetaDeltaFVarIds_4402_ = lean_ctor_get(v___x_4400_, 2);
v_postponed_4403_ = lean_ctor_get(v___x_4400_, 3);
v_diag_4404_ = lean_ctor_get(v___x_4400_, 4);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; 
v_unused_4414_ = lean_ctor_get(v___x_4400_, 1);
lean_dec(v_unused_4414_);
v___x_4406_ = v___x_4400_;
v_isShared_4407_ = v_isSharedCheck_4413_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_diag_4404_);
lean_inc(v_postponed_4403_);
lean_inc(v_zetaDeltaFVarIds_4402_);
lean_inc(v_mctx_4401_);
lean_dec(v___x_4400_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4413_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4408_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 1, v___x_4408_);
v___x_4410_ = v___x_4406_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_mctx_4401_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_zetaDeltaFVarIds_4402_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v_postponed_4403_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_diag_4404_);
v___x_4410_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4411_; 
v___x_4411_ = lean_st_ref_set(v___y_4362_, v___x_4410_);
v___y_4344_ = v_a_4382_;
v___y_4345_ = v_a_4379_;
v___y_4346_ = v___y_4363_;
v___y_4347_ = v___y_4365_;
goto v___jp_4343_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4379_);
return v___x_4380_;
}
}
else
{
lean_object* v___x_4419_; 
lean_dec_ref(v_expectedType_4306_);
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v_inst_4305_);
v___x_4419_ = v___x_4374_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_inst_4305_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec_ref(v_expectedType_4306_);
lean_dec_ref(v_inst_4305_);
v_a_4422_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4371_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4371_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4306_);
lean_dec_ref(v_inst_4305_);
return v___x_4369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object* v_expectedType_4586_, lean_object* v_inst_4587_, uint8_t v___x_4588_, uint8_t v_hasTrace_4589_, uint8_t v_compile_4590_, uint8_t v_logCompileErrors_4591_, uint8_t v_isMeta_4592_, lean_object* v_val_4593_, lean_object* v_____r_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v___x_4600_; 
lean_inc_ref(v_expectedType_4586_);
v___x_4600_ = l_Lean_Meta_isProp(v_expectedType_4586_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4622_; 
v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4603_ = v___x_4600_;
v_isShared_4604_ = v_isSharedCheck_4622_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4600_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4622_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
uint8_t v___x_4605_; 
v___x_4605_ = lean_unbox(v_a_4601_);
lean_dec(v_a_4601_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; 
lean_del_object(v___x_4603_);
lean_inc(v___y_4598_);
lean_inc_ref(v___y_4597_);
lean_inc(v___y_4596_);
lean_inc_ref(v___y_4595_);
lean_inc_ref(v_inst_4587_);
v___x_4606_ = lean_whnf(v_inst_4587_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v_dummy_4608_; lean_object* v_nargs_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref(v___x_4606_);
v_dummy_4608_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_4609_ = l_Lean_Expr_getAppNumArgs(v_a_4607_);
lean_inc(v_nargs_4609_);
v___x_4610_ = lean_mk_array(v_nargs_4609_, v_dummy_4608_);
v___x_4611_ = lean_unsigned_to_nat(1u);
v___x_4612_ = lean_nat_sub(v_nargs_4609_, v___x_4611_);
lean_dec(v_nargs_4609_);
v___x_4613_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13(v_inst_4587_, v_expectedType_4586_, v___x_4588_, v_hasTrace_4589_, v_compile_4590_, v_logCompileErrors_4591_, v_isMeta_4592_, v_val_4593_, v_a_4607_, v___x_4610_, v___x_4612_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec(v___x_4612_);
return v___x_4613_;
}
else
{
lean_dec(v_val_4593_);
lean_dec_ref(v_inst_4587_);
lean_dec_ref(v_expectedType_4586_);
return v___x_4606_;
}
}
else
{
lean_object* v_options_4614_; lean_object* v___x_4615_; uint8_t v___x_4616_; 
lean_dec(v_val_4593_);
v_options_4614_ = lean_ctor_get(v___y_4597_, 2);
v___x_4615_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4616_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4614_, v___x_4615_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4618_; 
lean_dec_ref(v_expectedType_4586_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 0, v_inst_4587_);
v___x_4618_ = v___x_4603_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_inst_4587_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
else
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
lean_del_object(v___x_4603_);
v___x_4620_ = lean_box(0);
v___x_4621_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_4586_, v_inst_4587_, v_hasTrace_4589_, v___x_4620_, v_hasTrace_4589_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
return v___x_4621_;
}
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec(v_val_4593_);
lean_dec_ref(v_inst_4587_);
lean_dec_ref(v_expectedType_4586_);
v_a_4623_ = lean_ctor_get(v___x_4600_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4600_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4600_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___closed__3(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = ((lean_object*)(l_Lean_Meta_wrapInstance___closed__2));
v___x_4633_ = l_Lean_stringToMessageData(v___x_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg(lean_object* v_upperBound_4634_, lean_object* v_fst_4635_, lean_object* v_args_4636_, uint8_t v___x_4637_, uint8_t v_compile_4638_, uint8_t v_logCompileErrors_4639_, uint8_t v_isMeta_4640_, lean_object* v_val_4641_, lean_object* v_expectedType_4642_, lean_object* v_a_4643_, lean_object* v_b_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_a_4651_; lean_object* v___y_4656_; uint8_t v___x_4675_; 
v___x_4675_ = lean_nat_dec_lt(v_a_4643_, v_upperBound_4634_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; 
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v_b_4644_);
return v___x_4676_;
}
else
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = lean_array_fget_borrowed(v_fst_4635_, v_a_4643_);
v___x_4678_ = l_Lean_Expr_mvarId_x21(v___x_4677_);
lean_inc(v___x_4678_);
v___x_4679_ = l_Lean_MVarId_getDecl(v___x_4678_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v_userName_4681_; lean_object* v_type_4682_; lean_object* v___x_4683_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v___x_4679_);
v_userName_4681_ = lean_ctor_get(v_a_4680_, 0);
lean_inc(v_userName_4681_);
v_type_4682_ = lean_ctor_get(v_a_4680_, 2);
lean_inc_ref(v_type_4682_);
lean_dec(v_a_4680_);
v___x_4683_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__4___redArg(v_type_4682_, v___y_4646_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4685_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc_n(v_a_4684_, 2);
lean_dec_ref(v___x_4683_);
v___x_4685_ = l_Lean_Meta_isProp(v_a_4684_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; lean_object* v___x_4687_; lean_object* v_cls_4688_; lean_object* v___f_4689_; lean_object* v___x_4690_; uint8_t v___x_4691_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
lean_inc(v_a_4686_);
lean_dec_ref(v___x_4685_);
v___x_4687_ = lean_box(0);
v_cls_4688_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_4689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__0));
v___x_4690_ = lean_array_fget_borrowed(v_args_4636_, v_a_4643_);
v___x_4691_ = lean_unbox(v_a_4686_);
lean_dec(v_a_4686_);
if (v___x_4691_ == 0)
{
lean_object* v___x_4692_; 
lean_inc(v_a_4684_);
v___x_4692_ = l_Lean_Meta_isClass_x3f(v_a_4684_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4791_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4791_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4791_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___f_4701_; 
v___x_4697_ = lean_box(v___x_4637_);
v___x_4698_ = lean_box(v_compile_4638_);
v___x_4699_ = lean_box(v_logCompileErrors_4639_);
v___x_4700_ = lean_box(v_isMeta_4640_);
lean_inc(v_a_4684_);
lean_inc(v___x_4690_);
lean_inc(v___x_4678_);
v___f_4701_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1___boxed), 14, 8);
lean_closure_set(v___f_4701_, 0, v___x_4678_);
lean_closure_set(v___f_4701_, 1, v___x_4690_);
lean_closure_set(v___f_4701_, 2, v___x_4687_);
lean_closure_set(v___f_4701_, 3, v_a_4684_);
lean_closure_set(v___f_4701_, 4, v___x_4697_);
lean_closure_set(v___f_4701_, 5, v___x_4698_);
lean_closure_set(v___f_4701_, 6, v___x_4699_);
lean_closure_set(v___f_4701_, 7, v___x_4700_);
if (lean_obj_tag(v_a_4693_) == 0)
{
lean_del_object(v___x_4695_);
goto v___jp_4704_;
}
else
{
lean_dec_ref(v_a_4693_);
if (v___x_4637_ == 0)
{
lean_del_object(v___x_4695_);
goto v___jp_4704_;
}
else
{
lean_object* v_options_4752_; lean_object* v_a_4754_; lean_object* v___y_4757_; uint8_t v___y_4758_; lean_object* v_a_4763_; lean_object* v___y_4767_; lean_object* v___x_4771_; uint8_t v___x_4772_; 
lean_dec_ref(v___f_4701_);
lean_dec(v_userName_4681_);
v_options_4752_ = lean_ctor_get(v___y_4647_, 2);
v___x_4771_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4772_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4752_, v___x_4771_);
if (v___x_4772_ == 0)
{
lean_object* v___x_4773_; 
lean_del_object(v___x_4695_);
lean_inc(v___x_4690_);
v___x_4773_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_4690_, v_a_4684_, v_compile_4638_, v_logCompileErrors_4639_, v_isMeta_4640_, v___x_4678_, v___x_4687_, v___x_4687_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4773_;
goto v___jp_4655_;
}
else
{
lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4774_ = lean_box(0);
lean_inc(v_a_4684_);
v___x_4775_ = l_Lean_Meta_trySynthInstance(v_a_4684_, v___x_4774_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref(v___x_4775_);
if (lean_obj_tag(v_a_4776_) == 1)
{
lean_object* v_a_4777_; lean_object* v___x_4778_; 
v_a_4777_ = lean_ctor_get(v_a_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref(v_a_4776_);
v___x_4778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_4688_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; uint8_t v___x_4780_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref(v___x_4778_);
v___x_4780_ = lean_unbox(v_a_4779_);
lean_dec(v_a_4779_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; 
lean_inc(v___x_4678_);
v___x_4781_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_4678_, v_a_4777_, v___x_4687_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4767_ = v___x_4781_;
goto v___jp_4766_;
}
else
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4782_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__2);
lean_inc(v_a_4777_);
v___x_4783_ = l_Lean_MessageData_ofExpr(v_a_4777_);
v___x_4784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4782_);
lean_ctor_set(v___x_4784_, 1, v___x_4783_);
v___x_4785_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_4688_, v___x_4784_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4787_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref(v___x_4785_);
lean_inc(v___x_4678_);
v___x_4787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__5(v___x_4678_, v_a_4777_, v_a_4786_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4767_ = v___x_4787_;
goto v___jp_4766_;
}
else
{
lean_object* v_a_4788_; 
lean_dec(v_a_4777_);
v_a_4788_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4788_);
lean_dec_ref(v___x_4785_);
v_a_4763_ = v_a_4788_;
goto v___jp_4762_;
}
}
}
else
{
lean_object* v_a_4789_; 
lean_dec(v_a_4777_);
v_a_4789_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4789_);
lean_dec_ref(v___x_4778_);
v_a_4763_ = v_a_4789_;
goto v___jp_4762_;
}
}
else
{
lean_dec(v_a_4776_);
lean_del_object(v___x_4695_);
v_a_4754_ = v___x_4687_;
goto v___jp_4753_;
}
}
else
{
lean_object* v_a_4790_; 
v_a_4790_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4775_);
v_a_4763_ = v_a_4790_;
goto v___jp_4762_;
}
}
v___jp_4753_:
{
lean_object* v___x_4755_; 
lean_inc(v___x_4690_);
v___x_4755_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_4690_, v_a_4684_, v_compile_4638_, v_logCompileErrors_4639_, v_isMeta_4640_, v___x_4678_, v___x_4687_, v_a_4754_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4755_;
goto v___jp_4655_;
}
v___jp_4756_:
{
if (v___y_4758_ == 0)
{
lean_dec_ref(v___y_4757_);
lean_del_object(v___x_4695_);
v_a_4754_ = v___x_4687_;
goto v___jp_4753_;
}
else
{
lean_object* v___x_4760_; 
lean_dec(v_a_4684_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
if (v_isShared_4696_ == 0)
{
lean_ctor_set_tag(v___x_4695_, 1);
lean_ctor_set(v___x_4695_, 0, v___y_4757_);
v___x_4760_ = v___x_4695_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___y_4757_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
v___jp_4762_:
{
uint8_t v___x_4764_; 
v___x_4764_ = l_Lean_Exception_isInterrupt(v_a_4763_);
if (v___x_4764_ == 0)
{
uint8_t v___x_4765_; 
lean_inc_ref(v_a_4763_);
v___x_4765_ = l_Lean_Exception_isRuntime(v_a_4763_);
v___y_4757_ = v_a_4763_;
v___y_4758_ = v___x_4765_;
goto v___jp_4756_;
}
else
{
v___y_4757_ = v_a_4763_;
v___y_4758_ = v___x_4764_;
goto v___jp_4756_;
}
}
v___jp_4766_:
{
if (lean_obj_tag(v___y_4767_) == 0)
{
lean_object* v_a_4768_; 
lean_del_object(v___x_4695_);
v_a_4768_ = lean_ctor_get(v___y_4767_, 0);
lean_inc(v_a_4768_);
lean_dec_ref(v___y_4767_);
if (lean_obj_tag(v_a_4768_) == 0)
{
lean_dec(v_a_4684_);
lean_dec(v___x_4678_);
v_a_4651_ = v___x_4687_;
goto v___jp_4650_;
}
else
{
lean_object* v_a_4769_; 
v_a_4769_ = lean_ctor_get(v_a_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref(v_a_4768_);
v_a_4754_ = v_a_4769_;
goto v___jp_4753_;
}
}
else
{
lean_object* v_a_4770_; 
v_a_4770_ = lean_ctor_get(v___y_4767_, 0);
lean_inc(v_a_4770_);
lean_dec_ref(v___y_4767_);
v_a_4763_ = v_a_4770_;
goto v___jp_4762_;
}
}
}
}
v___jp_4702_:
{
lean_object* v___x_4703_; 
lean_inc(v___x_4690_);
v___x_4703_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1(v___x_4678_, v___x_4690_, v___x_4687_, v_a_4684_, v___x_4637_, v_compile_4638_, v_logCompileErrors_4639_, v_isMeta_4640_, v___x_4687_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4703_;
goto v___jp_4655_;
}
v___jp_4704_:
{
lean_object* v_options_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; 
v_options_4705_ = lean_ctor_get(v___y_4647_, 2);
v___x_4706_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4707_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4705_, v___x_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; 
lean_dec_ref(v___f_4701_);
lean_dec(v_userName_4681_);
lean_inc(v___x_4690_);
v___x_4708_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___lam__1(v___x_4678_, v___x_4690_, v___x_4687_, v_a_4684_, v___x_4637_, v_compile_4638_, v_logCompileErrors_4639_, v_isMeta_4640_, v___x_4687_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4708_;
goto v___jp_4655_;
}
else
{
lean_object* v___x_4709_; 
lean_inc(v_userName_4681_);
lean_inc(v_val_4641_);
v___x_4709_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_4641_, v_userName_4681_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v_fst_4711_; lean_object* v_snd_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4743_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
lean_inc(v_a_4710_);
lean_dec_ref(v___x_4709_);
v_fst_4711_ = lean_ctor_get(v_a_4710_, 0);
v_snd_4712_ = lean_ctor_get(v_a_4710_, 1);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_a_4710_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4714_ = v_a_4710_;
v_isShared_4715_ = v_isSharedCheck_4743_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_snd_4712_);
lean_inc(v_fst_4711_);
lean_dec(v_a_4710_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4743_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
uint8_t v___x_4716_; 
v___x_4716_ = lean_name_eq(v_fst_4711_, v_val_4641_);
if (v___x_4716_ == 0)
{
if (v___x_4637_ == 0)
{
lean_del_object(v___x_4714_);
lean_dec(v_snd_4712_);
lean_dec(v_fst_4711_);
lean_dec_ref(v___f_4701_);
lean_dec(v_userName_4681_);
goto v___jp_4702_;
}
else
{
lean_object* v___x_4717_; 
lean_dec(v_a_4684_);
v___x_4717_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_4688_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; uint8_t v___x_4719_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref(v___x_4717_);
v___x_4719_ = lean_unbox(v_a_4718_);
lean_dec(v_a_4718_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; 
lean_del_object(v___x_4714_);
lean_dec(v_userName_4681_);
lean_inc_ref(v_expectedType_4642_);
lean_inc(v_val_4641_);
v___x_4720_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(v_val_4641_, v_fst_4711_, v_expectedType_4642_, v___f_4689_, v___f_4701_, v___x_4687_, v_cls_4688_, v_snd_4712_, v___x_4678_, v___x_4687_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4720_;
goto v___jp_4655_;
}
else
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4721_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__4);
v___x_4722_ = l_Lean_MessageData_ofName(v_userName_4681_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set_tag(v___x_4714_, 7);
lean_ctor_set(v___x_4714_, 1, v___x_4722_);
lean_ctor_set(v___x_4714_, 0, v___x_4721_);
v___x_4724_ = v___x_4714_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4721_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v___x_4722_);
v___x_4724_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4725_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__6);
v___x_4726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4724_);
lean_ctor_set(v___x_4726_, 1, v___x_4725_);
lean_inc(v_fst_4711_);
v___x_4727_ = l_Lean_MessageData_ofName(v_fst_4711_);
v___x_4728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4726_);
lean_ctor_set(v___x_4728_, 1, v___x_4727_);
v___x_4729_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4728_);
lean_ctor_set(v___x_4730_, 1, v___x_4729_);
v___x_4731_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_4688_, v___x_4730_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4733_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref(v___x_4731_);
lean_inc_ref(v_expectedType_4642_);
lean_inc(v_val_4641_);
v___x_4733_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__3(v_val_4641_, v_fst_4711_, v_expectedType_4642_, v___f_4689_, v___f_4701_, v___x_4687_, v_cls_4688_, v_snd_4712_, v___x_4678_, v_a_4732_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4733_;
goto v___jp_4655_;
}
else
{
lean_dec(v_snd_4712_);
lean_dec(v_fst_4711_);
lean_dec_ref(v___f_4701_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
return v___x_4731_;
}
}
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_del_object(v___x_4714_);
lean_dec(v_snd_4712_);
lean_dec(v_fst_4711_);
lean_dec_ref(v___f_4701_);
lean_dec(v_userName_4681_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4735_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4717_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4717_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
else
{
lean_del_object(v___x_4714_);
lean_dec(v_snd_4712_);
lean_dec(v_fst_4711_);
lean_dec_ref(v___f_4701_);
lean_dec(v_userName_4681_);
goto v___jp_4702_;
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec_ref(v___f_4701_);
lean_dec(v_a_4684_);
lean_dec(v_userName_4681_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4744_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4709_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4709_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec(v_a_4684_);
lean_dec(v_userName_4681_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4792_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4692_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4692_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
else
{
lean_object* v___x_4800_; 
lean_dec(v_userName_4681_);
lean_inc(v___y_4648_);
lean_inc_ref(v___y_4647_);
lean_inc(v___y_4646_);
lean_inc_ref(v___y_4645_);
lean_inc(v___x_4690_);
v___x_4800_ = lean_infer_type(v___x_4690_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4802_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc_n(v_a_4801_, 2);
lean_dec_ref(v___x_4800_);
lean_inc(v_a_4684_);
v___x_4802_ = l_Lean_Meta_isExprDefEq(v_a_4684_, v_a_4801_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___f_4804_; uint8_t v___x_4805_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc(v_a_4803_);
lean_dec_ref(v___x_4802_);
v___f_4804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__7));
v___x_4805_ = lean_unbox(v_a_4803_);
lean_dec(v_a_4803_);
if (v___x_4805_ == 0)
{
lean_object* v___x_4806_; 
v___x_4806_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__0(v_cls_4688_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; uint8_t v___x_4808_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
lean_inc(v_a_4807_);
lean_dec_ref(v___x_4806_);
v___x_4808_ = lean_unbox(v_a_4807_);
lean_dec(v_a_4807_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4809_; 
lean_dec(v_a_4801_);
lean_inc(v___x_4690_);
v___x_4809_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_4684_, v___x_4690_, v___x_4637_, v___x_4678_, v___f_4804_, v___x_4687_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4809_;
goto v___jp_4655_;
}
else
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4810_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__9);
lean_inc(v_a_4643_);
v___x_4811_ = l_Nat_reprFast(v_a_4643_);
v___x_4812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
v___x_4813_ = l_Lean_MessageData_ofFormat(v___x_4812_);
v___x_4814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4810_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__11);
v___x_4816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4814_);
lean_ctor_set(v___x_4816_, 1, v___x_4815_);
lean_inc(v_a_4684_);
v___x_4817_ = l_Lean_MessageData_ofExpr(v_a_4684_);
v___x_4818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4816_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__13);
v___x_4820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4818_);
lean_ctor_set(v___x_4820_, 1, v___x_4819_);
v___x_4821_ = l_Lean_MessageData_ofExpr(v_a_4801_);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
v___x_4823_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___closed__15);
v___x_4824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4822_);
lean_ctor_set(v___x_4824_, 1, v___x_4823_);
lean_inc(v___x_4690_);
v___x_4825_ = l_Lean_MessageData_ofExpr(v___x_4690_);
v___x_4826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4824_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
v___x_4827_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_4688_, v___x_4826_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4829_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref(v___x_4827_);
lean_inc(v___x_4690_);
v___x_4829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__7(v_a_4684_, v___x_4690_, v___x_4637_, v___x_4678_, v___f_4804_, v_a_4828_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4829_;
goto v___jp_4655_;
}
else
{
lean_dec(v_a_4684_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
return v___x_4827_;
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec(v_a_4801_);
lean_dec(v_a_4684_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4830_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4806_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4806_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
else
{
lean_object* v___x_4838_; 
lean_dec(v_a_4801_);
lean_dec(v_a_4684_);
lean_inc(v___x_4690_);
v___x_4838_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_4678_, v___x_4690_, v___y_4646_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v_a_4839_; lean_object* v___x_4840_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
lean_inc(v_a_4839_);
lean_dec_ref(v___x_4838_);
v___x_4840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__6(v___x_4687_, v_a_4839_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
v___y_4656_ = v___x_4840_;
goto v___jp_4655_;
}
else
{
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
return v___x_4838_;
}
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
lean_dec(v_a_4801_);
lean_dec(v_a_4684_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4841_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4802_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4802_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_dec(v_a_4684_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4849_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4800_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4800_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec(v_a_4684_);
lean_dec(v_userName_4681_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4857_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4685_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4685_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
lean_dec(v_userName_4681_);
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4865_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4683_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4683_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
else
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
lean_dec(v___x_4678_);
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4873_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4875_ = v___x_4679_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4679_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
v___jp_4650_:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = lean_unsigned_to_nat(1u);
v___x_4653_ = lean_nat_add(v_a_4643_, v___x_4652_);
lean_dec(v_a_4643_);
v_a_4643_ = v___x_4653_;
v_b_4644_ = v_a_4651_;
goto _start;
}
v___jp_4655_:
{
if (lean_obj_tag(v___y_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4666_; 
v_a_4657_ = lean_ctor_get(v___y_4656_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___y_4656_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4659_ = v___y_4656_;
v_isShared_4660_ = v_isSharedCheck_4666_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___y_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4666_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
if (lean_obj_tag(v_a_4657_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4663_; 
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4661_ = lean_ctor_get(v_a_4657_, 0);
lean_inc(v_a_4661_);
lean_dec_ref(v_a_4657_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v_a_4661_);
v___x_4663_ = v___x_4659_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
else
{
lean_object* v_a_4665_; 
lean_del_object(v___x_4659_);
v_a_4665_ = lean_ctor_get(v_a_4657_, 0);
lean_inc(v_a_4665_);
lean_dec_ref(v_a_4657_);
v_a_4651_ = v_a_4665_;
goto v___jp_4650_;
}
}
}
else
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4674_; 
lean_dec(v_a_4643_);
lean_dec_ref(v_expectedType_4642_);
lean_dec(v_val_4641_);
v_a_4667_ = lean_ctor_get(v___y_4656_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___y_4656_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4669_ = v___y_4656_;
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___y_4656_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4672_; 
if (v_isShared_4670_ == 0)
{
v___x_4672_ = v___x_4669_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4667_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15_spec__24(lean_object* v_inst_4881_, lean_object* v_expectedType_4882_, uint8_t v___x_4883_, uint8_t v_compile_4884_, uint8_t v_logCompileErrors_4885_, uint8_t v_isMeta_4886_, lean_object* v_val_4887_, lean_object* v_x_4888_, lean_object* v_x_4889_, lean_object* v_x_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___y_4900_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v_options_4939_; lean_object* v___y_4940_; 
if (lean_obj_tag(v_x_4888_) == 5)
{
lean_object* v_fn_5007_; lean_object* v_arg_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v_fn_5007_ = lean_ctor_get(v_x_4888_, 0);
lean_inc_ref(v_fn_5007_);
v_arg_5008_ = lean_ctor_get(v_x_4888_, 1);
lean_inc_ref(v_arg_5008_);
lean_dec_ref(v_x_4888_);
v___x_5009_ = lean_array_set(v_x_4889_, v_x_4890_, v_arg_5008_);
v___x_5010_ = lean_unsigned_to_nat(1u);
v___x_5011_ = lean_nat_sub(v_x_4890_, v___x_5010_);
lean_dec(v_x_4890_);
v_x_4888_ = v_fn_5007_;
v_x_4889_ = v___x_5009_;
v_x_4890_ = v___x_5011_;
goto _start;
}
else
{
lean_object* v_cls_5013_; lean_object* v___y_5015_; lean_object* v___y_5016_; lean_object* v___y_5017_; lean_object* v___y_5018_; lean_object* v___x_5036_; 
lean_dec(v_x_4890_);
v_cls_5013_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5036_ = l_Lean_Expr_constName_x3f(v_x_4888_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_x_4888_);
lean_dec(v_val_4887_);
v___y_5015_ = v___y_4891_;
v___y_5016_ = v___y_4892_;
v___y_5017_ = v___y_4893_;
v___y_5018_ = v___y_4894_;
goto v___jp_5014_;
}
else
{
lean_object* v_val_5037_; lean_object* v___x_5038_; 
v_val_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_val_5037_);
lean_dec_ref(v___x_5036_);
v___x_5038_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(v_val_5037_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5039_);
lean_dec_ref(v___x_5038_);
if (lean_obj_tag(v_a_5039_) == 6)
{
lean_object* v_val_5040_; lean_object* v___x_5041_; 
lean_dec_ref(v_inst_4881_);
v_val_5040_ = lean_ctor_get(v_a_5039_, 0);
lean_inc_ref(v_val_5040_);
lean_dec_ref(v_a_5039_);
lean_inc(v___y_4894_);
lean_inc_ref(v___y_4893_);
lean_inc(v___y_4892_);
lean_inc_ref(v___y_4891_);
lean_inc_ref(v_x_4888_);
v___x_5041_ = lean_infer_type(v_x_4888_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; uint8_t v___x_5043_; lean_object* v___x_5044_; 
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
lean_inc(v_a_5042_);
lean_dec_ref(v___x_5041_);
v___x_5043_ = 0;
v___x_5044_ = l_Lean_Meta_forallMetaTelescope(v_a_5042_, v___x_5043_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v_snd_5046_; lean_object* v_fst_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5147_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref(v___x_5044_);
v_snd_5046_ = lean_ctor_get(v_a_5045_, 1);
v_fst_5047_ = lean_ctor_get(v_a_5045_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v_a_5045_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5049_ = v_a_5045_;
v_isShared_5050_ = v_isSharedCheck_5147_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_snd_5046_);
lean_inc(v_fst_5047_);
lean_dec(v_a_5045_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5147_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v_snd_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5145_; 
v_snd_5051_ = lean_ctor_get(v_snd_5046_, 1);
v_isSharedCheck_5145_ = !lean_is_exclusive(v_snd_5046_);
if (v_isSharedCheck_5145_ == 0)
{
lean_object* v_unused_5146_; 
v_unused_5146_ = lean_ctor_get(v_snd_5046_, 0);
lean_dec(v_unused_5146_);
v___x_5053_ = v_snd_5046_;
v_isShared_5054_ = v_isSharedCheck_5145_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_snd_5051_);
lean_dec(v_snd_5046_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5145_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5055_; lean_object* v___y_5057_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___x_5092_; uint8_t v___x_5093_; 
v___x_5055_ = lean_array_get_size(v_x_4889_);
v___x_5092_ = lean_array_get_size(v_fst_5047_);
v___x_5093_ = lean_nat_dec_eq(v___x_5055_, v___x_5092_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5097_; 
lean_dec(v_snd_5051_);
lean_dec(v_fst_5047_);
lean_dec_ref(v_val_5040_);
lean_dec(v_val_4887_);
lean_dec_ref(v_expectedType_4882_);
v___x_5094_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3);
v___x_5095_ = l_Lean_MessageData_ofExpr(v_x_4888_);
if (v_isShared_5054_ == 0)
{
lean_ctor_set_tag(v___x_5053_, 7);
lean_ctor_set(v___x_5053_, 1, v___x_5095_);
lean_ctor_set(v___x_5053_, 0, v___x_5094_);
v___x_5097_ = v___x_5053_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5094_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v___x_5095_);
v___x_5097_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
lean_object* v___x_5098_; lean_object* v___x_5100_; 
v___x_5098_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
if (v_isShared_5050_ == 0)
{
lean_ctor_set_tag(v___x_5049_, 7);
lean_ctor_set(v___x_5049_, 1, v___x_5098_);
lean_ctor_set(v___x_5049_, 0, v___x_5097_);
v___x_5100_ = v___x_5049_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5097_);
lean_ctor_set(v_reuseFailAlloc_5107_, 1, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5101_ = lean_array_to_list(v_x_4889_);
v___x_5102_ = lean_box(0);
v___x_5103_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_5101_, v___x_5102_);
v___x_5104_ = l_Lean_MessageData_ofList(v___x_5103_);
v___x_5105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5100_);
lean_ctor_set(v___x_5105_, 1, v___x_5104_);
v___x_5106_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5105_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
return v___x_5106_;
}
}
}
else
{
lean_object* v___x_5109_; 
lean_inc_ref(v_expectedType_4882_);
v___x_5109_ = l_Lean_Meta_isExprDefEq(v_expectedType_4882_, v_snd_5051_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v_a_5110_; uint8_t v___x_5111_; 
v_a_5110_ = lean_ctor_get(v___x_5109_, 0);
lean_inc(v_a_5110_);
lean_dec_ref(v___x_5109_);
v___x_5111_ = lean_unbox(v_a_5110_);
if (v___x_5111_ == 0)
{
lean_object* v_toConstantVal_5112_; lean_object* v_name_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5117_; 
lean_dec(v_fst_5047_);
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_x_4888_);
lean_dec(v_val_4887_);
v_toConstantVal_5112_ = lean_ctor_get(v_val_5040_, 0);
lean_inc_ref(v_toConstantVal_5112_);
lean_dec_ref(v_val_5040_);
v_name_5113_ = lean_ctor_get(v_toConstantVal_5112_, 0);
lean_inc(v_name_5113_);
lean_dec_ref(v_toConstantVal_5112_);
v___x_5114_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5);
v___x_5115_ = l_Lean_MessageData_ofExpr(v_expectedType_4882_);
if (v_isShared_5054_ == 0)
{
lean_ctor_set_tag(v___x_5053_, 7);
lean_ctor_set(v___x_5053_, 1, v___x_5115_);
lean_ctor_set(v___x_5053_, 0, v___x_5114_);
v___x_5117_ = v___x_5053_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5114_);
lean_ctor_set(v_reuseFailAlloc_5136_, 1, v___x_5115_);
v___x_5117_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
lean_object* v___x_5118_; lean_object* v___x_5120_; 
v___x_5118_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7);
if (v_isShared_5050_ == 0)
{
lean_ctor_set_tag(v___x_5049_, 7);
lean_ctor_set(v___x_5049_, 1, v___x_5118_);
lean_ctor_set(v___x_5049_, 0, v___x_5117_);
v___x_5120_ = v___x_5049_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v___x_5117_);
lean_ctor_set(v_reuseFailAlloc_5135_, 1, v___x_5118_);
v___x_5120_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
uint8_t v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
v___x_5121_ = lean_unbox(v_a_5110_);
lean_dec(v_a_5110_);
v___x_5122_ = l_Lean_MessageData_ofConstName(v_name_5113_, v___x_5121_);
v___x_5123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5123_, 0, v___x_5120_);
lean_ctor_set(v___x_5123_, 1, v___x_5122_);
v___x_5124_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_5125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5125_, 0, v___x_5123_);
lean_ctor_set(v___x_5125_, 1, v___x_5124_);
v___x_5126_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5125_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5126_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5126_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
}
}
else
{
lean_dec(v_a_5110_);
lean_del_object(v___x_5053_);
lean_del_object(v___x_5049_);
v___y_5057_ = v___y_4891_;
v___y_5058_ = v___y_4892_;
v___y_5059_ = v___y_4893_;
v___y_5060_ = v___y_4894_;
goto v___jp_5056_;
}
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
lean_del_object(v___x_5053_);
lean_del_object(v___x_5049_);
lean_dec(v_fst_5047_);
lean_dec_ref(v_val_5040_);
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_x_4888_);
lean_dec(v_val_4887_);
lean_dec_ref(v_expectedType_4882_);
v_a_5137_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5109_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5109_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
v___jp_5056_:
{
lean_object* v_numParams_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v_numParams_5061_ = lean_ctor_get(v_val_5040_, 3);
lean_inc(v_numParams_5061_);
lean_dec_ref(v_val_5040_);
v___x_5062_ = lean_box(0);
v___x_5063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg(v___x_5055_, v_fst_5047_, v_x_4889_, v___x_4883_, v_compile_4884_, v_logCompileErrors_4885_, v_isMeta_4886_, v_val_4887_, v_expectedType_4882_, v_numParams_5061_, v___x_5062_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
lean_dec_ref(v_x_4889_);
if (lean_obj_tag(v___x_5063_) == 0)
{
size_t v_sz_5064_; size_t v___x_5065_; lean_object* v___x_5066_; 
lean_dec_ref(v___x_5063_);
v_sz_5064_ = lean_array_size(v_fst_5047_);
v___x_5065_ = ((size_t)0ULL);
v___x_5066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_5064_, v___x_5065_, v_fst_5047_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5075_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5069_ = v___x_5066_;
v_isShared_5070_ = v_isSharedCheck_5075_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_5066_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5075_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; lean_object* v___x_5073_; 
v___x_5071_ = l_Lean_mkAppN(v_x_4888_, v_a_5067_);
lean_dec(v_a_5067_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5071_);
v___x_5073_ = v___x_5069_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5071_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec_ref(v_x_4888_);
v_a_5076_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5066_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5066_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
else
{
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5091_; 
lean_dec(v_fst_5047_);
lean_dec_ref(v_x_4888_);
v_a_5084_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5086_ = v___x_5063_;
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5063_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5089_; 
if (v_isShared_5087_ == 0)
{
v___x_5089_ = v___x_5086_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5084_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
lean_dec_ref(v_val_5040_);
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_x_4888_);
lean_dec(v_val_4887_);
lean_dec_ref(v_expectedType_4882_);
v_a_5148_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_5044_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5044_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
else
{
lean_dec_ref(v_val_5040_);
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_x_4888_);
lean_dec(v_val_4887_);
lean_dec_ref(v_expectedType_4882_);
return v___x_5041_;
}
}
else
{
lean_dec(v_a_5039_);
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_x_4888_);
lean_dec(v_val_4887_);
v___y_5015_ = v___y_4891_;
v___y_5016_ = v___y_4892_;
v___y_5017_ = v___y_4893_;
v___y_5018_ = v___y_4894_;
goto v___jp_5014_;
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_x_4888_);
lean_dec(v_val_4887_);
lean_dec_ref(v_expectedType_4882_);
lean_dec_ref(v_inst_4881_);
v_a_5156_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5038_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5038_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
v___jp_5014_:
{
lean_object* v_options_5019_; uint8_t v_hasTrace_5020_; 
v_options_5019_ = lean_ctor_get(v___y_5017_, 2);
v_hasTrace_5020_ = lean_ctor_get_uint8(v_options_5019_, sizeof(void*)*1);
if (v_hasTrace_5020_ == 0)
{
v___y_4936_ = v___y_5015_;
v___y_4937_ = v___y_5016_;
v___y_4938_ = v___y_5017_;
v_options_4939_ = v_options_5019_;
v___y_4940_ = v___y_5018_;
goto v___jp_4935_;
}
else
{
lean_object* v_inheritedTraceOptions_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v_inheritedTraceOptions_5021_ = lean_ctor_get(v___y_5017_, 13);
v___x_5022_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5023_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5021_, v_options_5019_, v___x_5022_);
if (v___x_5023_ == 0)
{
v___y_4936_ = v___y_5015_;
v___y_4937_ = v___y_5016_;
v___y_4938_ = v___y_5017_;
v_options_4939_ = v_options_5019_;
v___y_4940_ = v___y_5018_;
goto v___jp_4935_;
}
else
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5024_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1);
lean_inc_ref(v_inst_4881_);
v___x_5025_ = l_Lean_MessageData_ofExpr(v_inst_4881_);
v___x_5026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5024_);
lean_ctor_set(v___x_5026_, 1, v___x_5025_);
v___x_5027_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_5013_, v___x_5026_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_dec_ref(v___x_5027_);
v___y_4936_ = v___y_5015_;
v___y_4937_ = v___y_5016_;
v___y_4938_ = v___y_5017_;
v_options_4939_ = v_options_5019_;
v___y_4940_ = v___y_5018_;
goto v___jp_4935_;
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_dec_ref(v_expectedType_4882_);
lean_dec_ref(v_inst_4881_);
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_5027_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_5027_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
}
}
}
v___jp_4896_:
{
lean_object* v___x_4901_; 
v___x_4901_ = l_Lean_enableRealizationsForConst(v___y_4898_, v___y_4899_, v___y_4900_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4908_ == 0)
{
lean_object* v_unused_4909_; 
v_unused_4909_ = lean_ctor_get(v___x_4901_, 0);
lean_dec(v_unused_4909_);
v___x_4903_ = v___x_4901_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_dec(v___x_4901_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 0, v___y_4897_);
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___y_4897_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
lean_dec_ref(v___y_4897_);
v_a_4910_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4901_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4901_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
v___jp_4918_:
{
if (v_compile_4884_ == 0)
{
v___y_4897_ = v___y_4920_;
v___y_4898_ = v___y_4919_;
v___y_4899_ = v___y_4921_;
v___y_4900_ = v___y_4922_;
goto v___jp_4896_;
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4923_ = lean_unsigned_to_nat(1u);
v___x_4924_ = lean_mk_empty_array_with_capacity(v___x_4923_);
lean_inc(v___y_4919_);
v___x_4925_ = lean_array_push(v___x_4924_, v___y_4919_);
v___x_4926_ = l_Lean_compileDecls(v___x_4925_, v_logCompileErrors_4885_, v___y_4921_, v___y_4922_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_dec_ref(v___x_4926_);
v___y_4897_ = v___y_4920_;
v___y_4898_ = v___y_4919_;
v___y_4899_ = v___y_4921_;
v___y_4900_ = v___y_4922_;
goto v___jp_4896_;
}
else
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
lean_dec_ref(v___y_4920_);
lean_dec(v___y_4919_);
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4926_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
}
v___jp_4935_:
{
lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4941_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4942_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4939_, v___x_4941_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; 
lean_dec_ref(v_expectedType_4882_);
v___x_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4943_, 0, v_inst_4881_);
return v___x_4943_;
}
else
{
lean_object* v___x_4944_; 
lean_inc(v___y_4940_);
lean_inc_ref(v___y_4938_);
lean_inc(v___y_4937_);
lean_inc_ref(v___y_4936_);
lean_inc_ref(v_inst_4881_);
v___x_4944_ = lean_infer_type(v_inst_4881_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4940_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4946_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref(v___x_4944_);
lean_inc_ref(v_expectedType_4882_);
v___x_4946_ = l_Lean_Meta_isExprDefEq(v_expectedType_4882_, v_a_4945_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4940_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4998_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4949_ = v___x_4946_;
v_isShared_4950_ = v_isSharedCheck_4998_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4946_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4998_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
uint8_t v___x_4951_; 
v___x_4951_ = lean_unbox(v_a_4947_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v_a_4954_; uint8_t v___x_4955_; uint8_t v___x_4956_; lean_object* v___x_4957_; 
lean_del_object(v___x_4949_);
v___x_4952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_4953_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4952_, v___y_4940_);
v_a_4954_ = lean_ctor_get(v___x_4953_, 0);
lean_inc_n(v_a_4954_, 2);
lean_dec_ref(v___x_4953_);
v___x_4955_ = lean_unbox(v_a_4947_);
v___x_4956_ = lean_unbox(v_a_4947_);
lean_dec(v_a_4947_);
v___x_4957_ = l_Lean_Meta_mkAuxDefinition(v_a_4954_, v_expectedType_4882_, v_inst_4881_, v___x_4955_, v___x_4956_, v___x_4883_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4940_);
if (lean_obj_tag(v___x_4957_) == 0)
{
if (v_isMeta_4886_ == 0)
{
lean_object* v_a_4958_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref(v___x_4957_);
v___y_4919_ = v_a_4954_;
v___y_4920_ = v_a_4958_;
v___y_4921_ = v___y_4938_;
v___y_4922_ = v___y_4940_;
goto v___jp_4918_;
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4960_; lean_object* v_env_4961_; lean_object* v_nextMacroScope_4962_; lean_object* v_ngen_4963_; lean_object* v_auxDeclNGen_4964_; lean_object* v_traceState_4965_; lean_object* v_messages_4966_; lean_object* v_infoState_4967_; lean_object* v_snapshotTasks_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4993_; 
v_a_4959_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4959_);
lean_dec_ref(v___x_4957_);
v___x_4960_ = lean_st_ref_take(v___y_4940_);
v_env_4961_ = lean_ctor_get(v___x_4960_, 0);
v_nextMacroScope_4962_ = lean_ctor_get(v___x_4960_, 1);
v_ngen_4963_ = lean_ctor_get(v___x_4960_, 2);
v_auxDeclNGen_4964_ = lean_ctor_get(v___x_4960_, 3);
v_traceState_4965_ = lean_ctor_get(v___x_4960_, 4);
v_messages_4966_ = lean_ctor_get(v___x_4960_, 6);
v_infoState_4967_ = lean_ctor_get(v___x_4960_, 7);
v_snapshotTasks_4968_ = lean_ctor_get(v___x_4960_, 8);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4993_ == 0)
{
lean_object* v_unused_4994_; 
v_unused_4994_ = lean_ctor_get(v___x_4960_, 5);
lean_dec(v_unused_4994_);
v___x_4970_ = v___x_4960_;
v_isShared_4971_ = v_isSharedCheck_4993_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_snapshotTasks_4968_);
lean_inc(v_infoState_4967_);
lean_inc(v_messages_4966_);
lean_inc(v_traceState_4965_);
lean_inc(v_auxDeclNGen_4964_);
lean_inc(v_ngen_4963_);
lean_inc(v_nextMacroScope_4962_);
lean_inc(v_env_4961_);
lean_dec(v___x_4960_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4993_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4975_; 
lean_inc(v_a_4954_);
v___x_4972_ = l_Lean_markMeta(v_env_4961_, v_a_4954_);
v___x_4973_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_4971_ == 0)
{
lean_ctor_set(v___x_4970_, 5, v___x_4973_);
lean_ctor_set(v___x_4970_, 0, v___x_4972_);
v___x_4975_ = v___x_4970_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4972_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_nextMacroScope_4962_);
lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_ngen_4963_);
lean_ctor_set(v_reuseFailAlloc_4992_, 3, v_auxDeclNGen_4964_);
lean_ctor_set(v_reuseFailAlloc_4992_, 4, v_traceState_4965_);
lean_ctor_set(v_reuseFailAlloc_4992_, 5, v___x_4973_);
lean_ctor_set(v_reuseFailAlloc_4992_, 6, v_messages_4966_);
lean_ctor_set(v_reuseFailAlloc_4992_, 7, v_infoState_4967_);
lean_ctor_set(v_reuseFailAlloc_4992_, 8, v_snapshotTasks_4968_);
v___x_4975_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v_mctx_4978_; lean_object* v_zetaDeltaFVarIds_4979_; lean_object* v_postponed_4980_; lean_object* v_diag_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4990_; 
v___x_4976_ = lean_st_ref_set(v___y_4940_, v___x_4975_);
v___x_4977_ = lean_st_ref_take(v___y_4937_);
v_mctx_4978_ = lean_ctor_get(v___x_4977_, 0);
v_zetaDeltaFVarIds_4979_ = lean_ctor_get(v___x_4977_, 2);
v_postponed_4980_ = lean_ctor_get(v___x_4977_, 3);
v_diag_4981_ = lean_ctor_get(v___x_4977_, 4);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4990_ == 0)
{
lean_object* v_unused_4991_; 
v_unused_4991_ = lean_ctor_get(v___x_4977_, 1);
lean_dec(v_unused_4991_);
v___x_4983_ = v___x_4977_;
v_isShared_4984_ = v_isSharedCheck_4990_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_diag_4981_);
lean_inc(v_postponed_4980_);
lean_inc(v_zetaDeltaFVarIds_4979_);
lean_inc(v_mctx_4978_);
lean_dec(v___x_4977_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4990_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4985_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_4985_);
v___x_4987_ = v___x_4983_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_mctx_4978_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_zetaDeltaFVarIds_4979_);
lean_ctor_set(v_reuseFailAlloc_4989_, 3, v_postponed_4980_);
lean_ctor_set(v_reuseFailAlloc_4989_, 4, v_diag_4981_);
v___x_4987_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_st_ref_set(v___y_4937_, v___x_4987_);
v___y_4919_ = v_a_4954_;
v___y_4920_ = v_a_4959_;
v___y_4921_ = v___y_4938_;
v___y_4922_ = v___y_4940_;
goto v___jp_4918_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4954_);
return v___x_4957_;
}
}
else
{
lean_object* v___x_4996_; 
lean_dec(v_a_4947_);
lean_dec_ref(v_expectedType_4882_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 0, v_inst_4881_);
v___x_4996_ = v___x_4949_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_inst_4881_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec_ref(v_expectedType_4882_);
lean_dec_ref(v_inst_4881_);
v_a_4999_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4946_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4946_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4882_);
lean_dec_ref(v_inst_4881_);
return v___x_4944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15(lean_object* v_inst_5164_, lean_object* v_expectedType_5165_, uint8_t v___x_5166_, uint8_t v_compile_5167_, uint8_t v_logCompileErrors_5168_, uint8_t v_isMeta_5169_, lean_object* v_val_5170_, lean_object* v_x_5171_, lean_object* v_x_5172_, lean_object* v_x_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5202_; lean_object* v___y_5203_; lean_object* v___y_5204_; lean_object* v___y_5205_; lean_object* v___y_5219_; lean_object* v___y_5220_; lean_object* v___y_5221_; lean_object* v_options_5222_; lean_object* v___y_5223_; 
if (lean_obj_tag(v_x_5171_) == 5)
{
lean_object* v_fn_5290_; lean_object* v_arg_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
v_fn_5290_ = lean_ctor_get(v_x_5171_, 0);
lean_inc_ref(v_fn_5290_);
v_arg_5291_ = lean_ctor_get(v_x_5171_, 1);
lean_inc_ref(v_arg_5291_);
lean_dec_ref(v_x_5171_);
v___x_5292_ = lean_array_set(v_x_5172_, v_x_5173_, v_arg_5291_);
v___x_5293_ = lean_unsigned_to_nat(1u);
v___x_5294_ = lean_nat_sub(v_x_5173_, v___x_5293_);
v___x_5295_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15_spec__24(v_inst_5164_, v_expectedType_5165_, v___x_5166_, v_compile_5167_, v_logCompileErrors_5168_, v_isMeta_5169_, v_val_5170_, v_fn_5290_, v___x_5292_, v___x_5294_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
return v___x_5295_;
}
else
{
lean_object* v_cls_5296_; lean_object* v___y_5298_; lean_object* v___y_5299_; lean_object* v___y_5300_; lean_object* v___y_5301_; lean_object* v___x_5319_; 
v_cls_5296_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5319_ = l_Lean_Expr_constName_x3f(v_x_5171_);
if (lean_obj_tag(v___x_5319_) == 0)
{
lean_dec_ref(v_x_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_val_5170_);
v___y_5298_ = v___y_5174_;
v___y_5299_ = v___y_5175_;
v___y_5300_ = v___y_5176_;
v___y_5301_ = v___y_5177_;
goto v___jp_5297_;
}
else
{
lean_object* v_val_5320_; lean_object* v___x_5321_; 
v_val_5320_ = lean_ctor_get(v___x_5319_, 0);
lean_inc(v_val_5320_);
lean_dec_ref(v___x_5319_);
v___x_5321_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3(v_val_5320_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
lean_inc(v_a_5322_);
lean_dec_ref(v___x_5321_);
if (lean_obj_tag(v_a_5322_) == 6)
{
lean_object* v_val_5323_; lean_object* v___x_5324_; 
lean_dec_ref(v_inst_5164_);
v_val_5323_ = lean_ctor_get(v_a_5322_, 0);
lean_inc_ref(v_val_5323_);
lean_dec_ref(v_a_5322_);
lean_inc(v___y_5177_);
lean_inc_ref(v___y_5176_);
lean_inc(v___y_5175_);
lean_inc_ref(v___y_5174_);
lean_inc_ref(v_x_5171_);
v___x_5324_ = lean_infer_type(v_x_5171_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; uint8_t v___x_5326_; lean_object* v___x_5327_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
lean_inc(v_a_5325_);
lean_dec_ref(v___x_5324_);
v___x_5326_ = 0;
v___x_5327_ = l_Lean_Meta_forallMetaTelescope(v_a_5325_, v___x_5326_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
if (lean_obj_tag(v___x_5327_) == 0)
{
lean_object* v_a_5328_; lean_object* v_snd_5329_; lean_object* v_fst_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5430_; 
v_a_5328_ = lean_ctor_get(v___x_5327_, 0);
lean_inc(v_a_5328_);
lean_dec_ref(v___x_5327_);
v_snd_5329_ = lean_ctor_get(v_a_5328_, 1);
v_fst_5330_ = lean_ctor_get(v_a_5328_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v_a_5328_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5332_ = v_a_5328_;
v_isShared_5333_ = v_isSharedCheck_5430_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_snd_5329_);
lean_inc(v_fst_5330_);
lean_dec(v_a_5328_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5430_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v_snd_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5428_; 
v_snd_5334_ = lean_ctor_get(v_snd_5329_, 1);
v_isSharedCheck_5428_ = !lean_is_exclusive(v_snd_5329_);
if (v_isSharedCheck_5428_ == 0)
{
lean_object* v_unused_5429_; 
v_unused_5429_ = lean_ctor_get(v_snd_5329_, 0);
lean_dec(v_unused_5429_);
v___x_5336_ = v_snd_5329_;
v_isShared_5337_ = v_isSharedCheck_5428_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_snd_5334_);
lean_dec(v_snd_5329_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5428_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5338_; lean_object* v___y_5340_; lean_object* v___y_5341_; lean_object* v___y_5342_; lean_object* v___y_5343_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v___x_5338_ = lean_array_get_size(v_x_5172_);
v___x_5375_ = lean_array_get_size(v_fst_5330_);
v___x_5376_ = lean_nat_dec_eq(v___x_5338_, v___x_5375_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5380_; 
lean_dec(v_snd_5334_);
lean_dec(v_fst_5330_);
lean_dec_ref(v_val_5323_);
lean_dec(v_val_5170_);
lean_dec_ref(v_expectedType_5165_);
v___x_5377_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__3);
v___x_5378_ = l_Lean_MessageData_ofExpr(v_x_5171_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set_tag(v___x_5336_, 7);
lean_ctor_set(v___x_5336_, 1, v___x_5378_);
lean_ctor_set(v___x_5336_, 0, v___x_5377_);
v___x_5380_ = v___x_5336_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v___x_5377_);
lean_ctor_set(v_reuseFailAlloc_5391_, 1, v___x_5378_);
v___x_5380_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
lean_object* v___x_5381_; lean_object* v___x_5383_; 
v___x_5381_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___lam__5___closed__3);
if (v_isShared_5333_ == 0)
{
lean_ctor_set_tag(v___x_5332_, 7);
lean_ctor_set(v___x_5332_, 1, v___x_5381_);
lean_ctor_set(v___x_5332_, 0, v___x_5380_);
v___x_5383_ = v___x_5332_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5380_);
lean_ctor_set(v_reuseFailAlloc_5390_, 1, v___x_5381_);
v___x_5383_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5384_ = lean_array_to_list(v_x_5172_);
v___x_5385_ = lean_box(0);
v___x_5386_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_5384_, v___x_5385_);
v___x_5387_ = l_Lean_MessageData_ofList(v___x_5386_);
v___x_5388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5383_);
lean_ctor_set(v___x_5388_, 1, v___x_5387_);
v___x_5389_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5388_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
return v___x_5389_;
}
}
}
else
{
lean_object* v___x_5392_; 
lean_inc_ref(v_expectedType_5165_);
v___x_5392_ = l_Lean_Meta_isExprDefEq(v_expectedType_5165_, v_snd_5334_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v_a_5393_; uint8_t v___x_5394_; 
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
lean_inc(v_a_5393_);
lean_dec_ref(v___x_5392_);
v___x_5394_ = lean_unbox(v_a_5393_);
if (v___x_5394_ == 0)
{
lean_object* v_toConstantVal_5395_; lean_object* v_name_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5400_; 
lean_dec(v_fst_5330_);
lean_dec_ref(v_x_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_val_5170_);
v_toConstantVal_5395_ = lean_ctor_get(v_val_5323_, 0);
lean_inc_ref(v_toConstantVal_5395_);
lean_dec_ref(v_val_5323_);
v_name_5396_ = lean_ctor_get(v_toConstantVal_5395_, 0);
lean_inc(v_name_5396_);
lean_dec_ref(v_toConstantVal_5395_);
v___x_5397_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__5);
v___x_5398_ = l_Lean_MessageData_ofExpr(v_expectedType_5165_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set_tag(v___x_5336_, 7);
lean_ctor_set(v___x_5336_, 1, v___x_5398_);
lean_ctor_set(v___x_5336_, 0, v___x_5397_);
v___x_5400_ = v___x_5336_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5397_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v___x_5398_);
v___x_5400_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
lean_object* v___x_5401_; lean_object* v___x_5403_; 
v___x_5401_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__7);
if (v_isShared_5333_ == 0)
{
lean_ctor_set_tag(v___x_5332_, 7);
lean_ctor_set(v___x_5332_, 1, v___x_5401_);
lean_ctor_set(v___x_5332_, 0, v___x_5400_);
v___x_5403_ = v___x_5332_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5400_);
lean_ctor_set(v_reuseFailAlloc_5418_, 1, v___x_5401_);
v___x_5403_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
uint8_t v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v_a_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5417_; 
v___x_5404_ = lean_unbox(v_a_5393_);
lean_dec(v_a_5393_);
v___x_5405_ = l_Lean_MessageData_ofConstName(v_name_5396_, v___x_5404_);
v___x_5406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5403_);
lean_ctor_set(v___x_5406_, 1, v___x_5405_);
v___x_5407_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_5408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5406_);
lean_ctor_set(v___x_5408_, 1, v___x_5407_);
v___x_5409_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5408_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
v_a_5410_ = lean_ctor_get(v___x_5409_, 0);
v_isSharedCheck_5417_ = !lean_is_exclusive(v___x_5409_);
if (v_isSharedCheck_5417_ == 0)
{
v___x_5412_ = v___x_5409_;
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_a_5410_);
lean_dec(v___x_5409_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5415_; 
if (v_isShared_5413_ == 0)
{
v___x_5415_ = v___x_5412_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
return v___x_5415_;
}
}
}
}
}
else
{
lean_dec(v_a_5393_);
lean_del_object(v___x_5336_);
lean_del_object(v___x_5332_);
v___y_5340_ = v___y_5174_;
v___y_5341_ = v___y_5175_;
v___y_5342_ = v___y_5176_;
v___y_5343_ = v___y_5177_;
goto v___jp_5339_;
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5427_; 
lean_del_object(v___x_5336_);
lean_del_object(v___x_5332_);
lean_dec(v_fst_5330_);
lean_dec_ref(v_val_5323_);
lean_dec_ref(v_x_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_val_5170_);
lean_dec_ref(v_expectedType_5165_);
v_a_5420_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5422_ = v___x_5392_;
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5392_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5425_; 
if (v_isShared_5423_ == 0)
{
v___x_5425_ = v___x_5422_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5420_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
v___jp_5339_:
{
lean_object* v_numParams_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; 
v_numParams_5344_ = lean_ctor_get(v_val_5323_, 3);
lean_inc(v_numParams_5344_);
lean_dec_ref(v_val_5323_);
v___x_5345_ = lean_box(0);
v___x_5346_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg(v___x_5338_, v_fst_5330_, v_x_5172_, v___x_5166_, v_compile_5167_, v_logCompileErrors_5168_, v_isMeta_5169_, v_val_5170_, v_expectedType_5165_, v_numParams_5344_, v___x_5345_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
lean_dec_ref(v_x_5172_);
if (lean_obj_tag(v___x_5346_) == 0)
{
size_t v_sz_5347_; size_t v___x_5348_; lean_object* v___x_5349_; 
lean_dec_ref(v___x_5346_);
v_sz_5347_ = lean_array_size(v_fst_5330_);
v___x_5348_ = ((size_t)0ULL);
v___x_5349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_5347_, v___x_5348_, v_fst_5330_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
if (lean_obj_tag(v___x_5349_) == 0)
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5358_; 
v_a_5350_ = lean_ctor_get(v___x_5349_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5352_ = v___x_5349_;
v_isShared_5353_ = v_isSharedCheck_5358_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5349_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5358_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5354_; lean_object* v___x_5356_; 
v___x_5354_ = l_Lean_mkAppN(v_x_5171_, v_a_5350_);
lean_dec(v_a_5350_);
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 0, v___x_5354_);
v___x_5356_ = v___x_5352_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5354_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
else
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5366_; 
lean_dec_ref(v_x_5171_);
v_a_5359_ = lean_ctor_get(v___x_5349_, 0);
v_isSharedCheck_5366_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5366_ == 0)
{
v___x_5361_ = v___x_5349_;
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___x_5349_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5364_; 
if (v_isShared_5362_ == 0)
{
v___x_5364_ = v___x_5361_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_a_5359_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_dec(v_fst_5330_);
lean_dec_ref(v_x_5171_);
v_a_5367_ = lean_ctor_get(v___x_5346_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5346_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5346_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5438_; 
lean_dec_ref(v_val_5323_);
lean_dec_ref(v_x_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_val_5170_);
lean_dec_ref(v_expectedType_5165_);
v_a_5431_ = lean_ctor_get(v___x_5327_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5433_ = v___x_5327_;
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5327_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5436_; 
if (v_isShared_5434_ == 0)
{
v___x_5436_ = v___x_5433_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
}
else
{
lean_dec_ref(v_val_5323_);
lean_dec_ref(v_x_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_val_5170_);
lean_dec_ref(v_expectedType_5165_);
return v___x_5324_;
}
}
else
{
lean_dec(v_a_5322_);
lean_dec_ref(v_x_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_val_5170_);
v___y_5298_ = v___y_5174_;
v___y_5299_ = v___y_5175_;
v___y_5300_ = v___y_5176_;
v___y_5301_ = v___y_5177_;
goto v___jp_5297_;
}
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
lean_dec_ref(v_x_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_val_5170_);
lean_dec_ref(v_expectedType_5165_);
lean_dec_ref(v_inst_5164_);
v_a_5439_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5321_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5321_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
v___jp_5297_:
{
lean_object* v_options_5302_; uint8_t v_hasTrace_5303_; 
v_options_5302_ = lean_ctor_get(v___y_5300_, 2);
v_hasTrace_5303_ = lean_ctor_get_uint8(v_options_5302_, sizeof(void*)*1);
if (v_hasTrace_5303_ == 0)
{
v___y_5219_ = v___y_5298_;
v___y_5220_ = v___y_5299_;
v___y_5221_ = v___y_5300_;
v_options_5222_ = v_options_5302_;
v___y_5223_ = v___y_5301_;
goto v___jp_5218_;
}
else
{
lean_object* v_inheritedTraceOptions_5304_; lean_object* v___x_5305_; uint8_t v___x_5306_; 
v_inheritedTraceOptions_5304_ = lean_ctor_get(v___y_5300_, 13);
v___x_5305_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5306_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5304_, v_options_5302_, v___x_5305_);
if (v___x_5306_ == 0)
{
v___y_5219_ = v___y_5298_;
v___y_5220_ = v___y_5299_;
v___y_5221_ = v___y_5300_;
v_options_5222_ = v_options_5302_;
v___y_5223_ = v___y_5301_;
goto v___jp_5218_;
}
else
{
lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___x_5307_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___closed__1);
lean_inc_ref(v_inst_5164_);
v___x_5308_ = l_Lean_MessageData_ofExpr(v_inst_5164_);
v___x_5309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5309_, 0, v___x_5307_);
lean_ctor_set(v___x_5309_, 1, v___x_5308_);
v___x_5310_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_5296_, v___x_5309_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_dec_ref(v___x_5310_);
v___y_5219_ = v___y_5298_;
v___y_5220_ = v___y_5299_;
v___y_5221_ = v___y_5300_;
v_options_5222_ = v_options_5302_;
v___y_5223_ = v___y_5301_;
goto v___jp_5218_;
}
else
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5318_; 
lean_dec_ref(v_expectedType_5165_);
lean_dec_ref(v_inst_5164_);
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5313_ = v___x_5310_;
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5310_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
if (v_isShared_5314_ == 0)
{
v___x_5316_ = v___x_5313_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5311_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
}
}
}
}
v___jp_5179_:
{
lean_object* v___x_5184_; 
v___x_5184_ = l_Lean_enableRealizationsForConst(v___y_5180_, v___y_5182_, v___y_5183_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5191_ == 0)
{
lean_object* v_unused_5192_; 
v_unused_5192_ = lean_ctor_get(v___x_5184_, 0);
lean_dec(v_unused_5192_);
v___x_5186_ = v___x_5184_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_dec(v___x_5184_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
lean_ctor_set(v___x_5186_, 0, v___y_5181_);
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___y_5181_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_dec_ref(v___y_5181_);
v_a_5193_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5184_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5184_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
v___jp_5201_:
{
if (v_compile_5167_ == 0)
{
v___y_5180_ = v___y_5202_;
v___y_5181_ = v___y_5203_;
v___y_5182_ = v___y_5204_;
v___y_5183_ = v___y_5205_;
goto v___jp_5179_;
}
else
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5206_ = lean_unsigned_to_nat(1u);
v___x_5207_ = lean_mk_empty_array_with_capacity(v___x_5206_);
lean_inc(v___y_5202_);
v___x_5208_ = lean_array_push(v___x_5207_, v___y_5202_);
v___x_5209_ = l_Lean_compileDecls(v___x_5208_, v_logCompileErrors_5168_, v___y_5204_, v___y_5205_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_dec_ref(v___x_5209_);
v___y_5180_ = v___y_5202_;
v___y_5181_ = v___y_5203_;
v___y_5182_ = v___y_5204_;
v___y_5183_ = v___y_5205_;
goto v___jp_5179_;
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5209_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5209_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
}
v___jp_5218_:
{
lean_object* v___x_5224_; uint8_t v___x_5225_; 
v___x_5224_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5225_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5222_, v___x_5224_);
if (v___x_5225_ == 0)
{
lean_object* v___x_5226_; 
lean_dec_ref(v_expectedType_5165_);
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v_inst_5164_);
return v___x_5226_;
}
else
{
lean_object* v___x_5227_; 
lean_inc(v___y_5223_);
lean_inc_ref(v___y_5221_);
lean_inc(v___y_5220_);
lean_inc_ref(v___y_5219_);
lean_inc_ref(v_inst_5164_);
v___x_5227_ = lean_infer_type(v_inst_5164_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5223_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5229_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref(v___x_5227_);
lean_inc_ref(v_expectedType_5165_);
v___x_5229_ = l_Lean_Meta_isExprDefEq(v_expectedType_5165_, v_a_5228_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5223_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5281_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5232_ = v___x_5229_;
v_isShared_5233_ = v_isSharedCheck_5281_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5229_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5281_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
uint8_t v___x_5234_; 
v___x_5234_ = lean_unbox(v_a_5230_);
if (v___x_5234_ == 0)
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v_a_5237_; uint8_t v___x_5238_; uint8_t v___x_5239_; lean_object* v___x_5240_; 
lean_del_object(v___x_5232_);
v___x_5235_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__1));
v___x_5236_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_5235_, v___y_5223_);
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
lean_inc_n(v_a_5237_, 2);
lean_dec_ref(v___x_5236_);
v___x_5238_ = lean_unbox(v_a_5230_);
v___x_5239_ = lean_unbox(v_a_5230_);
lean_dec(v_a_5230_);
v___x_5240_ = l_Lean_Meta_mkAuxDefinition(v_a_5237_, v_expectedType_5165_, v_inst_5164_, v___x_5238_, v___x_5239_, v___x_5166_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5223_);
if (lean_obj_tag(v___x_5240_) == 0)
{
if (v_isMeta_5169_ == 0)
{
lean_object* v_a_5241_; 
v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
lean_inc(v_a_5241_);
lean_dec_ref(v___x_5240_);
v___y_5202_ = v_a_5237_;
v___y_5203_ = v_a_5241_;
v___y_5204_ = v___y_5221_;
v___y_5205_ = v___y_5223_;
goto v___jp_5201_;
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5243_; lean_object* v_env_5244_; lean_object* v_nextMacroScope_5245_; lean_object* v_ngen_5246_; lean_object* v_auxDeclNGen_5247_; lean_object* v_traceState_5248_; lean_object* v_messages_5249_; lean_object* v_infoState_5250_; lean_object* v_snapshotTasks_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5276_; 
v_a_5242_ = lean_ctor_get(v___x_5240_, 0);
lean_inc(v_a_5242_);
lean_dec_ref(v___x_5240_);
v___x_5243_ = lean_st_ref_take(v___y_5223_);
v_env_5244_ = lean_ctor_get(v___x_5243_, 0);
v_nextMacroScope_5245_ = lean_ctor_get(v___x_5243_, 1);
v_ngen_5246_ = lean_ctor_get(v___x_5243_, 2);
v_auxDeclNGen_5247_ = lean_ctor_get(v___x_5243_, 3);
v_traceState_5248_ = lean_ctor_get(v___x_5243_, 4);
v_messages_5249_ = lean_ctor_get(v___x_5243_, 6);
v_infoState_5250_ = lean_ctor_get(v___x_5243_, 7);
v_snapshotTasks_5251_ = lean_ctor_get(v___x_5243_, 8);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5243_);
if (v_isSharedCheck_5276_ == 0)
{
lean_object* v_unused_5277_; 
v_unused_5277_ = lean_ctor_get(v___x_5243_, 5);
lean_dec(v_unused_5277_);
v___x_5253_ = v___x_5243_;
v_isShared_5254_ = v_isSharedCheck_5276_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_snapshotTasks_5251_);
lean_inc(v_infoState_5250_);
lean_inc(v_messages_5249_);
lean_inc(v_traceState_5248_);
lean_inc(v_auxDeclNGen_5247_);
lean_inc(v_ngen_5246_);
lean_inc(v_nextMacroScope_5245_);
lean_inc(v_env_5244_);
lean_dec(v___x_5243_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5276_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5258_; 
lean_inc(v_a_5237_);
v___x_5255_ = l_Lean_markMeta(v_env_5244_, v_a_5237_);
v___x_5256_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__4);
if (v_isShared_5254_ == 0)
{
lean_ctor_set(v___x_5253_, 5, v___x_5256_);
lean_ctor_set(v___x_5253_, 0, v___x_5255_);
v___x_5258_ = v___x_5253_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5255_);
lean_ctor_set(v_reuseFailAlloc_5275_, 1, v_nextMacroScope_5245_);
lean_ctor_set(v_reuseFailAlloc_5275_, 2, v_ngen_5246_);
lean_ctor_set(v_reuseFailAlloc_5275_, 3, v_auxDeclNGen_5247_);
lean_ctor_set(v_reuseFailAlloc_5275_, 4, v_traceState_5248_);
lean_ctor_set(v_reuseFailAlloc_5275_, 5, v___x_5256_);
lean_ctor_set(v_reuseFailAlloc_5275_, 6, v_messages_5249_);
lean_ctor_set(v_reuseFailAlloc_5275_, 7, v_infoState_5250_);
lean_ctor_set(v_reuseFailAlloc_5275_, 8, v_snapshotTasks_5251_);
v___x_5258_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v_mctx_5261_; lean_object* v_zetaDeltaFVarIds_5262_; lean_object* v_postponed_5263_; lean_object* v_diag_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5273_; 
v___x_5259_ = lean_st_ref_set(v___y_5223_, v___x_5258_);
v___x_5260_ = lean_st_ref_take(v___y_5220_);
v_mctx_5261_ = lean_ctor_get(v___x_5260_, 0);
v_zetaDeltaFVarIds_5262_ = lean_ctor_get(v___x_5260_, 2);
v_postponed_5263_ = lean_ctor_get(v___x_5260_, 3);
v_diag_5264_ = lean_ctor_get(v___x_5260_, 4);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5273_ == 0)
{
lean_object* v_unused_5274_; 
v_unused_5274_ = lean_ctor_get(v___x_5260_, 1);
lean_dec(v_unused_5274_);
v___x_5266_ = v___x_5260_;
v_isShared_5267_ = v_isSharedCheck_5273_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_diag_5264_);
lean_inc(v_postponed_5263_);
lean_inc(v_zetaDeltaFVarIds_5262_);
lean_inc(v_mctx_5261_);
lean_dec(v___x_5260_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5273_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5268_; lean_object* v___x_5270_; 
v___x_5268_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__1___closed__5);
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 1, v___x_5268_);
v___x_5270_ = v___x_5266_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_mctx_5261_);
lean_ctor_set(v_reuseFailAlloc_5272_, 1, v___x_5268_);
lean_ctor_set(v_reuseFailAlloc_5272_, 2, v_zetaDeltaFVarIds_5262_);
lean_ctor_set(v_reuseFailAlloc_5272_, 3, v_postponed_5263_);
lean_ctor_set(v_reuseFailAlloc_5272_, 4, v_diag_5264_);
v___x_5270_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
lean_object* v___x_5271_; 
v___x_5271_ = lean_st_ref_set(v___y_5220_, v___x_5270_);
v___y_5202_ = v_a_5237_;
v___y_5203_ = v_a_5242_;
v___y_5204_ = v___y_5221_;
v___y_5205_ = v___y_5223_;
goto v___jp_5201_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5237_);
return v___x_5240_;
}
}
else
{
lean_object* v___x_5279_; 
lean_dec(v_a_5230_);
lean_dec_ref(v_expectedType_5165_);
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 0, v_inst_5164_);
v___x_5279_ = v___x_5232_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_inst_5164_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
else
{
lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5289_; 
lean_dec_ref(v_expectedType_5165_);
lean_dec_ref(v_inst_5164_);
v_a_5282_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5284_ = v___x_5229_;
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v___x_5229_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___x_5287_; 
if (v_isShared_5285_ == 0)
{
v___x_5287_ = v___x_5284_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_a_5282_);
v___x_5287_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
return v___x_5287_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_5165_);
lean_dec_ref(v_inst_5164_);
return v___x_5227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object* v_expectedType_5447_, lean_object* v_inst_5448_, uint8_t v___x_5449_, uint8_t v_compile_5450_, uint8_t v_logCompileErrors_5451_, uint8_t v_isMeta_5452_, lean_object* v_val_5453_, lean_object* v_____r_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
lean_object* v___x_5460_; 
lean_inc_ref(v_expectedType_5447_);
v___x_5460_ = l_Lean_Meta_isProp(v_expectedType_5447_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5482_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5463_ = v___x_5460_;
v_isShared_5464_ = v_isSharedCheck_5482_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_a_5461_);
lean_dec(v___x_5460_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5482_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
uint8_t v___x_5465_; 
v___x_5465_ = lean_unbox(v_a_5461_);
lean_dec(v_a_5461_);
if (v___x_5465_ == 0)
{
lean_object* v___x_5466_; 
lean_del_object(v___x_5463_);
lean_inc(v___y_5458_);
lean_inc_ref(v___y_5457_);
lean_inc(v___y_5456_);
lean_inc_ref(v___y_5455_);
lean_inc_ref(v_inst_5448_);
v___x_5466_ = lean_whnf(v_inst_5448_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; lean_object* v_dummy_5468_; lean_object* v_nargs_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
lean_inc(v_a_5467_);
lean_dec_ref(v___x_5466_);
v_dummy_5468_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5469_ = l_Lean_Expr_getAppNumArgs(v_a_5467_);
lean_inc(v_nargs_5469_);
v___x_5470_ = lean_mk_array(v_nargs_5469_, v_dummy_5468_);
v___x_5471_ = lean_unsigned_to_nat(1u);
v___x_5472_ = lean_nat_sub(v_nargs_5469_, v___x_5471_);
lean_dec(v_nargs_5469_);
v___x_5473_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15(v_inst_5448_, v_expectedType_5447_, v___x_5449_, v_compile_5450_, v_logCompileErrors_5451_, v_isMeta_5452_, v_val_5453_, v_a_5467_, v___x_5470_, v___x_5472_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_);
lean_dec(v___x_5472_);
return v___x_5473_;
}
else
{
lean_dec(v_val_5453_);
lean_dec_ref(v_inst_5448_);
lean_dec_ref(v_expectedType_5447_);
return v___x_5466_;
}
}
else
{
lean_object* v_options_5474_; lean_object* v___x_5475_; uint8_t v___x_5476_; 
lean_dec(v_val_5453_);
v_options_5474_ = lean_ctor_get(v___y_5457_, 2);
v___x_5475_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5476_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5474_, v___x_5475_);
if (v___x_5476_ == 0)
{
lean_object* v___x_5478_; 
lean_dec_ref(v_expectedType_5447_);
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 0, v_inst_5448_);
v___x_5478_ = v___x_5463_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_inst_5448_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
else
{
lean_object* v___x_5480_; lean_object* v___x_5481_; 
lean_del_object(v___x_5463_);
v___x_5480_ = lean_box(0);
v___x_5481_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5447_, v_inst_5448_, v___x_5449_, v___x_5480_, v___x_5449_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_);
return v___x_5481_;
}
}
}
}
else
{
lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_dec(v_val_5453_);
lean_dec_ref(v_inst_5448_);
lean_dec_ref(v_expectedType_5447_);
v_a_5483_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5460_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_dec(v___x_5460_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object* v_inst_5491_, lean_object* v_expectedType_5492_, uint8_t v_compile_5493_, uint8_t v_logCompileErrors_5494_, uint8_t v_isMeta_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_){
_start:
{
lean_object* v___x_5501_; lean_object* v_options_5502_; uint8_t v_foApprox_5503_; uint8_t v_ctxApprox_5504_; uint8_t v_quasiPatternApprox_5505_; uint8_t v_constApprox_5506_; uint8_t v_isDefEqStuckEx_5507_; uint8_t v_unificationHints_5508_; uint8_t v_proofIrrelevance_5509_; uint8_t v_assignSyntheticOpaque_5510_; uint8_t v_offsetCnstrs_5511_; uint8_t v_etaStruct_5512_; uint8_t v_univApprox_5513_; uint8_t v_iota_5514_; uint8_t v_beta_5515_; uint8_t v_proj_5516_; uint8_t v_zeta_5517_; uint8_t v_zetaDelta_5518_; uint8_t v_zetaUnused_5519_; uint8_t v_zetaHave_5520_; lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5771_; 
v___x_5501_ = l_Lean_Meta_Context_config(v_a_5496_);
v_options_5502_ = lean_ctor_get(v_a_5498_, 2);
v_foApprox_5503_ = lean_ctor_get_uint8(v___x_5501_, 0);
v_ctxApprox_5504_ = lean_ctor_get_uint8(v___x_5501_, 1);
v_quasiPatternApprox_5505_ = lean_ctor_get_uint8(v___x_5501_, 2);
v_constApprox_5506_ = lean_ctor_get_uint8(v___x_5501_, 3);
v_isDefEqStuckEx_5507_ = lean_ctor_get_uint8(v___x_5501_, 4);
v_unificationHints_5508_ = lean_ctor_get_uint8(v___x_5501_, 5);
v_proofIrrelevance_5509_ = lean_ctor_get_uint8(v___x_5501_, 6);
v_assignSyntheticOpaque_5510_ = lean_ctor_get_uint8(v___x_5501_, 7);
v_offsetCnstrs_5511_ = lean_ctor_get_uint8(v___x_5501_, 8);
v_etaStruct_5512_ = lean_ctor_get_uint8(v___x_5501_, 10);
v_univApprox_5513_ = lean_ctor_get_uint8(v___x_5501_, 11);
v_iota_5514_ = lean_ctor_get_uint8(v___x_5501_, 12);
v_beta_5515_ = lean_ctor_get_uint8(v___x_5501_, 13);
v_proj_5516_ = lean_ctor_get_uint8(v___x_5501_, 14);
v_zeta_5517_ = lean_ctor_get_uint8(v___x_5501_, 15);
v_zetaDelta_5518_ = lean_ctor_get_uint8(v___x_5501_, 16);
v_zetaUnused_5519_ = lean_ctor_get_uint8(v___x_5501_, 17);
v_zetaHave_5520_ = lean_ctor_get_uint8(v___x_5501_, 18);
v_isSharedCheck_5771_ = !lean_is_exclusive(v___x_5501_);
if (v_isSharedCheck_5771_ == 0)
{
v___x_5522_ = v___x_5501_;
v_isShared_5523_ = v_isSharedCheck_5771_;
goto v_resetjp_5521_;
}
else
{
lean_dec(v___x_5501_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5771_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
uint8_t v_trackZetaDelta_5524_; lean_object* v_zetaDeltaSet_5525_; lean_object* v_lctx_5526_; lean_object* v_localInstances_5527_; lean_object* v_defEqCtx_x3f_5528_; lean_object* v_synthPendingDepth_5529_; lean_object* v_canUnfold_x3f_5530_; uint8_t v_univApprox_5531_; uint8_t v_inTypeClassResolution_5532_; uint8_t v_cacheInferType_5533_; lean_object* v_inheritedTraceOptions_5534_; uint8_t v_hasTrace_5535_; uint8_t v___x_5536_; lean_object* v_config_5538_; 
v_trackZetaDelta_5524_ = lean_ctor_get_uint8(v_a_5496_, sizeof(void*)*7);
v_zetaDeltaSet_5525_ = lean_ctor_get(v_a_5496_, 1);
v_lctx_5526_ = lean_ctor_get(v_a_5496_, 2);
v_localInstances_5527_ = lean_ctor_get(v_a_5496_, 3);
v_defEqCtx_x3f_5528_ = lean_ctor_get(v_a_5496_, 4);
v_synthPendingDepth_5529_ = lean_ctor_get(v_a_5496_, 5);
v_canUnfold_x3f_5530_ = lean_ctor_get(v_a_5496_, 6);
v_univApprox_5531_ = lean_ctor_get_uint8(v_a_5496_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5532_ = lean_ctor_get_uint8(v_a_5496_, sizeof(void*)*7 + 2);
v_cacheInferType_5533_ = lean_ctor_get_uint8(v_a_5496_, sizeof(void*)*7 + 3);
v_inheritedTraceOptions_5534_ = lean_ctor_get(v_a_5498_, 13);
v_hasTrace_5535_ = lean_ctor_get_uint8(v_options_5502_, sizeof(void*)*1);
v___x_5536_ = 3;
if (v_isShared_5523_ == 0)
{
v_config_5538_ = v___x_5522_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 0, v_foApprox_5503_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 1, v_ctxApprox_5504_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 2, v_quasiPatternApprox_5505_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 3, v_constApprox_5506_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 4, v_isDefEqStuckEx_5507_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 5, v_unificationHints_5508_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 6, v_proofIrrelevance_5509_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 7, v_assignSyntheticOpaque_5510_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 8, v_offsetCnstrs_5511_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 10, v_etaStruct_5512_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 11, v_univApprox_5513_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 12, v_iota_5514_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 13, v_beta_5515_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 14, v_proj_5516_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 15, v_zeta_5517_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 16, v_zetaDelta_5518_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 17, v_zetaUnused_5519_);
lean_ctor_set_uint8(v_reuseFailAlloc_5770_, 18, v_zetaHave_5520_);
v_config_5538_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
uint64_t v___x_5539_; uint64_t v___x_5540_; uint64_t v___x_5541_; uint64_t v___x_5542_; uint64_t v___x_5543_; uint64_t v_key_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; 
lean_ctor_set_uint8(v_config_5538_, 9, v___x_5536_);
v___x_5539_ = l_Lean_Meta_Context_configKey(v_a_5496_);
v___x_5540_ = 2ULL;
v___x_5541_ = lean_uint64_shift_right(v___x_5539_, v___x_5540_);
v___x_5542_ = lean_uint64_shift_left(v___x_5541_, v___x_5540_);
v___x_5543_ = lean_uint64_once(&l_Lean_Meta_wrapInstance___closed__0, &l_Lean_Meta_wrapInstance___closed__0_once, _init_l_Lean_Meta_wrapInstance___closed__0);
v_key_5544_ = lean_uint64_lor(v___x_5542_, v___x_5543_);
v___x_5545_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5545_, 0, v_config_5538_);
lean_ctor_set_uint64(v___x_5545_, sizeof(void*)*1, v_key_5544_);
lean_inc(v_canUnfold_x3f_5530_);
lean_inc(v_synthPendingDepth_5529_);
lean_inc(v_defEqCtx_x3f_5528_);
lean_inc_ref(v_localInstances_5527_);
lean_inc_ref(v_lctx_5526_);
lean_inc(v_zetaDeltaSet_5525_);
v___x_5546_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5546_, 0, v___x_5545_);
lean_ctor_set(v___x_5546_, 1, v_zetaDeltaSet_5525_);
lean_ctor_set(v___x_5546_, 2, v_lctx_5526_);
lean_ctor_set(v___x_5546_, 3, v_localInstances_5527_);
lean_ctor_set(v___x_5546_, 4, v_defEqCtx_x3f_5528_);
lean_ctor_set(v___x_5546_, 5, v_synthPendingDepth_5529_);
lean_ctor_set(v___x_5546_, 6, v_canUnfold_x3f_5530_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*7, v_trackZetaDelta_5524_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*7 + 1, v_univApprox_5531_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5532_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*7 + 3, v_cacheInferType_5533_);
if (v_hasTrace_5535_ == 0)
{
lean_object* v___x_5547_; 
lean_inc_ref(v_expectedType_5492_);
v___x_5547_ = l_Lean_Meta_isClass_x3f(v_expectedType_5492_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5586_; 
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5550_ = v___x_5547_;
v_isShared_5551_ = v_isSharedCheck_5586_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5547_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5586_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
if (lean_obj_tag(v_a_5548_) == 1)
{
lean_object* v_val_5552_; lean_object* v___x_5553_; 
lean_del_object(v___x_5550_);
v_val_5552_ = lean_ctor_get(v_a_5548_, 0);
lean_inc(v_val_5552_);
lean_dec_ref(v_a_5548_);
lean_inc_ref(v_expectedType_5492_);
v___x_5553_ = l_Lean_Meta_isProp(v_expectedType_5492_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5574_; 
v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5556_ = v___x_5553_;
v_isShared_5557_ = v_isSharedCheck_5574_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5553_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5574_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
uint8_t v___x_5558_; 
v___x_5558_ = lean_unbox(v_a_5554_);
lean_dec(v_a_5554_);
if (v___x_5558_ == 0)
{
lean_object* v___x_5559_; 
lean_del_object(v___x_5556_);
lean_inc(v_a_5499_);
lean_inc_ref(v_a_5498_);
lean_inc(v_a_5497_);
lean_inc_ref(v___x_5546_);
lean_inc_ref(v_inst_5491_);
v___x_5559_ = lean_whnf(v_inst_5491_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_a_5560_; lean_object* v_dummy_5561_; lean_object* v_nargs_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_a_5560_);
lean_dec_ref(v___x_5559_);
v_dummy_5561_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5562_ = l_Lean_Expr_getAppNumArgs(v_a_5560_);
lean_inc(v_nargs_5562_);
v___x_5563_ = lean_mk_array(v_nargs_5562_, v_dummy_5561_);
v___x_5564_ = lean_unsigned_to_nat(1u);
v___x_5565_ = lean_nat_sub(v_nargs_5562_, v___x_5564_);
lean_dec(v_nargs_5562_);
v___x_5566_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(v_inst_5491_, v_expectedType_5492_, v_hasTrace_5535_, v_compile_5493_, v_logCompileErrors_5494_, v_isMeta_5495_, v_val_5552_, v_a_5560_, v___x_5563_, v___x_5565_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
lean_dec_ref(v___x_5546_);
lean_dec(v___x_5565_);
return v___x_5566_;
}
else
{
lean_dec(v_val_5552_);
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
return v___x_5559_;
}
}
else
{
lean_object* v___x_5567_; uint8_t v___x_5568_; 
lean_dec(v_val_5552_);
v___x_5567_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5568_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5502_, v___x_5567_);
if (v___x_5568_ == 0)
{
lean_object* v___x_5570_; 
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 0, v_inst_5491_);
v___x_5570_ = v___x_5556_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_inst_5491_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
else
{
lean_object* v___x_5572_; lean_object* v___x_5573_; 
lean_del_object(v___x_5556_);
v___x_5572_ = lean_box(0);
v___x_5573_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5492_, v_inst_5491_, v___x_5568_, v___x_5572_, v___x_5568_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
lean_dec_ref(v___x_5546_);
return v___x_5573_;
}
}
}
}
else
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
lean_dec(v_val_5552_);
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5575_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5553_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5553_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
else
{
lean_object* v___x_5584_; 
lean_dec(v_a_5548_);
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 0, v_inst_5491_);
v___x_5584_ = v___x_5550_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_inst_5491_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5587_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5547_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___x_5547_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
}
}
else
{
lean_object* v___f_5595_; lean_object* v_cls_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; uint8_t v___x_5599_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v_a_5603_; lean_object* v___y_5613_; lean_object* v___y_5614_; lean_object* v_a_5615_; lean_object* v___y_5618_; lean_object* v___y_5619_; lean_object* v_a_5620_; lean_object* v___y_5623_; lean_object* v___y_5624_; lean_object* v___y_5625_; lean_object* v___y_5629_; lean_object* v___y_5630_; lean_object* v_a_5631_; lean_object* v___y_5644_; lean_object* v___y_5645_; lean_object* v_a_5646_; lean_object* v___y_5649_; lean_object* v___y_5650_; lean_object* v_a_5651_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; 
lean_inc_ref(v_expectedType_5492_);
v___f_5595_ = lean_alloc_closure((void*)(l_Lean_Meta_wrapInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5595_, 0, v_expectedType_5492_);
v_cls_5596_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5597_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_5598_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5599_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5534_, v_options_5502_, v___x_5598_);
if (v___x_5599_ == 0)
{
lean_object* v___x_5702_; uint8_t v___x_5703_; 
v___x_5702_ = l_Lean_trace_profiler;
v___x_5703_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5502_, v___x_5702_);
if (v___x_5703_ == 0)
{
lean_object* v___x_5704_; 
lean_dec_ref(v___f_5595_);
lean_inc_ref(v_expectedType_5492_);
v___x_5704_ = l_Lean_Meta_isClass_x3f(v_expectedType_5492_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5704_) == 0)
{
lean_object* v_a_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5761_; 
v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5761_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5761_ == 0)
{
v___x_5707_ = v___x_5704_;
v_isShared_5708_ = v_isSharedCheck_5761_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_a_5705_);
lean_dec(v___x_5704_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5761_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
if (lean_obj_tag(v_a_5705_) == 1)
{
lean_object* v_val_5709_; lean_object* v___y_5711_; lean_object* v___y_5712_; lean_object* v___y_5713_; lean_object* v___y_5714_; 
lean_del_object(v___x_5707_);
v_val_5709_ = lean_ctor_get(v_a_5705_, 0);
lean_inc(v_val_5709_);
lean_dec_ref(v_a_5705_);
if (v___x_5599_ == 0)
{
v___y_5711_ = v___x_5546_;
v___y_5712_ = v_a_5497_;
v___y_5713_ = v_a_5498_;
v___y_5714_ = v_a_5499_;
goto v___jp_5710_;
}
else
{
lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5746_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
lean_inc(v_val_5709_);
v___x_5747_ = l_Lean_MessageData_ofName(v_val_5709_);
v___x_5748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5746_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
v___x_5749_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_5596_, v___x_5748_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5749_) == 0)
{
lean_dec_ref(v___x_5749_);
v___y_5711_ = v___x_5546_;
v___y_5712_ = v_a_5497_;
v___y_5713_ = v_a_5498_;
v___y_5714_ = v_a_5499_;
goto v___jp_5710_;
}
else
{
lean_object* v_a_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5757_; 
lean_dec(v_val_5709_);
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5749_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5752_ = v___x_5749_;
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_a_5750_);
lean_dec(v___x_5749_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v___x_5755_; 
if (v_isShared_5753_ == 0)
{
v___x_5755_ = v___x_5752_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
}
v___jp_5710_:
{
lean_object* v___x_5715_; 
lean_inc_ref(v_expectedType_5492_);
v___x_5715_ = l_Lean_Meta_isProp(v_expectedType_5492_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
if (lean_obj_tag(v___x_5715_) == 0)
{
lean_object* v_a_5716_; lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5737_; 
v_a_5716_ = lean_ctor_get(v___x_5715_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5715_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5718_ = v___x_5715_;
v_isShared_5719_ = v_isSharedCheck_5737_;
goto v_resetjp_5717_;
}
else
{
lean_inc(v_a_5716_);
lean_dec(v___x_5715_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5737_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
uint8_t v___x_5720_; 
v___x_5720_ = lean_unbox(v_a_5716_);
lean_dec(v_a_5716_);
if (v___x_5720_ == 0)
{
lean_object* v___x_5721_; 
lean_del_object(v___x_5718_);
lean_inc(v___y_5714_);
lean_inc_ref(v___y_5713_);
lean_inc(v___y_5712_);
lean_inc_ref(v___y_5711_);
lean_inc_ref(v_inst_5491_);
v___x_5721_ = lean_whnf(v_inst_5491_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v_a_5722_; lean_object* v_dummy_5723_; lean_object* v_nargs_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; 
v_a_5722_ = lean_ctor_get(v___x_5721_, 0);
lean_inc(v_a_5722_);
lean_dec_ref(v___x_5721_);
v_dummy_5723_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5724_ = l_Lean_Expr_getAppNumArgs(v_a_5722_);
lean_inc(v_nargs_5724_);
v___x_5725_ = lean_mk_array(v_nargs_5724_, v_dummy_5723_);
v___x_5726_ = lean_unsigned_to_nat(1u);
v___x_5727_ = lean_nat_sub(v_nargs_5724_, v___x_5726_);
lean_dec(v_nargs_5724_);
v___x_5728_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13(v_inst_5491_, v_expectedType_5492_, v___x_5703_, v_hasTrace_5535_, v_compile_5493_, v_logCompileErrors_5494_, v_isMeta_5495_, v_val_5709_, v_a_5722_, v___x_5725_, v___x_5727_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
lean_dec_ref(v___y_5711_);
lean_dec(v___x_5727_);
return v___x_5728_;
}
else
{
lean_dec_ref(v___y_5711_);
lean_dec(v_val_5709_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
return v___x_5721_;
}
}
else
{
lean_object* v_options_5729_; lean_object* v___x_5730_; uint8_t v___x_5731_; 
lean_dec(v_val_5709_);
v_options_5729_ = lean_ctor_get(v___y_5713_, 2);
v___x_5730_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5731_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5729_, v___x_5730_);
if (v___x_5731_ == 0)
{
lean_object* v___x_5733_; 
lean_dec_ref(v___y_5711_);
lean_dec_ref(v_expectedType_5492_);
if (v_isShared_5719_ == 0)
{
lean_ctor_set(v___x_5718_, 0, v_inst_5491_);
v___x_5733_ = v___x_5718_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5734_; 
v_reuseFailAlloc_5734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5734_, 0, v_inst_5491_);
v___x_5733_ = v_reuseFailAlloc_5734_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
return v___x_5733_;
}
}
else
{
lean_object* v___x_5735_; lean_object* v___x_5736_; 
lean_del_object(v___x_5718_);
v___x_5735_ = lean_box(0);
v___x_5736_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5492_, v_inst_5491_, v_hasTrace_5535_, v___x_5735_, v_hasTrace_5535_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
lean_dec_ref(v___y_5711_);
return v___x_5736_;
}
}
}
}
else
{
lean_object* v_a_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5745_; 
lean_dec_ref(v___y_5711_);
lean_dec(v_val_5709_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5738_ = lean_ctor_get(v___x_5715_, 0);
v_isSharedCheck_5745_ = !lean_is_exclusive(v___x_5715_);
if (v_isSharedCheck_5745_ == 0)
{
v___x_5740_ = v___x_5715_;
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_a_5738_);
lean_dec(v___x_5715_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5743_; 
if (v_isShared_5741_ == 0)
{
v___x_5743_ = v___x_5740_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_a_5738_);
v___x_5743_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
return v___x_5743_;
}
}
}
}
}
else
{
lean_object* v___x_5759_; 
lean_dec(v_a_5705_);
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
if (v_isShared_5708_ == 0)
{
lean_ctor_set(v___x_5707_, 0, v_inst_5491_);
v___x_5759_ = v___x_5707_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v_inst_5491_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
}
else
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5769_; 
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5762_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5764_ = v___x_5704_;
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5704_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5767_; 
if (v_isShared_5765_ == 0)
{
v___x_5767_ = v___x_5764_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
}
else
{
goto v___jp_5659_;
}
}
else
{
goto v___jp_5659_;
}
v___jp_5600_:
{
lean_object* v___x_5604_; double v___x_5605_; double v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5604_ = lean_io_get_num_heartbeats();
v___x_5605_ = lean_float_of_nat(v___y_5602_);
v___x_5606_ = lean_float_of_nat(v___x_5604_);
v___x_5607_ = lean_box_float(v___x_5605_);
v___x_5608_ = lean_box_float(v___x_5606_);
v___x_5609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5607_);
lean_ctor_set(v___x_5609_, 1, v___x_5608_);
v___x_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5610_, 0, v_a_5603_);
lean_ctor_set(v___x_5610_, 1, v___x_5609_);
v___x_5611_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11(v_cls_5596_, v_hasTrace_5535_, v___x_5597_, v_options_5502_, v___x_5599_, v___y_5601_, v___f_5595_, v___x_5610_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
lean_dec_ref(v___x_5546_);
return v___x_5611_;
}
v___jp_5612_:
{
lean_object* v___x_5616_; 
v___x_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5616_, 0, v_a_5615_);
v___y_5601_ = v___y_5613_;
v___y_5602_ = v___y_5614_;
v_a_5603_ = v___x_5616_;
goto v___jp_5600_;
}
v___jp_5617_:
{
lean_object* v___x_5621_; 
v___x_5621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5621_, 0, v_a_5620_);
v___y_5601_ = v___y_5618_;
v___y_5602_ = v___y_5619_;
v_a_5603_ = v___x_5621_;
goto v___jp_5600_;
}
v___jp_5622_:
{
if (lean_obj_tag(v___y_5625_) == 0)
{
lean_object* v_a_5626_; 
v_a_5626_ = lean_ctor_get(v___y_5625_, 0);
lean_inc(v_a_5626_);
lean_dec_ref(v___y_5625_);
v___y_5613_ = v___y_5623_;
v___y_5614_ = v___y_5624_;
v_a_5615_ = v_a_5626_;
goto v___jp_5612_;
}
else
{
lean_object* v_a_5627_; 
v_a_5627_ = lean_ctor_get(v___y_5625_, 0);
lean_inc(v_a_5627_);
lean_dec_ref(v___y_5625_);
v___y_5618_ = v___y_5623_;
v___y_5619_ = v___y_5624_;
v_a_5620_ = v_a_5627_;
goto v___jp_5617_;
}
}
v___jp_5628_:
{
lean_object* v___x_5632_; double v___x_5633_; double v___x_5634_; double v___x_5635_; double v___x_5636_; double v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5632_ = lean_io_mono_nanos_now();
v___x_5633_ = lean_float_of_nat(v___y_5630_);
v___x_5634_ = lean_float_once(&l_Lean_Meta_wrapInstance___closed__1, &l_Lean_Meta_wrapInstance___closed__1_once, _init_l_Lean_Meta_wrapInstance___closed__1);
v___x_5635_ = lean_float_div(v___x_5633_, v___x_5634_);
v___x_5636_ = lean_float_of_nat(v___x_5632_);
v___x_5637_ = lean_float_div(v___x_5636_, v___x_5634_);
v___x_5638_ = lean_box_float(v___x_5635_);
v___x_5639_ = lean_box_float(v___x_5637_);
v___x_5640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5638_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5641_, 0, v_a_5631_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11(v_cls_5596_, v_hasTrace_5535_, v___x_5597_, v_options_5502_, v___x_5599_, v___y_5629_, v___f_5595_, v___x_5641_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
lean_dec_ref(v___x_5546_);
return v___x_5642_;
}
v___jp_5643_:
{
lean_object* v___x_5647_; 
v___x_5647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5647_, 0, v_a_5646_);
v___y_5629_ = v___y_5644_;
v___y_5630_ = v___y_5645_;
v_a_5631_ = v___x_5647_;
goto v___jp_5628_;
}
v___jp_5648_:
{
lean_object* v___x_5652_; 
v___x_5652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5652_, 0, v_a_5651_);
v___y_5629_ = v___y_5649_;
v___y_5630_ = v___y_5650_;
v_a_5631_ = v___x_5652_;
goto v___jp_5628_;
}
v___jp_5653_:
{
if (lean_obj_tag(v___y_5656_) == 0)
{
lean_object* v_a_5657_; 
v_a_5657_ = lean_ctor_get(v___y_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref(v___y_5656_);
v___y_5649_ = v___y_5654_;
v___y_5650_ = v___y_5655_;
v_a_5651_ = v_a_5657_;
goto v___jp_5648_;
}
else
{
lean_object* v_a_5658_; 
v_a_5658_ = lean_ctor_get(v___y_5656_, 0);
lean_inc(v_a_5658_);
lean_dec_ref(v___y_5656_);
v___y_5644_ = v___y_5654_;
v___y_5645_ = v___y_5655_;
v_a_5646_ = v_a_5658_;
goto v___jp_5643_;
}
}
v___jp_5659_:
{
lean_object* v___x_5660_; 
v___x_5660_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v_a_5499_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_object* v_a_5661_; lean_object* v___x_5662_; uint8_t v___x_5663_; 
v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
lean_inc(v_a_5661_);
lean_dec_ref(v___x_5660_);
v___x_5662_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5663_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5502_, v___x_5662_);
if (v___x_5663_ == 0)
{
lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___x_5664_ = lean_io_mono_nanos_now();
lean_inc_ref(v_expectedType_5492_);
v___x_5665_ = l_Lean_Meta_isClass_x3f(v_expectedType_5492_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5665_) == 0)
{
lean_object* v_a_5666_; 
v_a_5666_ = lean_ctor_get(v___x_5665_, 0);
lean_inc(v_a_5666_);
lean_dec_ref(v___x_5665_);
if (lean_obj_tag(v_a_5666_) == 1)
{
if (v___x_5599_ == 0)
{
lean_object* v_val_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; 
v_val_5667_ = lean_ctor_get(v_a_5666_, 0);
lean_inc(v_val_5667_);
lean_dec_ref(v_a_5666_);
v___x_5668_ = lean_box(0);
v___x_5669_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5492_, v_inst_5491_, v___x_5663_, v_hasTrace_5535_, v_compile_5493_, v_logCompileErrors_5494_, v_isMeta_5495_, v_val_5667_, v___x_5668_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
v___y_5654_ = v_a_5661_;
v___y_5655_ = v___x_5664_;
v___y_5656_ = v___x_5669_;
goto v___jp_5653_;
}
else
{
lean_object* v_val_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; 
v_val_5670_ = lean_ctor_get(v_a_5666_, 0);
lean_inc_n(v_val_5670_, 2);
lean_dec_ref(v_a_5666_);
v___x_5671_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5672_ = l_Lean_MessageData_ofName(v_val_5670_);
v___x_5673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5671_);
lean_ctor_set(v___x_5673_, 1, v___x_5672_);
v___x_5674_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_5596_, v___x_5673_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5674_) == 0)
{
lean_object* v_a_5675_; lean_object* v___x_5676_; 
v_a_5675_ = lean_ctor_get(v___x_5674_, 0);
lean_inc(v_a_5675_);
lean_dec_ref(v___x_5674_);
v___x_5676_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5492_, v_inst_5491_, v___x_5663_, v_hasTrace_5535_, v_compile_5493_, v_logCompileErrors_5494_, v_isMeta_5495_, v_val_5670_, v_a_5675_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
v___y_5654_ = v_a_5661_;
v___y_5655_ = v___x_5664_;
v___y_5656_ = v___x_5676_;
goto v___jp_5653_;
}
else
{
lean_object* v_a_5677_; 
lean_dec(v_val_5670_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5677_ = lean_ctor_get(v___x_5674_, 0);
lean_inc(v_a_5677_);
lean_dec_ref(v___x_5674_);
v___y_5644_ = v_a_5661_;
v___y_5645_ = v___x_5664_;
v_a_5646_ = v_a_5677_;
goto v___jp_5643_;
}
}
}
else
{
lean_dec(v_a_5666_);
lean_dec_ref(v_expectedType_5492_);
v___y_5649_ = v_a_5661_;
v___y_5650_ = v___x_5664_;
v_a_5651_ = v_inst_5491_;
goto v___jp_5648_;
}
}
else
{
lean_object* v_a_5678_; 
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5678_ = lean_ctor_get(v___x_5665_, 0);
lean_inc(v_a_5678_);
lean_dec_ref(v___x_5665_);
v___y_5644_ = v_a_5661_;
v___y_5645_ = v___x_5664_;
v_a_5646_ = v_a_5678_;
goto v___jp_5643_;
}
}
else
{
lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5679_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_expectedType_5492_);
v___x_5680_ = l_Lean_Meta_isClass_x3f(v_expectedType_5492_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5680_) == 0)
{
lean_object* v_a_5681_; 
v_a_5681_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_a_5681_);
lean_dec_ref(v___x_5680_);
if (lean_obj_tag(v_a_5681_) == 1)
{
if (v___x_5599_ == 0)
{
lean_object* v_val_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; 
v_val_5682_ = lean_ctor_get(v_a_5681_, 0);
lean_inc(v_val_5682_);
lean_dec_ref(v_a_5681_);
v___x_5683_ = lean_box(0);
v___x_5684_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5492_, v_inst_5491_, v___x_5663_, v_compile_5493_, v_logCompileErrors_5494_, v_isMeta_5495_, v_val_5682_, v___x_5683_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
v___y_5623_ = v_a_5661_;
v___y_5624_ = v___x_5679_;
v___y_5625_ = v___x_5684_;
goto v___jp_5622_;
}
else
{
lean_object* v_val_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v_val_5685_ = lean_ctor_get(v_a_5681_, 0);
lean_inc_n(v_val_5685_, 2);
lean_dec_ref(v_a_5681_);
v___x_5686_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5687_ = l_Lean_MessageData_ofName(v_val_5685_);
v___x_5688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5686_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__2(v_cls_5596_, v___x_5688_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
if (lean_obj_tag(v___x_5689_) == 0)
{
lean_object* v_a_5690_; lean_object* v___x_5691_; 
v_a_5690_ = lean_ctor_get(v___x_5689_, 0);
lean_inc(v_a_5690_);
lean_dec_ref(v___x_5689_);
v___x_5691_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5492_, v_inst_5491_, v___x_5663_, v_compile_5493_, v_logCompileErrors_5494_, v_isMeta_5495_, v_val_5685_, v_a_5690_, v___x_5546_, v_a_5497_, v_a_5498_, v_a_5499_);
v___y_5623_ = v_a_5661_;
v___y_5624_ = v___x_5679_;
v___y_5625_ = v___x_5691_;
goto v___jp_5622_;
}
else
{
lean_object* v_a_5692_; 
lean_dec(v_val_5685_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5692_ = lean_ctor_get(v___x_5689_, 0);
lean_inc(v_a_5692_);
lean_dec_ref(v___x_5689_);
v___y_5618_ = v_a_5661_;
v___y_5619_ = v___x_5679_;
v_a_5620_ = v_a_5692_;
goto v___jp_5617_;
}
}
}
else
{
lean_dec(v_a_5681_);
lean_dec_ref(v_expectedType_5492_);
v___y_5613_ = v_a_5661_;
v___y_5614_ = v___x_5679_;
v_a_5615_ = v_inst_5491_;
goto v___jp_5612_;
}
}
else
{
lean_object* v_a_5693_; 
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5693_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_a_5693_);
lean_dec_ref(v___x_5680_);
v___y_5618_ = v_a_5661_;
v___y_5619_ = v___x_5679_;
v_a_5620_ = v_a_5693_;
goto v___jp_5617_;
}
}
}
else
{
lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5701_; 
lean_dec_ref(v___f_5595_);
lean_dec_ref(v___x_5546_);
lean_dec_ref(v_expectedType_5492_);
lean_dec_ref(v_inst_5491_);
v_a_5694_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5696_ = v___x_5660_;
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___x_5660_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(lean_object* v___x_5772_, lean_object* v_a_5773_, uint8_t v_compile_5774_, uint8_t v_logCompileErrors_5775_, uint8_t v_isMeta_5776_, lean_object* v___x_5777_, lean_object* v___x_5778_, lean_object* v_____r_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_){
_start:
{
lean_object* v___x_5785_; 
v___x_5785_ = l_Lean_Meta_wrapInstance(v___x_5772_, v_a_5773_, v_compile_5774_, v_logCompileErrors_5775_, v_isMeta_5776_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
if (lean_obj_tag(v___x_5785_) == 0)
{
lean_object* v_a_5786_; lean_object* v___x_5787_; 
v_a_5786_ = lean_ctor_get(v___x_5785_, 0);
lean_inc(v_a_5786_);
lean_dec_ref(v___x_5785_);
v___x_5787_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_5777_, v_a_5786_, v___y_5781_);
if (lean_obj_tag(v___x_5787_) == 0)
{
lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5795_; 
v_isSharedCheck_5795_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5795_ == 0)
{
lean_object* v_unused_5796_; 
v_unused_5796_ = lean_ctor_get(v___x_5787_, 0);
lean_dec(v_unused_5796_);
v___x_5789_ = v___x_5787_;
v_isShared_5790_ = v_isSharedCheck_5795_;
goto v_resetjp_5788_;
}
else
{
lean_dec(v___x_5787_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5795_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___x_5791_; lean_object* v___x_5793_; 
v___x_5791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5791_, 0, v___x_5778_);
if (v_isShared_5790_ == 0)
{
lean_ctor_set(v___x_5789_, 0, v___x_5791_);
v___x_5793_ = v___x_5789_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
return v___x_5793_;
}
}
}
else
{
lean_object* v_a_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5804_; 
v_a_5797_ = lean_ctor_get(v___x_5787_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5799_ = v___x_5787_;
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_a_5797_);
lean_dec(v___x_5787_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5802_; 
if (v_isShared_5800_ == 0)
{
v___x_5802_ = v___x_5799_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5797_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
}
else
{
lean_object* v_a_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5812_; 
lean_dec(v___x_5777_);
v_a_5805_ = lean_ctor_get(v___x_5785_, 0);
v_isSharedCheck_5812_ = !lean_is_exclusive(v___x_5785_);
if (v_isSharedCheck_5812_ == 0)
{
v___x_5807_ = v___x_5785_;
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_a_5805_);
lean_dec(v___x_5785_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5810_; 
if (v_isShared_5808_ == 0)
{
v___x_5810_ = v___x_5807_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v_a_5805_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4___boxed(lean_object* v___x_5813_, lean_object* v_a_5814_, lean_object* v_compile_5815_, lean_object* v_logCompileErrors_5816_, lean_object* v_isMeta_5817_, lean_object* v___x_5818_, lean_object* v___x_5819_, lean_object* v_____r_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_){
_start:
{
uint8_t v_compile_boxed_5826_; uint8_t v_logCompileErrors_boxed_5827_; uint8_t v_isMeta_boxed_5828_; lean_object* v_res_5829_; 
v_compile_boxed_5826_ = lean_unbox(v_compile_5815_);
v_logCompileErrors_boxed_5827_ = lean_unbox(v_logCompileErrors_5816_);
v_isMeta_boxed_5828_ = lean_unbox(v_isMeta_5817_);
v_res_5829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___lam__4(v___x_5813_, v_a_5814_, v_compile_boxed_5826_, v_logCompileErrors_boxed_5827_, v_isMeta_boxed_5828_, v___x_5818_, v___x_5819_, v_____r_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_);
lean_dec(v___y_5824_);
lean_dec_ref(v___y_5823_);
lean_dec(v___y_5822_);
lean_dec_ref(v___y_5821_);
return v_res_5829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object* v_expectedType_5830_, lean_object* v_inst_5831_, lean_object* v___x_5832_, lean_object* v_hasTrace_5833_, lean_object* v_compile_5834_, lean_object* v_logCompileErrors_5835_, lean_object* v_isMeta_5836_, lean_object* v_val_5837_, lean_object* v_____r_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
uint8_t v___x_161530__boxed_5844_; uint8_t v_hasTrace_boxed_5845_; uint8_t v_compile_boxed_5846_; uint8_t v_logCompileErrors_boxed_5847_; uint8_t v_isMeta_boxed_5848_; lean_object* v_res_5849_; 
v___x_161530__boxed_5844_ = lean_unbox(v___x_5832_);
v_hasTrace_boxed_5845_ = lean_unbox(v_hasTrace_5833_);
v_compile_boxed_5846_ = lean_unbox(v_compile_5834_);
v_logCompileErrors_boxed_5847_ = lean_unbox(v_logCompileErrors_5835_);
v_isMeta_boxed_5848_ = lean_unbox(v_isMeta_5836_);
v_res_5849_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5830_, v_inst_5831_, v___x_161530__boxed_5844_, v_hasTrace_boxed_5845_, v_compile_boxed_5846_, v_logCompileErrors_boxed_5847_, v_isMeta_boxed_5848_, v_val_5837_, v_____r_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
return v_res_5849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object* v_expectedType_5850_, lean_object* v_inst_5851_, lean_object* v___x_5852_, lean_object* v_compile_5853_, lean_object* v_logCompileErrors_5854_, lean_object* v_isMeta_5855_, lean_object* v_val_5856_, lean_object* v_____r_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_){
_start:
{
uint8_t v___x_161555__boxed_5863_; uint8_t v_compile_boxed_5864_; uint8_t v_logCompileErrors_boxed_5865_; uint8_t v_isMeta_boxed_5866_; lean_object* v_res_5867_; 
v___x_161555__boxed_5863_ = lean_unbox(v___x_5852_);
v_compile_boxed_5864_ = lean_unbox(v_compile_5853_);
v_logCompileErrors_boxed_5865_ = lean_unbox(v_logCompileErrors_5854_);
v_isMeta_boxed_5866_ = lean_unbox(v_isMeta_5855_);
v_res_5867_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5850_, v_inst_5851_, v___x_161555__boxed_5863_, v_compile_boxed_5864_, v_logCompileErrors_boxed_5865_, v_isMeta_boxed_5866_, v_val_5856_, v_____r_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
lean_dec(v___y_5859_);
lean_dec_ref(v___y_5858_);
return v_res_5867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21___boxed(lean_object* v_inst_5868_, lean_object* v_expectedType_5869_, lean_object* v___x_5870_, lean_object* v___x_5871_, lean_object* v_compile_5872_, lean_object* v_logCompileErrors_5873_, lean_object* v_isMeta_5874_, lean_object* v_val_5875_, lean_object* v_x_5876_, lean_object* v_x_5877_, lean_object* v_x_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_){
_start:
{
uint8_t v___x_161592__boxed_5884_; uint8_t v___x_161593__boxed_5885_; uint8_t v_compile_boxed_5886_; uint8_t v_logCompileErrors_boxed_5887_; uint8_t v_isMeta_boxed_5888_; lean_object* v_res_5889_; 
v___x_161592__boxed_5884_ = lean_unbox(v___x_5870_);
v___x_161593__boxed_5885_ = lean_unbox(v___x_5871_);
v_compile_boxed_5886_ = lean_unbox(v_compile_5872_);
v_logCompileErrors_boxed_5887_ = lean_unbox(v_logCompileErrors_5873_);
v_isMeta_boxed_5888_ = lean_unbox(v_isMeta_5874_);
v_res_5889_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13_spec__21(v_inst_5868_, v_expectedType_5869_, v___x_161592__boxed_5884_, v___x_161593__boxed_5885_, v_compile_boxed_5886_, v_logCompileErrors_boxed_5887_, v_isMeta_boxed_5888_, v_val_5875_, v_x_5876_, v_x_5877_, v_x_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_);
lean_dec(v___y_5882_);
lean_dec_ref(v___y_5881_);
lean_dec(v___y_5880_);
lean_dec_ref(v___y_5879_);
return v_res_5889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15_spec__24___boxed(lean_object* v_inst_5890_, lean_object* v_expectedType_5891_, lean_object* v___x_5892_, lean_object* v_compile_5893_, lean_object* v_logCompileErrors_5894_, lean_object* v_isMeta_5895_, lean_object* v_val_5896_, lean_object* v_x_5897_, lean_object* v_x_5898_, lean_object* v_x_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_){
_start:
{
uint8_t v___x_161746__boxed_5905_; uint8_t v_compile_boxed_5906_; uint8_t v_logCompileErrors_boxed_5907_; uint8_t v_isMeta_boxed_5908_; lean_object* v_res_5909_; 
v___x_161746__boxed_5905_ = lean_unbox(v___x_5892_);
v_compile_boxed_5906_ = lean_unbox(v_compile_5893_);
v_logCompileErrors_boxed_5907_ = lean_unbox(v_logCompileErrors_5894_);
v_isMeta_boxed_5908_ = lean_unbox(v_isMeta_5895_);
v_res_5909_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15_spec__24(v_inst_5890_, v_expectedType_5891_, v___x_161746__boxed_5905_, v_compile_boxed_5906_, v_logCompileErrors_boxed_5907_, v_isMeta_boxed_5908_, v_val_5896_, v_x_5897_, v_x_5898_, v_x_5899_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_);
lean_dec(v___y_5903_);
lean_dec_ref(v___y_5902_);
lean_dec(v___y_5901_);
lean_dec_ref(v___y_5900_);
return v_res_5909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object* v_inst_5910_, lean_object* v_expectedType_5911_, lean_object* v___x_5912_, lean_object* v___x_5913_, lean_object* v_compile_5914_, lean_object* v_logCompileErrors_5915_, lean_object* v_isMeta_5916_, lean_object* v_val_5917_, lean_object* v_x_5918_, lean_object* v_x_5919_, lean_object* v_x_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_){
_start:
{
uint8_t v___x_161912__boxed_5926_; uint8_t v___x_161913__boxed_5927_; uint8_t v_compile_boxed_5928_; uint8_t v_logCompileErrors_boxed_5929_; uint8_t v_isMeta_boxed_5930_; lean_object* v_res_5931_; 
v___x_161912__boxed_5926_ = lean_unbox(v___x_5912_);
v___x_161913__boxed_5927_ = lean_unbox(v___x_5913_);
v_compile_boxed_5928_ = lean_unbox(v_compile_5914_);
v_logCompileErrors_boxed_5929_ = lean_unbox(v_logCompileErrors_5915_);
v_isMeta_boxed_5930_ = lean_unbox(v_isMeta_5916_);
v_res_5931_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__13(v_inst_5910_, v_expectedType_5911_, v___x_161912__boxed_5926_, v___x_161913__boxed_5927_, v_compile_boxed_5928_, v_logCompileErrors_boxed_5929_, v_isMeta_boxed_5930_, v_val_5917_, v_x_5918_, v_x_5919_, v_x_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_);
lean_dec(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec(v___y_5922_);
lean_dec_ref(v___y_5921_);
lean_dec(v_x_5920_);
return v_res_5931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object* v_inst_5932_, lean_object* v_expectedType_5933_, lean_object* v___x_5934_, lean_object* v_compile_5935_, lean_object* v_logCompileErrors_5936_, lean_object* v_isMeta_5937_, lean_object* v_val_5938_, lean_object* v_x_5939_, lean_object* v_x_5940_, lean_object* v_x_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_){
_start:
{
uint8_t v___x_162079__boxed_5947_; uint8_t v_compile_boxed_5948_; uint8_t v_logCompileErrors_boxed_5949_; uint8_t v_isMeta_boxed_5950_; lean_object* v_res_5951_; 
v___x_162079__boxed_5947_ = lean_unbox(v___x_5934_);
v_compile_boxed_5948_ = lean_unbox(v_compile_5935_);
v_logCompileErrors_boxed_5949_ = lean_unbox(v_logCompileErrors_5936_);
v_isMeta_boxed_5950_ = lean_unbox(v_isMeta_5937_);
v_res_5951_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__15(v_inst_5932_, v_expectedType_5933_, v___x_162079__boxed_5947_, v_compile_boxed_5948_, v_logCompileErrors_boxed_5949_, v_isMeta_boxed_5950_, v_val_5938_, v_x_5939_, v_x_5940_, v_x_5941_, v___y_5942_, v___y_5943_, v___y_5944_, v___y_5945_);
lean_dec(v___y_5945_);
lean_dec_ref(v___y_5944_);
lean_dec(v___y_5943_);
lean_dec_ref(v___y_5942_);
lean_dec(v_x_5941_);
return v_res_5951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__11___boxed(lean_object* v_inst_5952_, lean_object* v_expectedType_5953_, lean_object* v___x_5954_, lean_object* v_compile_5955_, lean_object* v_logCompileErrors_5956_, lean_object* v_isMeta_5957_, lean_object* v_val_5958_, lean_object* v_x_5959_, lean_object* v_x_5960_, lean_object* v_x_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_){
_start:
{
uint8_t v___x_162245__boxed_5967_; uint8_t v_compile_boxed_5968_; uint8_t v_logCompileErrors_boxed_5969_; uint8_t v_isMeta_boxed_5970_; lean_object* v_res_5971_; 
v___x_162245__boxed_5967_ = lean_unbox(v___x_5954_);
v_compile_boxed_5968_ = lean_unbox(v_compile_5955_);
v_logCompileErrors_boxed_5969_ = lean_unbox(v_logCompileErrors_5956_);
v_isMeta_boxed_5970_ = lean_unbox(v_isMeta_5957_);
v_res_5971_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__11(v_inst_5952_, v_expectedType_5953_, v___x_162245__boxed_5967_, v_compile_boxed_5968_, v_logCompileErrors_boxed_5969_, v_isMeta_boxed_5970_, v_val_5958_, v_x_5959_, v_x_5960_, v_x_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_);
lean_dec(v___y_5965_);
lean_dec_ref(v___y_5964_);
lean_dec(v___y_5963_);
lean_dec_ref(v___y_5962_);
return v_res_5971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9___boxed(lean_object* v_inst_5972_, lean_object* v_expectedType_5973_, lean_object* v___x_5974_, lean_object* v_compile_5975_, lean_object* v_logCompileErrors_5976_, lean_object* v_isMeta_5977_, lean_object* v_val_5978_, lean_object* v_x_5979_, lean_object* v_x_5980_, lean_object* v_x_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_){
_start:
{
uint8_t v___x_162412__boxed_5987_; uint8_t v_compile_boxed_5988_; uint8_t v_logCompileErrors_boxed_5989_; uint8_t v_isMeta_boxed_5990_; lean_object* v_res_5991_; 
v___x_162412__boxed_5987_ = lean_unbox(v___x_5974_);
v_compile_boxed_5988_ = lean_unbox(v_compile_5975_);
v_logCompileErrors_boxed_5989_ = lean_unbox(v_logCompileErrors_5976_);
v_isMeta_boxed_5990_ = lean_unbox(v_isMeta_5977_);
v_res_5991_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(v_inst_5972_, v_expectedType_5973_, v___x_162412__boxed_5987_, v_compile_boxed_5988_, v_logCompileErrors_boxed_5989_, v_isMeta_boxed_5990_, v_val_5978_, v_x_5979_, v_x_5980_, v_x_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
lean_dec(v___y_5983_);
lean_dec_ref(v___y_5982_);
lean_dec(v_x_5981_);
return v_res_5991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5992_ = _args[0];
lean_object* v_fst_5993_ = _args[1];
lean_object* v_args_5994_ = _args[2];
lean_object* v___x_5995_ = _args[3];
lean_object* v_compile_5996_ = _args[4];
lean_object* v_logCompileErrors_5997_ = _args[5];
lean_object* v___x_5998_ = _args[6];
lean_object* v_isMeta_5999_ = _args[7];
lean_object* v_val_6000_ = _args[8];
lean_object* v_expectedType_6001_ = _args[9];
lean_object* v_a_6002_ = _args[10];
lean_object* v_b_6003_ = _args[11];
lean_object* v___y_6004_ = _args[12];
lean_object* v___y_6005_ = _args[13];
lean_object* v___y_6006_ = _args[14];
lean_object* v___y_6007_ = _args[15];
lean_object* v___y_6008_ = _args[16];
_start:
{
uint8_t v___x_162606__boxed_6009_; uint8_t v_compile_boxed_6010_; uint8_t v_logCompileErrors_boxed_6011_; uint8_t v___x_162607__boxed_6012_; uint8_t v_isMeta_boxed_6013_; lean_object* v_res_6014_; 
v___x_162606__boxed_6009_ = lean_unbox(v___x_5995_);
v_compile_boxed_6010_ = lean_unbox(v_compile_5996_);
v_logCompileErrors_boxed_6011_ = lean_unbox(v_logCompileErrors_5997_);
v___x_162607__boxed_6012_ = lean_unbox(v___x_5998_);
v_isMeta_boxed_6013_ = lean_unbox(v_isMeta_5999_);
v_res_6014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg(v_upperBound_5992_, v_fst_5993_, v_args_5994_, v___x_162606__boxed_6009_, v_compile_boxed_6010_, v_logCompileErrors_boxed_6011_, v___x_162607__boxed_6012_, v_isMeta_boxed_6013_, v_val_6000_, v_expectedType_6001_, v_a_6002_, v_b_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec_ref(v___y_6004_);
lean_dec_ref(v_args_5994_);
lean_dec_ref(v_fst_5993_);
lean_dec(v_upperBound_5992_);
return v_res_6014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object* v_upperBound_6015_, lean_object* v_fst_6016_, lean_object* v_args_6017_, lean_object* v_compile_6018_, lean_object* v_logCompileErrors_6019_, lean_object* v___x_6020_, lean_object* v_isMeta_6021_, lean_object* v_val_6022_, lean_object* v_expectedType_6023_, lean_object* v_a_6024_, lean_object* v_b_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_){
_start:
{
uint8_t v_compile_boxed_6031_; uint8_t v_logCompileErrors_boxed_6032_; uint8_t v___x_162757__boxed_6033_; uint8_t v_isMeta_boxed_6034_; lean_object* v_res_6035_; 
v_compile_boxed_6031_ = lean_unbox(v_compile_6018_);
v_logCompileErrors_boxed_6032_ = lean_unbox(v_logCompileErrors_6019_);
v___x_162757__boxed_6033_ = lean_unbox(v___x_6020_);
v_isMeta_boxed_6034_ = lean_unbox(v_isMeta_6021_);
v_res_6035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_upperBound_6015_, v_fst_6016_, v_args_6017_, v_compile_boxed_6031_, v_logCompileErrors_boxed_6032_, v___x_162757__boxed_6033_, v_isMeta_boxed_6034_, v_val_6022_, v_expectedType_6023_, v_a_6024_, v_b_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
lean_dec(v___y_6029_);
lean_dec_ref(v___y_6028_);
lean_dec(v___y_6027_);
lean_dec_ref(v___y_6026_);
lean_dec_ref(v_args_6017_);
lean_dec_ref(v_fst_6016_);
lean_dec(v_upperBound_6015_);
return v_res_6035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_6036_ = _args[0];
lean_object* v_fst_6037_ = _args[1];
lean_object* v_args_6038_ = _args[2];
lean_object* v___x_6039_ = _args[3];
lean_object* v_compile_6040_ = _args[4];
lean_object* v_logCompileErrors_6041_ = _args[5];
lean_object* v___x_6042_ = _args[6];
lean_object* v_isMeta_6043_ = _args[7];
lean_object* v_val_6044_ = _args[8];
lean_object* v_expectedType_6045_ = _args[9];
lean_object* v_a_6046_ = _args[10];
lean_object* v_b_6047_ = _args[11];
lean_object* v___y_6048_ = _args[12];
lean_object* v___y_6049_ = _args[13];
lean_object* v___y_6050_ = _args[14];
lean_object* v___y_6051_ = _args[15];
lean_object* v___y_6052_ = _args[16];
_start:
{
uint8_t v___x_162916__boxed_6053_; uint8_t v_compile_boxed_6054_; uint8_t v_logCompileErrors_boxed_6055_; uint8_t v___x_162917__boxed_6056_; uint8_t v_isMeta_boxed_6057_; lean_object* v_res_6058_; 
v___x_162916__boxed_6053_ = lean_unbox(v___x_6039_);
v_compile_boxed_6054_ = lean_unbox(v_compile_6040_);
v_logCompileErrors_boxed_6055_ = lean_unbox(v_logCompileErrors_6041_);
v___x_162917__boxed_6056_ = lean_unbox(v___x_6042_);
v_isMeta_boxed_6057_ = lean_unbox(v_isMeta_6043_);
v_res_6058_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___redArg(v_upperBound_6036_, v_fst_6037_, v_args_6038_, v___x_162916__boxed_6053_, v_compile_boxed_6054_, v_logCompileErrors_boxed_6055_, v___x_162917__boxed_6056_, v_isMeta_boxed_6057_, v_val_6044_, v_expectedType_6045_, v_a_6046_, v_b_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_);
lean_dec(v___y_6051_);
lean_dec_ref(v___y_6050_);
lean_dec(v___y_6049_);
lean_dec_ref(v___y_6048_);
lean_dec_ref(v_args_6038_);
lean_dec_ref(v_fst_6037_);
lean_dec(v_upperBound_6036_);
return v_res_6058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg___boxed(lean_object* v_upperBound_6059_, lean_object* v_fst_6060_, lean_object* v_args_6061_, lean_object* v___x_6062_, lean_object* v_compile_6063_, lean_object* v_logCompileErrors_6064_, lean_object* v_isMeta_6065_, lean_object* v_val_6066_, lean_object* v_expectedType_6067_, lean_object* v_a_6068_, lean_object* v_b_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_){
_start:
{
uint8_t v___x_163077__boxed_6075_; uint8_t v_compile_boxed_6076_; uint8_t v_logCompileErrors_boxed_6077_; uint8_t v_isMeta_boxed_6078_; lean_object* v_res_6079_; 
v___x_163077__boxed_6075_ = lean_unbox(v___x_6062_);
v_compile_boxed_6076_ = lean_unbox(v_compile_6063_);
v_logCompileErrors_boxed_6077_ = lean_unbox(v_logCompileErrors_6064_);
v_isMeta_boxed_6078_ = lean_unbox(v_isMeta_6065_);
v_res_6079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg(v_upperBound_6059_, v_fst_6060_, v_args_6061_, v___x_163077__boxed_6075_, v_compile_boxed_6076_, v_logCompileErrors_boxed_6077_, v_isMeta_boxed_6078_, v_val_6066_, v_expectedType_6067_, v_a_6068_, v_b_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_);
lean_dec(v___y_6073_);
lean_dec_ref(v___y_6072_);
lean_dec(v___y_6071_);
lean_dec_ref(v___y_6070_);
lean_dec_ref(v_args_6061_);
lean_dec_ref(v_fst_6060_);
lean_dec(v_upperBound_6059_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object* v_inst_6080_, lean_object* v_expectedType_6081_, lean_object* v_compile_6082_, lean_object* v_logCompileErrors_6083_, lean_object* v_isMeta_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_){
_start:
{
uint8_t v_compile_boxed_6090_; uint8_t v_logCompileErrors_boxed_6091_; uint8_t v_isMeta_boxed_6092_; lean_object* v_res_6093_; 
v_compile_boxed_6090_ = lean_unbox(v_compile_6082_);
v_logCompileErrors_boxed_6091_ = lean_unbox(v_logCompileErrors_6083_);
v_isMeta_boxed_6092_ = lean_unbox(v_isMeta_6084_);
v_res_6093_ = l_Lean_Meta_wrapInstance(v_inst_6080_, v_expectedType_6081_, v_compile_boxed_6090_, v_logCompileErrors_boxed_6091_, v_isMeta_boxed_6092_, v_a_6085_, v_a_6086_, v_a_6087_, v_a_6088_);
lean_dec(v_a_6088_);
lean_dec_ref(v_a_6087_);
lean_dec(v_a_6086_);
lean_dec_ref(v_a_6085_);
return v_res_6093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6(lean_object* v_mvarId_6094_, lean_object* v_val_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_){
_start:
{
lean_object* v___x_6101_; 
v___x_6101_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_mvarId_6094_, v_val_6095_, v___y_6097_);
return v___x_6101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object* v_mvarId_6102_, lean_object* v_val_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
lean_object* v_res_6109_; 
v_res_6109_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6(v_mvarId_6102_, v_val_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7(lean_object* v_upperBound_6110_, lean_object* v_fst_6111_, lean_object* v_args_6112_, uint8_t v_compile_6113_, uint8_t v_logCompileErrors_6114_, uint8_t v___x_6115_, uint8_t v_isMeta_6116_, lean_object* v_val_6117_, lean_object* v_expectedType_6118_, lean_object* v_inst_6119_, lean_object* v_R_6120_, lean_object* v_a_6121_, lean_object* v_b_6122_, lean_object* v_c_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_){
_start:
{
lean_object* v___x_6129_; 
v___x_6129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_upperBound_6110_, v_fst_6111_, v_args_6112_, v_compile_6113_, v_logCompileErrors_6114_, v___x_6115_, v_isMeta_6116_, v_val_6117_, v_expectedType_6118_, v_a_6121_, v_b_6122_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_);
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object** _args){
lean_object* v_upperBound_6130_ = _args[0];
lean_object* v_fst_6131_ = _args[1];
lean_object* v_args_6132_ = _args[2];
lean_object* v_compile_6133_ = _args[3];
lean_object* v_logCompileErrors_6134_ = _args[4];
lean_object* v___x_6135_ = _args[5];
lean_object* v_isMeta_6136_ = _args[6];
lean_object* v_val_6137_ = _args[7];
lean_object* v_expectedType_6138_ = _args[8];
lean_object* v_inst_6139_ = _args[9];
lean_object* v_R_6140_ = _args[10];
lean_object* v_a_6141_ = _args[11];
lean_object* v_b_6142_ = _args[12];
lean_object* v_c_6143_ = _args[13];
lean_object* v___y_6144_ = _args[14];
lean_object* v___y_6145_ = _args[15];
lean_object* v___y_6146_ = _args[16];
lean_object* v___y_6147_ = _args[17];
lean_object* v___y_6148_ = _args[18];
_start:
{
uint8_t v_compile_boxed_6149_; uint8_t v_logCompileErrors_boxed_6150_; uint8_t v___x_167565__boxed_6151_; uint8_t v_isMeta_boxed_6152_; lean_object* v_res_6153_; 
v_compile_boxed_6149_ = lean_unbox(v_compile_6133_);
v_logCompileErrors_boxed_6150_ = lean_unbox(v_logCompileErrors_6134_);
v___x_167565__boxed_6151_ = lean_unbox(v___x_6135_);
v_isMeta_boxed_6152_ = lean_unbox(v_isMeta_6136_);
v_res_6153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__7(v_upperBound_6130_, v_fst_6131_, v_args_6132_, v_compile_boxed_6149_, v_logCompileErrors_boxed_6150_, v___x_167565__boxed_6151_, v_isMeta_boxed_6152_, v_val_6137_, v_expectedType_6138_, v_inst_6139_, v_R_6140_, v_a_6141_, v_b_6142_, v_c_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
lean_dec_ref(v_args_6132_);
lean_dec_ref(v_fst_6131_);
lean_dec(v_upperBound_6130_);
return v_res_6153_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16(lean_object* v_00_u03b1_6154_, lean_object* v_x_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_){
_start:
{
lean_object* v___x_6161_; 
v___x_6161_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___redArg(v_x_6155_);
return v___x_6161_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16___boxed(lean_object* v_00_u03b1_6162_, lean_object* v_x_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_){
_start:
{
lean_object* v_res_6169_; 
v_res_6169_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__11_spec__16(v_00_u03b1_6162_, v_x_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
lean_dec(v___y_6165_);
lean_dec_ref(v___y_6164_);
return v_res_6169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12(lean_object* v_upperBound_6170_, lean_object* v_fst_6171_, lean_object* v_args_6172_, uint8_t v___x_6173_, uint8_t v_compile_6174_, uint8_t v_logCompileErrors_6175_, uint8_t v___x_6176_, uint8_t v_isMeta_6177_, lean_object* v_val_6178_, lean_object* v_expectedType_6179_, lean_object* v_inst_6180_, lean_object* v_R_6181_, lean_object* v_a_6182_, lean_object* v_b_6183_, lean_object* v_c_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_){
_start:
{
lean_object* v___x_6190_; 
v___x_6190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___redArg(v_upperBound_6170_, v_fst_6171_, v_args_6172_, v___x_6173_, v_compile_6174_, v_logCompileErrors_6175_, v___x_6176_, v_isMeta_6177_, v_val_6178_, v_expectedType_6179_, v_a_6182_, v_b_6183_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_);
return v___x_6190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_6191_ = _args[0];
lean_object* v_fst_6192_ = _args[1];
lean_object* v_args_6193_ = _args[2];
lean_object* v___x_6194_ = _args[3];
lean_object* v_compile_6195_ = _args[4];
lean_object* v_logCompileErrors_6196_ = _args[5];
lean_object* v___x_6197_ = _args[6];
lean_object* v_isMeta_6198_ = _args[7];
lean_object* v_val_6199_ = _args[8];
lean_object* v_expectedType_6200_ = _args[9];
lean_object* v_inst_6201_ = _args[10];
lean_object* v_R_6202_ = _args[11];
lean_object* v_a_6203_ = _args[12];
lean_object* v_b_6204_ = _args[13];
lean_object* v_c_6205_ = _args[14];
lean_object* v___y_6206_ = _args[15];
lean_object* v___y_6207_ = _args[16];
lean_object* v___y_6208_ = _args[17];
lean_object* v___y_6209_ = _args[18];
lean_object* v___y_6210_ = _args[19];
_start:
{
uint8_t v___x_167617__boxed_6211_; uint8_t v_compile_boxed_6212_; uint8_t v_logCompileErrors_boxed_6213_; uint8_t v___x_167618__boxed_6214_; uint8_t v_isMeta_boxed_6215_; lean_object* v_res_6216_; 
v___x_167617__boxed_6211_ = lean_unbox(v___x_6194_);
v_compile_boxed_6212_ = lean_unbox(v_compile_6195_);
v_logCompileErrors_boxed_6213_ = lean_unbox(v_logCompileErrors_6196_);
v___x_167618__boxed_6214_ = lean_unbox(v___x_6197_);
v_isMeta_boxed_6215_ = lean_unbox(v_isMeta_6198_);
v_res_6216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12(v_upperBound_6191_, v_fst_6192_, v_args_6193_, v___x_167617__boxed_6211_, v_compile_boxed_6212_, v_logCompileErrors_boxed_6213_, v___x_167618__boxed_6214_, v_isMeta_boxed_6215_, v_val_6199_, v_expectedType_6200_, v_inst_6201_, v_R_6202_, v_a_6203_, v_b_6204_, v_c_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
lean_dec(v___y_6209_);
lean_dec_ref(v___y_6208_);
lean_dec(v___y_6207_);
lean_dec_ref(v___y_6206_);
lean_dec_ref(v_args_6193_);
lean_dec_ref(v_fst_6192_);
lean_dec(v_upperBound_6191_);
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14(lean_object* v_upperBound_6217_, lean_object* v_fst_6218_, lean_object* v_args_6219_, uint8_t v___x_6220_, uint8_t v_compile_6221_, uint8_t v_logCompileErrors_6222_, uint8_t v_isMeta_6223_, lean_object* v_val_6224_, lean_object* v_expectedType_6225_, lean_object* v_inst_6226_, lean_object* v_R_6227_, lean_object* v_a_6228_, lean_object* v_b_6229_, lean_object* v_c_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
lean_object* v___x_6236_; 
v___x_6236_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___redArg(v_upperBound_6217_, v_fst_6218_, v_args_6219_, v___x_6220_, v_compile_6221_, v_logCompileErrors_6222_, v_isMeta_6223_, v_val_6224_, v_expectedType_6225_, v_a_6228_, v_b_6229_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
return v___x_6236_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object** _args){
lean_object* v_upperBound_6237_ = _args[0];
lean_object* v_fst_6238_ = _args[1];
lean_object* v_args_6239_ = _args[2];
lean_object* v___x_6240_ = _args[3];
lean_object* v_compile_6241_ = _args[4];
lean_object* v_logCompileErrors_6242_ = _args[5];
lean_object* v_isMeta_6243_ = _args[6];
lean_object* v_val_6244_ = _args[7];
lean_object* v_expectedType_6245_ = _args[8];
lean_object* v_inst_6246_ = _args[9];
lean_object* v_R_6247_ = _args[10];
lean_object* v_a_6248_ = _args[11];
lean_object* v_b_6249_ = _args[12];
lean_object* v_c_6250_ = _args[13];
lean_object* v___y_6251_ = _args[14];
lean_object* v___y_6252_ = _args[15];
lean_object* v___y_6253_ = _args[16];
lean_object* v___y_6254_ = _args[17];
lean_object* v___y_6255_ = _args[18];
_start:
{
uint8_t v___x_167652__boxed_6256_; uint8_t v_compile_boxed_6257_; uint8_t v_logCompileErrors_boxed_6258_; uint8_t v_isMeta_boxed_6259_; lean_object* v_res_6260_; 
v___x_167652__boxed_6256_ = lean_unbox(v___x_6240_);
v_compile_boxed_6257_ = lean_unbox(v_compile_6241_);
v_logCompileErrors_boxed_6258_ = lean_unbox(v_logCompileErrors_6242_);
v_isMeta_boxed_6259_ = lean_unbox(v_isMeta_6243_);
v_res_6260_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__14(v_upperBound_6237_, v_fst_6238_, v_args_6239_, v___x_167652__boxed_6256_, v_compile_boxed_6257_, v_logCompileErrors_boxed_6258_, v_isMeta_boxed_6259_, v_val_6244_, v_expectedType_6245_, v_inst_6246_, v_R_6247_, v_a_6248_, v_b_6249_, v_c_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_);
lean_dec(v___y_6254_);
lean_dec_ref(v___y_6253_);
lean_dec(v___y_6252_);
lean_dec_ref(v___y_6251_);
lean_dec_ref(v_args_6239_);
lean_dec_ref(v_fst_6238_);
lean_dec(v_upperBound_6237_);
return v_res_6260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3(lean_object* v_00_u03b1_6261_, lean_object* v_constName_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_){
_start:
{
lean_object* v___x_6268_; 
v___x_6268_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___redArg(v_constName_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
return v___x_6268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3___boxed(lean_object* v_00_u03b1_6269_, lean_object* v_constName_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
lean_object* v_res_6276_; 
v_res_6276_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_00_u03b1_6269_, v_constName_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
lean_dec(v___y_6274_);
lean_dec_ref(v___y_6273_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7(lean_object* v_00_u03b2_6277_, lean_object* v_x_6278_, lean_object* v_x_6279_, lean_object* v_x_6280_){
_start:
{
lean_object* v___x_6281_; 
v___x_6281_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7___redArg(v_x_6278_, v_x_6279_, v_x_6280_);
return v___x_6281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19(lean_object* v_upperBound_6282_, lean_object* v_fst_6283_, lean_object* v_args_6284_, uint8_t v___x_6285_, uint8_t v_compile_6286_, uint8_t v_logCompileErrors_6287_, uint8_t v___x_6288_, uint8_t v_isMeta_6289_, lean_object* v_val_6290_, lean_object* v_expectedType_6291_, lean_object* v_inst_6292_, lean_object* v_R_6293_, lean_object* v_a_6294_, lean_object* v_b_6295_, lean_object* v_c_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_){
_start:
{
lean_object* v___x_6302_; 
v___x_6302_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___redArg(v_upperBound_6282_, v_fst_6283_, v_args_6284_, v___x_6285_, v_compile_6286_, v_logCompileErrors_6287_, v___x_6288_, v_isMeta_6289_, v_val_6290_, v_expectedType_6291_, v_a_6294_, v_b_6295_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19___boxed(lean_object** _args){
lean_object* v_upperBound_6303_ = _args[0];
lean_object* v_fst_6304_ = _args[1];
lean_object* v_args_6305_ = _args[2];
lean_object* v___x_6306_ = _args[3];
lean_object* v_compile_6307_ = _args[4];
lean_object* v_logCompileErrors_6308_ = _args[5];
lean_object* v___x_6309_ = _args[6];
lean_object* v_isMeta_6310_ = _args[7];
lean_object* v_val_6311_ = _args[8];
lean_object* v_expectedType_6312_ = _args[9];
lean_object* v_inst_6313_ = _args[10];
lean_object* v_R_6314_ = _args[11];
lean_object* v_a_6315_ = _args[12];
lean_object* v_b_6316_ = _args[13];
lean_object* v_c_6317_ = _args[14];
lean_object* v___y_6318_ = _args[15];
lean_object* v___y_6319_ = _args[16];
lean_object* v___y_6320_ = _args[17];
lean_object* v___y_6321_ = _args[18];
lean_object* v___y_6322_ = _args[19];
_start:
{
uint8_t v___x_167709__boxed_6323_; uint8_t v_compile_boxed_6324_; uint8_t v_logCompileErrors_boxed_6325_; uint8_t v___x_167710__boxed_6326_; uint8_t v_isMeta_boxed_6327_; lean_object* v_res_6328_; 
v___x_167709__boxed_6323_ = lean_unbox(v___x_6306_);
v_compile_boxed_6324_ = lean_unbox(v_compile_6307_);
v_logCompileErrors_boxed_6325_ = lean_unbox(v_logCompileErrors_6308_);
v___x_167710__boxed_6326_ = lean_unbox(v___x_6309_);
v_isMeta_boxed_6327_ = lean_unbox(v_isMeta_6310_);
v_res_6328_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__12_spec__19(v_upperBound_6303_, v_fst_6304_, v_args_6305_, v___x_167709__boxed_6323_, v_compile_boxed_6324_, v_logCompileErrors_boxed_6325_, v___x_167710__boxed_6326_, v_isMeta_boxed_6327_, v_val_6311_, v_expectedType_6312_, v_inst_6313_, v_R_6314_, v_a_6315_, v_b_6316_, v_c_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_);
lean_dec(v___y_6321_);
lean_dec_ref(v___y_6320_);
lean_dec(v___y_6319_);
lean_dec_ref(v___y_6318_);
lean_dec_ref(v_args_6305_);
lean_dec_ref(v_fst_6304_);
lean_dec(v_upperBound_6303_);
return v_res_6328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6(lean_object* v_00_u03b1_6329_, lean_object* v_ref_6330_, lean_object* v_constName_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_){
_start:
{
lean_object* v___x_6337_; 
v___x_6337_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___redArg(v_ref_6330_, v_constName_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_);
return v___x_6337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6___boxed(lean_object* v_00_u03b1_6338_, lean_object* v_ref_6339_, lean_object* v_constName_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_){
_start:
{
lean_object* v_res_6346_; 
v_res_6346_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6(v_00_u03b1_6338_, v_ref_6339_, v_constName_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_);
lean_dec(v___y_6344_);
lean_dec_ref(v___y_6343_);
lean_dec(v___y_6342_);
lean_dec_ref(v___y_6341_);
lean_dec(v_ref_6339_);
return v_res_6346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10(lean_object* v_00_u03b2_6347_, lean_object* v_x_6348_, size_t v_x_6349_, size_t v_x_6350_, lean_object* v_x_6351_, lean_object* v_x_6352_){
_start:
{
lean_object* v___x_6353_; 
v___x_6353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___redArg(v_x_6348_, v_x_6349_, v_x_6350_, v_x_6351_, v_x_6352_);
return v___x_6353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10___boxed(lean_object* v_00_u03b2_6354_, lean_object* v_x_6355_, lean_object* v_x_6356_, lean_object* v_x_6357_, lean_object* v_x_6358_, lean_object* v_x_6359_){
_start:
{
size_t v_x_167760__boxed_6360_; size_t v_x_167761__boxed_6361_; lean_object* v_res_6362_; 
v_x_167760__boxed_6360_ = lean_unbox_usize(v_x_6356_);
lean_dec(v_x_6356_);
v_x_167761__boxed_6361_ = lean_unbox_usize(v_x_6357_);
lean_dec(v_x_6357_);
v_res_6362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10(v_00_u03b2_6354_, v_x_6355_, v_x_167760__boxed_6360_, v_x_167761__boxed_6361_, v_x_6358_, v_x_6359_);
return v_res_6362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20(lean_object* v_00_u03b1_6363_, lean_object* v_ref_6364_, lean_object* v_msg_6365_, lean_object* v_declHint_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_){
_start:
{
lean_object* v___x_6372_; 
v___x_6372_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___redArg(v_ref_6364_, v_msg_6365_, v_declHint_6366_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_);
return v___x_6372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20___boxed(lean_object* v_00_u03b1_6373_, lean_object* v_ref_6374_, lean_object* v_msg_6375_, lean_object* v_declHint_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_){
_start:
{
lean_object* v_res_6382_; 
v_res_6382_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20(v_00_u03b1_6373_, v_ref_6374_, v_msg_6375_, v_declHint_6376_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_);
lean_dec(v___y_6380_);
lean_dec_ref(v___y_6379_);
lean_dec(v___y_6378_);
lean_dec_ref(v___y_6377_);
lean_dec(v_ref_6374_);
return v_res_6382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23(lean_object* v_00_u03b2_6383_, lean_object* v_n_6384_, lean_object* v_k_6385_, lean_object* v_v_6386_){
_start:
{
lean_object* v___x_6387_; 
v___x_6387_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23___redArg(v_n_6384_, v_k_6385_, v_v_6386_);
return v___x_6387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24(lean_object* v_00_u03b2_6388_, size_t v_depth_6389_, lean_object* v_keys_6390_, lean_object* v_vals_6391_, lean_object* v_heq_6392_, lean_object* v_i_6393_, lean_object* v_entries_6394_){
_start:
{
lean_object* v___x_6395_; 
v___x_6395_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___redArg(v_depth_6389_, v_keys_6390_, v_vals_6391_, v_i_6393_, v_entries_6394_);
return v___x_6395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24___boxed(lean_object* v_00_u03b2_6396_, lean_object* v_depth_6397_, lean_object* v_keys_6398_, lean_object* v_vals_6399_, lean_object* v_heq_6400_, lean_object* v_i_6401_, lean_object* v_entries_6402_){
_start:
{
size_t v_depth_boxed_6403_; lean_object* v_res_6404_; 
v_depth_boxed_6403_ = lean_unbox_usize(v_depth_6397_);
lean_dec(v_depth_6397_);
v_res_6404_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__24(v_00_u03b2_6396_, v_depth_boxed_6403_, v_keys_6398_, v_vals_6399_, v_heq_6400_, v_i_6401_, v_entries_6402_);
lean_dec_ref(v_vals_6399_);
lean_dec_ref(v_keys_6398_);
return v_res_6404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30(lean_object* v_msg_6405_, lean_object* v_declHint_6406_, lean_object* v___y_6407_, lean_object* v___y_6408_, lean_object* v___y_6409_, lean_object* v___y_6410_){
_start:
{
lean_object* v___x_6412_; 
v___x_6412_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___redArg(v_msg_6405_, v_declHint_6406_, v___y_6410_);
return v___x_6412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30___boxed(lean_object* v_msg_6413_, lean_object* v_declHint_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_){
_start:
{
lean_object* v_res_6420_; 
v_res_6420_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__27_spec__30(v_msg_6413_, v_declHint_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_);
lean_dec(v___y_6418_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
return v_res_6420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28(lean_object* v_00_u03b1_6421_, lean_object* v_ref_6422_, lean_object* v_msg_6423_, lean_object* v___y_6424_, lean_object* v___y_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_){
_start:
{
lean_object* v___x_6429_; 
v___x_6429_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___redArg(v_ref_6422_, v_msg_6423_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_);
return v___x_6429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28___boxed(lean_object* v_00_u03b1_6430_, lean_object* v_ref_6431_, lean_object* v_msg_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_){
_start:
{
lean_object* v_res_6438_; 
v_res_6438_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__3_spec__3_spec__6_spec__20_spec__28(v_00_u03b1_6430_, v_ref_6431_, v_msg_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_);
lean_dec(v___y_6436_);
lean_dec_ref(v___y_6435_);
lean_dec(v___y_6434_);
lean_dec_ref(v___y_6433_);
lean_dec(v_ref_6431_);
return v_res_6438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23_spec__31(lean_object* v_00_u03b2_6439_, lean_object* v_x_6440_, lean_object* v_x_6441_, lean_object* v_x_6442_, lean_object* v_x_6443_){
_start:
{
lean_object* v___x_6444_; 
v___x_6444_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__6_spec__7_spec__10_spec__23_spec__31___redArg(v_x_6440_, v_x_6441_, v_x_6442_, v_x_6443_);
return v___x_6444_;
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
