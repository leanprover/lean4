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
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_abstractInstImplicitArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractInstImplicitArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "could not reduce type `"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6;
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_wrapInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "error when attempting to reuse existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "using projection of existing instance `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "did not find existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_wrapInstance___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "did not reduce to constructor application, returning/wrapping as is: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found inherited field `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` from parent `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "using existing instance "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof field "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " does not have expected type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " but "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = ", wrapping in auxiliary theorem: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "wrapInstance: incorrect number of arguments for constructor application `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "wrapInstance: `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not unify with the conclusion of `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_wrapInstance___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "class is "};
static const lean_object* l_Lean_Meta_wrapInstance___closed__2 = (const lean_object*)&l_Lean_Meta_wrapInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(lean_object* v_e_205_, lean_object* v___y_206_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Lean_Expr_hasMVar(v_e_205_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_e_205_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v_mctx_211_; lean_object* v___x_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v___x_215_; lean_object* v_cache_216_; lean_object* v_zetaDeltaFVarIds_217_; lean_object* v_postponed_218_; lean_object* v_diag_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_228_; 
v___x_210_ = lean_st_ref_get(v___y_206_);
v_mctx_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_mctx_211_);
lean_dec(v___x_210_);
v___x_212_ = l_Lean_instantiateMVarsCore(v_mctx_211_, v_e_205_);
v_fst_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_fst_213_);
v_snd_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_snd_214_);
lean_dec_ref(v___x_212_);
v___x_215_ = lean_st_ref_take(v___y_206_);
v_cache_216_ = lean_ctor_get(v___x_215_, 1);
v_zetaDeltaFVarIds_217_ = lean_ctor_get(v___x_215_, 2);
v_postponed_218_ = lean_ctor_get(v___x_215_, 3);
v_diag_219_ = lean_ctor_get(v___x_215_, 4);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v___x_215_, 0);
lean_dec(v_unused_229_);
v___x_221_ = v___x_215_;
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_diag_219_);
lean_inc(v_postponed_218_);
lean_inc(v_zetaDeltaFVarIds_217_);
lean_inc(v_cache_216_);
lean_dec(v___x_215_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_snd_214_);
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_snd_214_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_cache_216_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_zetaDeltaFVarIds_217_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_postponed_218_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_diag_219_);
v___x_224_ = v_reuseFailAlloc_227_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_st_ref_set(v___y_206_, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_fst_213_);
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg___boxed(lean_object* v_e_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_e_230_, v___y_231_);
lean_dec(v___y_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(lean_object* v_e_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_e_234_, v___y_236_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___boxed(lean_object* v_e_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(v_e_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_ks_252_; lean_object* v_vs_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_277_; 
v_ks_252_ = lean_ctor_get(v_x_248_, 0);
v_vs_253_ = lean_ctor_get(v_x_248_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_277_ == 0)
{
v___x_255_ = v_x_248_;
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_vs_253_);
lean_inc(v_ks_252_);
lean_dec(v_x_248_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_ks_252_);
v___x_258_ = lean_nat_dec_lt(v_x_249_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_x_249_);
v___x_259_ = lean_array_push(v_ks_252_, v_x_250_);
v___x_260_ = lean_array_push(v_vs_253_, v_x_251_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_260_);
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v_k_x27_264_; uint8_t v___x_265_; 
v_k_x27_264_ = lean_array_fget_borrowed(v_ks_252_, v_x_249_);
v___x_265_ = l_Lean_instBEqMVarId_beq(v_x_250_, v_k_x27_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; 
if (v_isShared_256_ == 0)
{
v___x_267_ = v___x_255_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_ks_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_vs_253_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_x_249_, v___x_268_);
lean_dec(v_x_249_);
v_x_248_ = v___x_267_;
v_x_249_ = v___x_269_;
goto _start;
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_array_fset(v_ks_252_, v_x_249_, v_x_250_);
v___x_273_ = lean_array_fset(v_vs_253_, v_x_249_, v_x_251_);
lean_dec(v_x_249_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_273_);
lean_ctor_set(v___x_255_, 0, v___x_272_);
v___x_275_ = v___x_255_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_278_, lean_object* v_k_279_, lean_object* v_v_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_278_, v___x_281_, v_k_279_, v_v_280_);
return v___x_282_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; 
v___x_283_ = ((size_t)5ULL);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_shift_left(v___x_284_, v___x_283_);
return v___x_285_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; 
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_288_ = lean_usize_sub(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(lean_object* v_x_290_, size_t v_x_291_, size_t v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_es_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v_j_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_es_295_ = lean_ctor_get(v_x_290_, 0);
v___x_296_ = ((size_t)5ULL);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_299_ = lean_usize_land(v_x_291_, v___x_298_);
v_j_300_ = lean_usize_to_nat(v___x_299_);
v___x_301_ = lean_array_get_size(v_es_295_);
v___x_302_ = lean_nat_dec_lt(v_j_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v_j_300_);
lean_dec(v_x_294_);
lean_dec(v_x_293_);
return v_x_290_;
}
else
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_339_; 
lean_inc_ref(v_es_295_);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v_x_290_, 0);
lean_dec(v_unused_340_);
v___x_304_ = v_x_290_;
v_isShared_305_ = v_isSharedCheck_339_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_x_290_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_339_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_v_306_; lean_object* v___x_307_; lean_object* v_xs_x27_308_; lean_object* v___y_310_; 
v_v_306_ = lean_array_fget(v_es_295_, v_j_300_);
v___x_307_ = lean_box(0);
v_xs_x27_308_ = lean_array_fset(v_es_295_, v_j_300_, v___x_307_);
switch(lean_obj_tag(v_v_306_))
{
case 0:
{
lean_object* v_key_315_; lean_object* v_val_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_326_; 
v_key_315_ = lean_ctor_get(v_v_306_, 0);
v_val_316_ = lean_ctor_get(v_v_306_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_v_306_);
if (v_isSharedCheck_326_ == 0)
{
v___x_318_ = v_v_306_;
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_val_316_);
lean_inc(v_key_315_);
lean_dec(v_v_306_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = l_Lean_instBEqMVarId_beq(v_x_293_, v_key_315_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_318_);
v___x_321_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_315_, v_val_316_, v_x_293_, v_x_294_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___y_310_ = v___x_322_;
goto v___jp_309_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v_val_316_);
lean_dec(v_key_315_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v_x_294_);
lean_ctor_set(v___x_318_, 0, v_x_293_);
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_x_293_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_x_294_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v___y_310_ = v___x_324_;
goto v___jp_309_;
}
}
}
}
case 1:
{
lean_object* v_node_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_337_; 
v_node_327_ = lean_ctor_get(v_v_306_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_v_306_);
if (v_isSharedCheck_337_ == 0)
{
v___x_329_ = v_v_306_;
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_node_327_);
lean_dec(v_v_306_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_331_ = lean_usize_shift_right(v_x_291_, v___x_296_);
v___x_332_ = lean_usize_add(v_x_292_, v___x_297_);
v___x_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_node_327_, v___x_331_, v___x_332_, v_x_293_, v_x_294_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_333_);
v___x_335_ = v___x_329_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v___y_310_ = v___x_335_;
goto v___jp_309_;
}
}
}
default: 
{
lean_object* v___x_338_; 
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_x_293_);
lean_ctor_set(v___x_338_, 1, v_x_294_);
v___y_310_ = v___x_338_;
goto v___jp_309_;
}
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_array_fset(v_xs_x27_308_, v_j_300_, v___y_310_);
lean_dec(v_j_300_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_311_);
v___x_313_ = v___x_304_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_ks_341_; lean_object* v_vs_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_362_; 
v_ks_341_ = lean_ctor_get(v_x_290_, 0);
v_vs_342_ = lean_ctor_get(v_x_290_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_362_ == 0)
{
v___x_344_ = v_x_290_;
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_vs_342_);
lean_inc(v_ks_341_);
lean_dec(v_x_290_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_ks_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_vs_342_);
v___x_347_ = v_reuseFailAlloc_361_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v_newNode_348_; uint8_t v___y_350_; size_t v___x_356_; uint8_t v___x_357_; 
v_newNode_348_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(v___x_347_, v_x_293_, v_x_294_);
v___x_356_ = ((size_t)7ULL);
v___x_357_ = lean_usize_dec_le(v___x_356_, v_x_292_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_348_);
v___x_359_ = lean_unsigned_to_nat(4u);
v___x_360_ = lean_nat_dec_lt(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___y_350_ = v___x_360_;
goto v___jp_349_;
}
else
{
v___y_350_ = v___x_357_;
goto v___jp_349_;
}
v___jp_349_:
{
if (v___y_350_ == 0)
{
lean_object* v_ks_351_; lean_object* v_vs_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_ks_351_ = lean_ctor_get(v_newNode_348_, 0);
lean_inc_ref(v_ks_351_);
v_vs_352_ = lean_ctor_get(v_newNode_348_, 1);
lean_inc_ref(v_vs_352_);
lean_dec_ref(v_newNode_348_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_x_292_, v_ks_351_, v_vs_352_, v___x_353_, v___x_354_);
lean_dec_ref(v_vs_352_);
lean_dec_ref(v_ks_351_);
return v___x_355_;
}
else
{
return v_newNode_348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_363_, lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_i_366_, lean_object* v_entries_367_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_keys_364_);
v___x_369_ = lean_nat_dec_lt(v_i_366_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v_i_366_);
return v_entries_367_;
}
else
{
lean_object* v_k_370_; lean_object* v_v_371_; uint64_t v___x_372_; size_t v_h_373_; size_t v___x_374_; lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v_h_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_k_370_ = lean_array_fget_borrowed(v_keys_364_, v_i_366_);
v_v_371_ = lean_array_fget_borrowed(v_vals_365_, v_i_366_);
v___x_372_ = l_Lean_instHashableMVarId_hash(v_k_370_);
v_h_373_ = lean_uint64_to_usize(v___x_372_);
v___x_374_ = ((size_t)5ULL);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_sub(v_depth_363_, v___x_376_);
v___x_378_ = lean_usize_mul(v___x_374_, v___x_377_);
v_h_379_ = lean_usize_shift_right(v_h_373_, v___x_378_);
v___x_380_ = lean_nat_add(v_i_366_, v___x_375_);
lean_dec(v_i_366_);
lean_inc(v_v_371_);
lean_inc(v_k_370_);
v___x_381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_entries_367_, v_h_379_, v_depth_363_, v_k_370_, v_v_371_);
v_i_366_ = v___x_380_;
v_entries_367_ = v___x_381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_383_, lean_object* v_keys_384_, lean_object* v_vals_385_, lean_object* v_i_386_, lean_object* v_entries_387_){
_start:
{
size_t v_depth_boxed_388_; lean_object* v_res_389_; 
v_depth_boxed_388_ = lean_unbox_usize(v_depth_383_);
lean_dec(v_depth_383_);
v_res_389_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_388_, v_keys_384_, v_vals_385_, v_i_386_, v_entries_387_);
lean_dec_ref(v_vals_385_);
lean_dec_ref(v_keys_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
size_t v_x_2193__boxed_395_; size_t v_x_2194__boxed_396_; lean_object* v_res_397_; 
v_x_2193__boxed_395_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_x_2194__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_res_397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_390_, v_x_2193__boxed_395_, v_x_2194__boxed_396_, v_x_393_, v_x_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint64_t v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v___x_404_; 
v___x_401_ = l_Lean_instHashableMVarId_hash(v_x_399_);
v___x_402_ = lean_uint64_to_usize(v___x_401_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_398_, v___x_402_, v___x_403_, v_x_399_, v_x_400_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(lean_object* v_mvarId_405_, lean_object* v_val_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_mctx_410_; lean_object* v_cache_411_; lean_object* v_zetaDeltaFVarIds_412_; lean_object* v_postponed_413_; lean_object* v_diag_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_442_; 
v___x_409_ = lean_st_ref_take(v___y_407_);
v_mctx_410_ = lean_ctor_get(v___x_409_, 0);
v_cache_411_ = lean_ctor_get(v___x_409_, 1);
v_zetaDeltaFVarIds_412_ = lean_ctor_get(v___x_409_, 2);
v_postponed_413_ = lean_ctor_get(v___x_409_, 3);
v_diag_414_ = lean_ctor_get(v___x_409_, 4);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_442_ == 0)
{
v___x_416_ = v___x_409_;
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_diag_414_);
lean_inc(v_postponed_413_);
lean_inc(v_zetaDeltaFVarIds_412_);
lean_inc(v_cache_411_);
lean_inc(v_mctx_410_);
lean_dec(v___x_409_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_depth_418_; lean_object* v_levelAssignDepth_419_; lean_object* v_lmvarCounter_420_; lean_object* v_mvarCounter_421_; lean_object* v_lDecls_422_; lean_object* v_decls_423_; lean_object* v_userNames_424_; lean_object* v_lAssignment_425_; lean_object* v_eAssignment_426_; lean_object* v_dAssignment_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_441_; 
v_depth_418_ = lean_ctor_get(v_mctx_410_, 0);
v_levelAssignDepth_419_ = lean_ctor_get(v_mctx_410_, 1);
v_lmvarCounter_420_ = lean_ctor_get(v_mctx_410_, 2);
v_mvarCounter_421_ = lean_ctor_get(v_mctx_410_, 3);
v_lDecls_422_ = lean_ctor_get(v_mctx_410_, 4);
v_decls_423_ = lean_ctor_get(v_mctx_410_, 5);
v_userNames_424_ = lean_ctor_get(v_mctx_410_, 6);
v_lAssignment_425_ = lean_ctor_get(v_mctx_410_, 7);
v_eAssignment_426_ = lean_ctor_get(v_mctx_410_, 8);
v_dAssignment_427_ = lean_ctor_get(v_mctx_410_, 9);
v_isSharedCheck_441_ = !lean_is_exclusive(v_mctx_410_);
if (v_isSharedCheck_441_ == 0)
{
v___x_429_ = v_mctx_410_;
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_dAssignment_427_);
lean_inc(v_eAssignment_426_);
lean_inc(v_lAssignment_425_);
lean_inc(v_userNames_424_);
lean_inc(v_decls_423_);
lean_inc(v_lDecls_422_);
lean_inc(v_mvarCounter_421_);
lean_inc(v_lmvarCounter_420_);
lean_inc(v_levelAssignDepth_419_);
lean_inc(v_depth_418_);
lean_dec(v_mctx_410_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(v_eAssignment_426_, v_mvarId_405_, v_val_406_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 8, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_depth_418_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_levelAssignDepth_419_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_lmvarCounter_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_mvarCounter_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_lDecls_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_decls_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_userNames_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_lAssignment_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 9, v_dAssignment_427_);
v___x_433_ = v_reuseFailAlloc_440_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_433_);
v___x_435_ = v___x_416_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_cache_411_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_zetaDeltaFVarIds_412_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_postponed_413_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_diag_414_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_st_ref_set(v___y_407_, v___x_435_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg___boxed(lean_object* v_mvarId_443_, lean_object* v_val_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v_mvarId_443_, v_val_444_, v___y_445_);
lean_dec(v___y_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(lean_object* v_fst_448_, lean_object* v_fst_449_, lean_object* v_args_450_, lean_object* v_range_451_, lean_object* v_b_452_, lean_object* v_i_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_stop_459_; lean_object* v_step_460_; uint8_t v___x_461_; 
v_stop_459_ = lean_ctor_get(v_range_451_, 1);
v_step_460_ = lean_ctor_get(v_range_451_, 2);
v___x_461_ = lean_nat_dec_lt(v_i_453_, v_stop_459_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v_i_453_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_b_452_);
return v___x_462_;
}
else
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_463_ = 0;
v___x_464_ = lean_box(0);
v___x_468_ = lean_box(v___x_463_);
v___x_469_ = lean_array_get(v___x_468_, v_fst_448_, v_i_453_);
lean_dec(v___x_468_);
v___x_470_ = lean_unbox(v___x_469_);
lean_dec(v___x_469_);
v___x_471_ = l_Lean_BinderInfo_isInstImplicit(v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_472_ = l_Lean_instInhabitedExpr;
v___x_473_ = lean_array_get_borrowed(v___x_472_, v_fst_449_, v_i_453_);
v___x_474_ = l_Lean_Expr_mvarId_x21(v___x_473_);
v___x_475_ = lean_array_get_borrowed(v___x_472_, v_args_450_, v_i_453_);
lean_inc(v___x_475_);
v___x_476_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_474_, v___x_475_, v___y_455_);
lean_dec_ref(v___x_476_);
goto v___jp_465_;
}
else
{
goto v___jp_465_;
}
v___jp_465_:
{
lean_object* v___x_466_; 
v___x_466_ = lean_nat_add(v_i_453_, v_step_460_);
lean_dec(v_i_453_);
v_b_452_ = v___x_464_;
v_i_453_ = v___x_466_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg___boxed(lean_object* v_fst_477_, lean_object* v_fst_478_, lean_object* v_args_479_, lean_object* v_range_480_, lean_object* v_b_481_, lean_object* v_i_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_477_, v_fst_478_, v_args_479_, v_range_480_, v_b_481_, v_i_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_range_480_);
lean_dec_ref(v_args_479_);
lean_dec_ref(v_fst_478_);
lean_dec_ref(v_fst_477_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0(void){
_start:
{
lean_object* v___x_489_; lean_object* v_dummy_490_; 
v___x_489_ = lean_box(0);
v_dummy_490_ = l_Lean_Expr_sort___override(v___x_489_);
return v_dummy_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs(lean_object* v_type_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_fn_497_; lean_object* v___x_498_; 
v_fn_497_ = l_Lean_Expr_getAppFn(v_type_491_);
lean_inc(v_a_495_);
lean_inc_ref(v_a_494_);
lean_inc(v_a_493_);
lean_inc_ref(v_a_492_);
lean_inc_ref(v_fn_497_);
v___x_498_ = lean_infer_type(v_fn_497_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; uint8_t v___x_500_; lean_object* v___x_501_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
v___x_500_ = 0;
v___x_501_ = l_Lean_Meta_forallMetaTelescope(v_a_499_, v___x_500_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v_snd_503_; lean_object* v_fst_504_; lean_object* v_fst_505_; lean_object* v_nargs_506_; lean_object* v_dummy_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_args_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v_snd_503_ = lean_ctor_get(v_a_502_, 1);
lean_inc(v_snd_503_);
v_fst_504_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_fst_504_);
lean_dec(v_a_502_);
v_fst_505_ = lean_ctor_get(v_snd_503_, 0);
lean_inc(v_fst_505_);
lean_dec(v_snd_503_);
v_nargs_506_ = l_Lean_Expr_getAppNumArgs(v_type_491_);
v_dummy_507_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
lean_inc(v_nargs_506_);
v___x_508_ = lean_mk_array(v_nargs_506_, v_dummy_507_);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_sub(v_nargs_506_, v___x_509_);
lean_dec(v_nargs_506_);
v_args_511_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_491_, v___x_508_, v___x_510_);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_array_get_size(v_fst_504_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
lean_ctor_set(v___x_514_, 2, v___x_509_);
v___x_515_ = lean_box(0);
v___x_516_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_505_, v_fst_504_, v_args_511_, v___x_514_, v___x_515_, v___x_512_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec_ref(v___x_514_);
lean_dec(v_fst_505_);
lean_dec_ref(v___x_516_);
v___x_517_ = lean_array_get_size(v_args_511_);
v___x_518_ = l_Array_extract___redArg(v_args_511_, v___x_513_, v___x_517_);
lean_dec_ref(v_args_511_);
v___x_519_ = l_Array_append___redArg(v_fst_504_, v___x_518_);
lean_dec_ref(v___x_518_);
v___x_520_ = l_Lean_mkAppN(v_fn_497_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v___x_520_, v_a_493_);
return v___x_521_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v_fn_497_);
lean_dec_ref(v_type_491_);
v_a_522_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_501_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_501_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_dec_ref(v_fn_497_);
lean_dec_ref(v_type_491_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs___boxed(lean_object* v_type_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_abstractInstImplicitArgs(v_type_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(lean_object* v_mvarId_537_, lean_object* v_val_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v_mvarId_537_, v_val_538_, v___y_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___boxed(lean_object* v_mvarId_545_, lean_object* v_val_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(v_mvarId_545_, v_val_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(lean_object* v_fst_553_, lean_object* v_fst_554_, lean_object* v_args_555_, lean_object* v_range_556_, lean_object* v_b_557_, lean_object* v_i_558_, lean_object* v_hs_559_, lean_object* v_hl_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_553_, v_fst_554_, v_args_555_, v_range_556_, v_b_557_, v_i_558_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___boxed(lean_object* v_fst_567_, lean_object* v_fst_568_, lean_object* v_args_569_, lean_object* v_range_570_, lean_object* v_b_571_, lean_object* v_i_572_, lean_object* v_hs_573_, lean_object* v_hl_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(v_fst_567_, v_fst_568_, v_args_569_, v_range_570_, v_b_571_, v_i_572_, v_hs_573_, v_hl_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec_ref(v_range_570_);
lean_dec_ref(v_args_569_);
lean_dec_ref(v_fst_568_);
lean_dec_ref(v_fst_567_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0(lean_object* v_00_u03b2_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(v_x_582_, v_x_583_, v_x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_586_, lean_object* v_x_587_, size_t v_x_588_, size_t v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_587_, v_x_588_, v_x_589_, v_x_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
size_t v_x_2584__boxed_599_; size_t v_x_2585__boxed_600_; lean_object* v_res_601_; 
v_x_2584__boxed_599_ = lean_unbox_usize(v_x_595_);
lean_dec(v_x_595_);
v_x_2585__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_res_601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(v_00_u03b2_593_, v_x_594_, v_x_2584__boxed_599_, v_x_2585__boxed_600_, v_x_597_, v_x_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_602_, lean_object* v_n_603_, lean_object* v_k_604_, lean_object* v_v_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(v_n_603_, v_k_604_, v_v_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_607_, size_t v_depth_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_heq_611_, lean_object* v_i_612_, lean_object* v_entries_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_608_, v_keys_609_, v_vals_610_, v_i_612_, v_entries_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_615_, lean_object* v_depth_616_, lean_object* v_keys_617_, lean_object* v_vals_618_, lean_object* v_heq_619_, lean_object* v_i_620_, lean_object* v_entries_621_){
_start:
{
size_t v_depth_boxed_622_; lean_object* v_res_623_; 
v_depth_boxed_622_ = lean_unbox_usize(v_depth_616_);
lean_dec(v_depth_616_);
v_res_623_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_615_, v_depth_boxed_622_, v_keys_617_, v_vals_618_, v_heq_619_, v_i_620_, v_entries_621_);
lean_dec_ref(v_vals_618_);
lean_dec_ref(v_keys_617_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_625_, v_x_626_, v_x_627_, v_x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(lean_object* v_msgData_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; lean_object* v_env_637_; lean_object* v___x_638_; lean_object* v_mctx_639_; lean_object* v_lctx_640_; lean_object* v_options_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_636_ = lean_st_ref_get(v___y_634_);
v_env_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_env_637_);
lean_dec(v___x_636_);
v___x_638_ = lean_st_ref_get(v___y_632_);
v_mctx_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc_ref(v_mctx_639_);
lean_dec(v___x_638_);
v_lctx_640_ = lean_ctor_get(v___y_631_, 2);
v_options_641_ = lean_ctor_get(v___y_633_, 2);
lean_inc_ref(v_options_641_);
lean_inc_ref(v_lctx_640_);
v___x_642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_642_, 0, v_env_637_);
lean_ctor_set(v___x_642_, 1, v_mctx_639_);
lean_ctor_set(v___x_642_, 2, v_lctx_640_);
lean_ctor_set(v___x_642_, 3, v_options_641_);
v___x_643_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_msgData_630_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1___boxed(lean_object* v_msgData_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msgData_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_ref_658_; lean_object* v___x_659_; lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_ref_658_ = lean_ctor_get(v___y_655_, 5);
v___x_659_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc(v_ref_658_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_ref_658_);
lean_ctor_set(v___x_664_, 1, v_a_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg___boxed(lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(lean_object* v_structName_685_, lean_object* v_field_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_692_; lean_object* v_env_693_; lean_object* v___x_694_; lean_object* v___x_695_; size_t v_sz_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_692_ = lean_st_ref_get(v_a_690_);
v_env_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc_ref_n(v_env_693_, 3);
lean_dec(v___x_692_);
lean_inc(v_structName_685_);
v___x_694_ = l_Lean_getStructureParentInfo(v_env_693_, v_structName_685_);
v___x_695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0));
v_sz_696_ = lean_array_size(v___x_694_);
v___x_697_ = ((size_t)0ULL);
lean_inc(v_field_686_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(v_env_693_, v_field_686_, v___x_694_, v_sz_696_, v___x_697_, v___x_695_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v___x_694_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_729_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_729_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_729_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_729_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_fst_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_727_; 
v_fst_703_ = lean_ctor_get(v_a_699_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_a_699_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_a_699_, 1);
lean_dec(v_unused_728_);
v___x_705_ = v_a_699_;
v_isShared_706_ = v_isSharedCheck_727_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_fst_703_);
lean_dec(v_a_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_727_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
if (lean_obj_tag(v_fst_703_) == 0)
{
lean_object* v___x_707_; 
lean_inc(v_field_686_);
lean_inc(v_structName_685_);
v___x_707_ = l_Lean_getFieldInfo_x3f(v_env_693_, v_structName_685_, v_field_686_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_710_; 
lean_dec(v_field_686_);
v_val_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref(v___x_707_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v_val_708_);
lean_ctor_set(v___x_705_, 0, v_structName_685_);
v___x_710_ = v___x_705_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_structName_685_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_val_708_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_710_);
v___x_712_ = v___x_701_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v___x_707_);
lean_del_object(v___x_705_);
lean_del_object(v___x_701_);
v___x_715_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1);
v___x_716_ = l_Lean_MessageData_ofName(v_field_686_);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = l_Lean_MessageData_ofName(v_structName_685_);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_721_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
return v___x_722_;
}
}
else
{
lean_object* v_val_723_; lean_object* v___x_725_; 
lean_del_object(v___x_705_);
lean_dec_ref(v_env_693_);
lean_dec(v_field_686_);
lean_dec(v_structName_685_);
v_val_723_ = lean_ctor_get(v_fst_703_, 0);
lean_inc(v_val_723_);
lean_dec_ref(v_fst_703_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_val_723_);
v___x_725_ = v___x_701_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_val_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_env_693_);
lean_dec(v_field_686_);
lean_dec(v_structName_685_);
v_a_730_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_698_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_698_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(lean_object* v___x_738_, lean_object* v_field_739_, lean_object* v_as_740_, size_t v_sz_741_, size_t v_i_742_, lean_object* v_b_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_lt(v_i_742_, v_sz_741_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec(v_field_739_);
lean_dec_ref(v___x_738_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_b_743_);
return v___x_750_;
}
else
{
lean_object* v_a_751_; lean_object* v_structName_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_b_743_);
v_a_751_ = lean_array_uget_borrowed(v_as_740_, v_i_742_);
v_structName_752_ = lean_ctor_get(v_a_751_, 0);
v___x_753_ = lean_box(0);
lean_inc(v_structName_752_);
lean_inc_ref(v___x_738_);
v___x_754_ = l_Lean_findField_x3f(v___x_738_, v_structName_752_, v_field_739_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; 
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0));
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_742_, v___x_756_);
v_i_742_ = v___x_757_;
v_b_743_ = v___x_755_;
goto _start;
}
else
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v___x_738_);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___x_754_, 0);
lean_dec(v_unused_784_);
v___x_760_ = v___x_754_;
v_isShared_761_ = v_isSharedCheck_783_;
goto v_resetjp_759_;
}
else
{
lean_dec(v___x_754_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_783_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; 
lean_inc(v_structName_752_);
v___x_762_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_structName_752_, v_field_739_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_774_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_774_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v_a_763_);
v___x_768_ = v___x_760_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_773_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_753_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_769_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_del_object(v___x_760_);
v_a_775_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_762_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_762_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___boxed(lean_object* v___x_785_, lean_object* v_field_786_, lean_object* v_as_787_, lean_object* v_sz_788_, lean_object* v_i_789_, lean_object* v_b_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
size_t v_sz_boxed_796_; size_t v_i_boxed_797_; lean_object* v_res_798_; 
v_sz_boxed_796_ = lean_unbox_usize(v_sz_788_);
lean_dec(v_sz_788_);
v_i_boxed_797_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(v___x_785_, v_field_786_, v_as_787_, v_sz_boxed_796_, v_i_boxed_797_, v_b_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec_ref(v_as_787_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___boxed(lean_object* v_structName_799_, lean_object* v_field_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_structName_799_, v_field_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(lean_object* v_00_u03b1_807_, lean_object* v_msg_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___boxed(lean_object* v_00_u03b1_815_, lean_object* v_msg_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(v_00_u03b1_815_, v_msg_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_823_; double v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_float_of_nat(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(lean_object* v_cls_830_, lean_object* v_msg_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_ref_837_; lean_object* v___x_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_883_; 
v_ref_837_ = lean_ctor_get(v___y_834_, 5);
v___x_838_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_883_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v_traceState_844_; lean_object* v_env_845_; lean_object* v_nextMacroScope_846_; lean_object* v_ngen_847_; lean_object* v_auxDeclNGen_848_; lean_object* v_cache_849_; lean_object* v_messages_850_; lean_object* v_infoState_851_; lean_object* v_snapshotTasks_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_882_; 
v___x_843_ = lean_st_ref_take(v___y_835_);
v_traceState_844_ = lean_ctor_get(v___x_843_, 4);
v_env_845_ = lean_ctor_get(v___x_843_, 0);
v_nextMacroScope_846_ = lean_ctor_get(v___x_843_, 1);
v_ngen_847_ = lean_ctor_get(v___x_843_, 2);
v_auxDeclNGen_848_ = lean_ctor_get(v___x_843_, 3);
v_cache_849_ = lean_ctor_get(v___x_843_, 5);
v_messages_850_ = lean_ctor_get(v___x_843_, 6);
v_infoState_851_ = lean_ctor_get(v___x_843_, 7);
v_snapshotTasks_852_ = lean_ctor_get(v___x_843_, 8);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_882_ == 0)
{
v___x_854_ = v___x_843_;
v_isShared_855_ = v_isSharedCheck_882_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snapshotTasks_852_);
lean_inc(v_infoState_851_);
lean_inc(v_messages_850_);
lean_inc(v_cache_849_);
lean_inc(v_traceState_844_);
lean_inc(v_auxDeclNGen_848_);
lean_inc(v_ngen_847_);
lean_inc(v_nextMacroScope_846_);
lean_inc(v_env_845_);
lean_dec(v___x_843_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_882_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint64_t v_tid_856_; lean_object* v_traces_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_881_; 
v_tid_856_ = lean_ctor_get_uint64(v_traceState_844_, sizeof(void*)*1);
v_traces_857_ = lean_ctor_get(v_traceState_844_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_traceState_844_);
if (v_isSharedCheck_881_ == 0)
{
v___x_859_ = v_traceState_844_;
v_isShared_860_ = v_isSharedCheck_881_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_traces_857_);
lean_dec(v_traceState_844_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_881_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; double v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_861_ = lean_box(0);
v___x_862_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
v___x_863_ = 0;
v___x_864_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_865_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_865_, 0, v_cls_830_);
lean_ctor_set(v___x_865_, 1, v___x_861_);
lean_ctor_set(v___x_865_, 2, v___x_864_);
lean_ctor_set_float(v___x_865_, sizeof(void*)*3, v___x_862_);
lean_ctor_set_float(v___x_865_, sizeof(void*)*3 + 8, v___x_862_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*3 + 16, v___x_863_);
v___x_866_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2));
v___x_867_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v_a_839_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
lean_inc(v_ref_837_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_ref_837_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_PersistentArray_push___redArg(v_traces_857_, v___x_868_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_869_);
v___x_871_ = v___x_859_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_869_);
lean_ctor_set_uint64(v_reuseFailAlloc_880_, sizeof(void*)*1, v_tid_856_);
v___x_871_ = v_reuseFailAlloc_880_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 4, v___x_871_);
v___x_873_ = v___x_854_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_env_845_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_nextMacroScope_846_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_ngen_847_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_auxDeclNGen_848_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v_cache_849_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_messages_850_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_infoState_851_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_snapshotTasks_852_);
v___x_873_ = v_reuseFailAlloc_879_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = lean_st_ref_set(v___y_835_, v___x_873_);
v___x_875_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3));
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_875_);
v___x_877_ = v___x_841_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___boxed(lean_object* v_cls_884_, lean_object* v_msg_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v_cls_884_, v_msg_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_896_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1));
v___x_897_ = l_Lean_Name_append(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_x_904_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
else
{
lean_object* v_head_916_; lean_object* v_tail_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_975_; 
v_head_916_ = lean_ctor_get(v_x_905_, 0);
v_tail_917_ = lean_ctor_get(v_x_905_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_905_);
if (v_isSharedCheck_975_ == 0)
{
v___x_919_ = v_x_905_;
v_isShared_920_ = v_isSharedCheck_975_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_tail_917_);
lean_inc(v_head_916_);
lean_dec(v_x_905_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_975_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; 
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc_ref(v_x_904_);
v___x_921_ = lean_infer_type(v_x_904_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
v___x_923_ = lean_whnf(v_a_922_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_925_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
v___x_925_ = l_Lean_Expr_getAppFn(v_a_924_);
if (lean_obj_tag(v___x_925_) == 4)
{
lean_object* v_us_926_; lean_object* v_dummy_927_; lean_object* v_nargs_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_del_object(v___x_919_);
v_us_926_ = lean_ctor_get(v___x_925_, 1);
lean_inc(v_us_926_);
lean_dec_ref(v___x_925_);
v_dummy_927_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_928_ = l_Lean_Expr_getAppNumArgs(v_a_924_);
lean_inc(v_nargs_928_);
v___x_929_ = lean_mk_array(v_nargs_928_, v_dummy_927_);
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_sub(v_nargs_928_, v___x_930_);
lean_dec(v_nargs_928_);
v___x_932_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_924_, v___x_929_, v___x_931_);
v___x_933_ = l_Lean_Expr_const___override(v_head_916_, v_us_926_);
v___x_934_ = l_Lean_mkAppN(v___x_933_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_935_ = l_Lean_Expr_app___override(v___x_934_, v_x_904_);
v_x_904_ = v___x_935_;
v_x_905_ = v_tail_917_;
goto _start;
}
else
{
lean_object* v_options_937_; uint8_t v_hasTrace_938_; 
lean_dec_ref(v___x_925_);
lean_dec(v_tail_917_);
lean_dec(v_head_916_);
lean_dec_ref(v_x_904_);
v_options_937_ = lean_ctor_get(v___y_908_, 2);
v_hasTrace_938_ = lean_ctor_get_uint8(v_options_937_, sizeof(void*)*1);
if (v_hasTrace_938_ == 0)
{
lean_dec(v_a_924_);
lean_del_object(v___x_919_);
goto v___jp_911_;
}
else
{
lean_object* v_inheritedTraceOptions_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_inheritedTraceOptions_939_ = lean_ctor_get(v___y_908_, 13);
v___x_940_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_941_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_942_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_939_, v_options_937_, v___x_941_);
if (v___x_942_ == 0)
{
lean_dec(v_a_924_);
lean_del_object(v___x_919_);
goto v___jp_911_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4);
v___x_944_ = l_Lean_MessageData_ofExpr(v_a_924_);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 7);
lean_ctor_set(v___x_919_, 1, v___x_944_);
lean_ctor_set(v___x_919_, 0, v___x_943_);
v___x_946_ = v___x_919_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_944_);
v___x_946_ = v_reuseFailAlloc_958_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v___x_940_, v___x_948_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_dec_ref(v___x_949_);
goto v___jp_911_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
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
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_del_object(v___x_919_);
lean_dec(v_tail_917_);
lean_dec(v_head_916_);
lean_dec_ref(v_x_904_);
v_a_959_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_923_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_923_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_919_);
lean_dec(v_tail_917_);
lean_dec(v_head_916_);
lean_dec_ref(v_x_904_);
v_a_967_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_921_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_921_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
v___jp_911_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_box(0);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___boxed(lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(v_x_976_, v_x_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_983_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(lean_object* v_val_987_, lean_object* v_self_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_997_; 
lean_inc_ref(v_self_988_);
v___x_997_ = l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(v_self_988_, v_val_987_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
if (lean_obj_tag(v_a_998_) == 0)
{
lean_dec_ref(v_self_988_);
return v___x_997_;
}
else
{
lean_object* v_val_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v___x_997_);
v_val_999_ = lean_ctor_get(v_a_998_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_a_998_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1001_ = v_a_998_;
v_isShared_1002_ = v_isSharedCheck_1053_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_val_999_);
lean_dec(v_a_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1053_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; 
lean_inc(v___y_992_);
lean_inc_ref(v___y_991_);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
v___x_1003_ = lean_infer_type(v_val_999_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
lean_inc(v___y_992_);
lean_inc_ref(v___y_991_);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
v___x_1005_ = lean_whnf(v_a_1004_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1036_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1036_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1036_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = l_Lean_Expr_fvarId_x21(v_self_988_);
lean_dec_ref(v_self_988_);
v___x_1011_ = l_Lean_Expr_containsFVar(v_a_1006_, v___x_1010_);
lean_dec(v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1013_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_a_1006_);
v___x_1013_ = v___x_1001_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1006_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1013_);
v___x_1015_ = v___x_1008_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v_options_1018_; uint8_t v_hasTrace_1019_; 
lean_del_object(v___x_1008_);
lean_del_object(v___x_1001_);
v_options_1018_ = lean_ctor_get(v___y_991_, 2);
v_hasTrace_1019_ = lean_ctor_get_uint8(v_options_1018_, sizeof(void*)*1);
if (v_hasTrace_1019_ == 0)
{
lean_dec(v_a_1006_);
goto v___jp_994_;
}
else
{
lean_object* v_inheritedTraceOptions_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_inheritedTraceOptions_1020_ = lean_ctor_get(v___y_991_, 13);
v___x_1021_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_1022_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_1023_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1020_, v_options_1018_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_dec(v_a_1006_);
goto v___jp_994_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1);
v___x_1025_ = l_Lean_indentExpr(v_a_1006_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v___x_1021_, v___x_1026_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_dec_ref(v___x_1027_);
goto v___jp_994_;
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
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
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_del_object(v___x_1001_);
lean_dec_ref(v_self_988_);
v_a_1037_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1005_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1005_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_del_object(v___x_1001_);
lean_dec_ref(v_self_988_);
v_a_1045_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1003_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1003_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_self_988_);
return v___x_997_;
}
v___jp_994_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed(lean_object* v_val_1054_, lean_object* v_self_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(v_val_1054_, v_self_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(lean_object* v_k_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
v___x_1069_ = lean_apply_6(v_k_1062_, v_b_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, lean_box(0));
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_k_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(v_k_1070_, v_b_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(lean_object* v_name_1078_, uint8_t v_bi_1079_, lean_object* v_type_1080_, lean_object* v_k_1081_, uint8_t v_kind_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___f_1088_; lean_object* v___x_1089_; 
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1088_, 0, v_k_1081_);
v___x_1089_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1078_, v_bi_1079_, v_type_1080_, v___f_1088_, v_kind_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1089_) == 0)
{
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_name_1098_, lean_object* v_bi_1099_, lean_object* v_type_1100_, lean_object* v_k_1101_, lean_object* v_kind_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v_bi_boxed_1108_; uint8_t v_kind_boxed_1109_; lean_object* v_res_1110_; 
v_bi_boxed_1108_ = lean_unbox(v_bi_1099_);
v_kind_boxed_1109_ = lean_unbox(v_kind_1102_);
v_res_1110_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_1098_, v_bi_boxed_1108_, v_type_1100_, v_k_1101_, v_kind_boxed_1109_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(lean_object* v_name_1111_, lean_object* v_type_1112_, lean_object* v_k_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = 0;
v___x_1120_ = 0;
v___x_1121_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_1111_, v___x_1119_, v_type_1112_, v_k_1113_, v___x_1120_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg___boxed(lean_object* v_name_1122_, lean_object* v_type_1123_, lean_object* v_k_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v_name_1122_, v_type_1123_, v_k_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(lean_object* v_structName_1134_, lean_object* v_parentStructName_1135_, lean_object* v_structType_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v_env_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_st_ref_get(v_a_1140_);
v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_env_1143_);
lean_dec(v___x_1142_);
v___x_1144_ = l_Lean_getPathToBaseStructure_x3f(v_env_1143_, v_parentStructName_1135_, v_structName_1134_);
if (lean_obj_tag(v___x_1144_) == 1)
{
lean_object* v_val_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_val_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_val_1145_);
lean_dec_ref(v___x_1144_);
v___f_1146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1146_, 0, v_val_1145_);
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1));
v___x_1148_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v___x_1147_, v_structType_1136_, v___f_1146_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v___x_1144_);
lean_dec_ref(v_structType_1136_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___boxed(lean_object* v_structName_1151_, lean_object* v_parentStructName_1152_, lean_object* v_structType_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_structName_1151_, v_parentStructName_1152_, v_structType_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(lean_object* v_00_u03b1_1160_, lean_object* v_name_1161_, uint8_t v_bi_1162_, lean_object* v_type_1163_, lean_object* v_k_1164_, uint8_t v_kind_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_1161_, v_bi_1162_, v_type_1163_, v_k_1164_, v_kind_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_name_1173_, lean_object* v_bi_1174_, lean_object* v_type_1175_, lean_object* v_k_1176_, lean_object* v_kind_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_bi_boxed_1183_; uint8_t v_kind_boxed_1184_; lean_object* v_res_1185_; 
v_bi_boxed_1183_ = lean_unbox(v_bi_1174_);
v_kind_boxed_1184_ = lean_unbox(v_kind_1177_);
v_res_1185_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(v_00_u03b1_1172_, v_name_1173_, v_bi_boxed_1183_, v_type_1175_, v_k_1176_, v_kind_boxed_1184_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(lean_object* v_00_u03b1_1186_, lean_object* v_name_1187_, lean_object* v_type_1188_, lean_object* v_k_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v_name_1187_, v_type_1188_, v_k_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___boxed(lean_object* v_00_u03b1_1196_, lean_object* v_name_1197_, lean_object* v_type_1198_, lean_object* v_k_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(v_00_u03b1_1196_, v_name_1197_, v_type_1198_, v_k_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object* v_opts_1206_, lean_object* v_opt_1207_){
_start:
{
lean_object* v_name_1208_; lean_object* v_defValue_1209_; lean_object* v_map_1210_; lean_object* v___x_1211_; 
v_name_1208_ = lean_ctor_get(v_opt_1207_, 0);
v_defValue_1209_ = lean_ctor_get(v_opt_1207_, 1);
v_map_1210_ = lean_ctor_get(v_opts_1206_, 0);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1210_, v_name_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_unbox(v_defValue_1209_);
return v___x_1212_;
}
else
{
lean_object* v_val_1213_; 
v_val_1213_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v___x_1211_);
if (lean_obj_tag(v_val_1213_) == 1)
{
uint8_t v_v_1214_; 
v_v_1214_ = lean_ctor_get_uint8(v_val_1213_, 0);
lean_dec_ref(v_val_1213_);
return v_v_1214_;
}
else
{
uint8_t v___x_1215_; 
lean_dec(v_val_1213_);
v___x_1215_ = lean_unbox(v_defValue_1209_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object* v_opts_1216_, lean_object* v_opt_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_1216_, v_opt_1217_);
lean_dec_ref(v_opt_1217_);
lean_dec_ref(v_opts_1216_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object* v_kind_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v_auxDeclNGen_1224_; lean_object* v___x_1225_; lean_object* v_env_1226_; lean_object* v___x_1227_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v___x_1230_; lean_object* v_env_1231_; lean_object* v_nextMacroScope_1232_; lean_object* v_ngen_1233_; lean_object* v_traceState_1234_; lean_object* v_cache_1235_; lean_object* v_messages_1236_; lean_object* v_infoState_1237_; lean_object* v_snapshotTasks_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1247_; 
v___x_1223_ = lean_st_ref_get(v___y_1221_);
v_auxDeclNGen_1224_ = lean_ctor_get(v___x_1223_, 3);
lean_inc_ref(v_auxDeclNGen_1224_);
lean_dec(v___x_1223_);
v___x_1225_ = lean_st_ref_get(v___y_1221_);
v_env_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_ref(v_env_1226_);
lean_dec(v___x_1225_);
v___x_1227_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_1226_, v_auxDeclNGen_1224_, v_kind_1220_);
v_fst_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_fst_1228_);
v_snd_1229_ = lean_ctor_get(v___x_1227_, 1);
lean_inc(v_snd_1229_);
lean_dec_ref(v___x_1227_);
v___x_1230_ = lean_st_ref_take(v___y_1221_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
v_nextMacroScope_1232_ = lean_ctor_get(v___x_1230_, 1);
v_ngen_1233_ = lean_ctor_get(v___x_1230_, 2);
v_traceState_1234_ = lean_ctor_get(v___x_1230_, 4);
v_cache_1235_ = lean_ctor_get(v___x_1230_, 5);
v_messages_1236_ = lean_ctor_get(v___x_1230_, 6);
v_infoState_1237_ = lean_ctor_get(v___x_1230_, 7);
v_snapshotTasks_1238_ = lean_ctor_get(v___x_1230_, 8);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1230_, 3);
lean_dec(v_unused_1248_);
v___x_1240_ = v___x_1230_;
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snapshotTasks_1238_);
lean_inc(v_infoState_1237_);
lean_inc(v_messages_1236_);
lean_inc(v_cache_1235_);
lean_inc(v_traceState_1234_);
lean_inc(v_ngen_1233_);
lean_inc(v_nextMacroScope_1232_);
lean_inc(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 3, v_snd_1229_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_env_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_nextMacroScope_1232_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_ngen_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_snd_1229_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_traceState_1234_);
lean_ctor_set(v_reuseFailAlloc_1246_, 5, v_cache_1235_);
lean_ctor_set(v_reuseFailAlloc_1246_, 6, v_messages_1236_);
lean_ctor_set(v_reuseFailAlloc_1246_, 7, v_infoState_1237_);
lean_ctor_set(v_reuseFailAlloc_1246_, 8, v_snapshotTasks_1238_);
v___x_1243_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_st_ref_set(v___y_1221_, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_fst_1228_);
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object* v_kind_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_1249_, v___y_1250_);
lean_dec(v___y_1250_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object* v_kind_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_1253_, v___y_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object* v_kind_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(v_kind_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1266_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
return v___x_1271_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_1273_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
lean_ctor_set(v___x_1273_, 3, v___x_1272_);
lean_ctor_set(v___x_1273_, 4, v___x_1272_);
lean_ctor_set(v___x_1273_, 5, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object* v_declName_1274_, uint8_t v_s_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v_env_1280_; lean_object* v_nextMacroScope_1281_; lean_object* v_ngen_1282_; lean_object* v_auxDeclNGen_1283_; lean_object* v_traceState_1284_; lean_object* v_messages_1285_; lean_object* v_infoState_1286_; lean_object* v_snapshotTasks_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1316_; 
v___x_1279_ = lean_st_ref_take(v___y_1277_);
v_env_1280_ = lean_ctor_get(v___x_1279_, 0);
v_nextMacroScope_1281_ = lean_ctor_get(v___x_1279_, 1);
v_ngen_1282_ = lean_ctor_get(v___x_1279_, 2);
v_auxDeclNGen_1283_ = lean_ctor_get(v___x_1279_, 3);
v_traceState_1284_ = lean_ctor_get(v___x_1279_, 4);
v_messages_1285_ = lean_ctor_get(v___x_1279_, 6);
v_infoState_1286_ = lean_ctor_get(v___x_1279_, 7);
v_snapshotTasks_1287_ = lean_ctor_get(v___x_1279_, 8);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1279_, 5);
lean_dec(v_unused_1317_);
v___x_1289_ = v___x_1279_;
v_isShared_1290_ = v_isSharedCheck_1316_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_snapshotTasks_1287_);
lean_inc(v_infoState_1286_);
lean_inc(v_messages_1285_);
lean_inc(v_traceState_1284_);
lean_inc(v_auxDeclNGen_1283_);
lean_inc(v_ngen_1282_);
lean_inc(v_nextMacroScope_1281_);
lean_inc(v_env_1280_);
lean_dec(v___x_1279_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1316_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1291_ = 0;
v___x_1292_ = lean_box(0);
v___x_1293_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1280_, v_declName_1274_, v_s_1275_, v___x_1291_, v___x_1292_);
v___x_1294_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 5, v___x_1294_);
lean_ctor_set(v___x_1289_, 0, v___x_1293_);
v___x_1296_ = v___x_1289_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_nextMacroScope_1281_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_ngen_1282_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_auxDeclNGen_1283_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_traceState_1284_);
lean_ctor_set(v_reuseFailAlloc_1315_, 5, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1315_, 6, v_messages_1285_);
lean_ctor_set(v_reuseFailAlloc_1315_, 7, v_infoState_1286_);
lean_ctor_set(v_reuseFailAlloc_1315_, 8, v_snapshotTasks_1287_);
v___x_1296_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_mctx_1299_; lean_object* v_zetaDeltaFVarIds_1300_; lean_object* v_postponed_1301_; lean_object* v_diag_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1313_; 
v___x_1297_ = lean_st_ref_set(v___y_1277_, v___x_1296_);
v___x_1298_ = lean_st_ref_take(v___y_1276_);
v_mctx_1299_ = lean_ctor_get(v___x_1298_, 0);
v_zetaDeltaFVarIds_1300_ = lean_ctor_get(v___x_1298_, 2);
v_postponed_1301_ = lean_ctor_get(v___x_1298_, 3);
v_diag_1302_ = lean_ctor_get(v___x_1298_, 4);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1298_, 1);
lean_dec(v_unused_1314_);
v___x_1304_ = v___x_1298_;
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_diag_1302_);
lean_inc(v_postponed_1301_);
lean_inc(v_zetaDeltaFVarIds_1300_);
lean_inc(v_mctx_1299_);
lean_dec(v___x_1298_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___x_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_mctx_1299_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_zetaDeltaFVarIds_1300_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_postponed_1301_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_diag_1302_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_st_ref_set(v___y_1276_, v___x_1308_);
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object* v_declName_1318_, lean_object* v_s_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v_s_boxed_1323_; lean_object* v_res_1324_; 
v_s_boxed_1323_ = lean_unbox(v_s_1319_);
v_res_1324_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_1318_, v_s_boxed_1323_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object* v_declName_1325_, uint8_t v_s_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_1325_, v_s_1326_, v___y_1328_, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object* v_declName_1333_, lean_object* v_s_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_s_boxed_1340_; lean_object* v_res_1341_; 
v_s_boxed_1340_ = lean_unbox(v_s_1334_);
v_res_1341_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(v_declName_1333_, v_s_boxed_1340_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1341_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = lean_unsigned_to_nat(32u);
v___x_1343_ = lean_mk_empty_array_with_capacity(v___x_1342_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1345_ = ((size_t)5ULL);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_unsigned_to_nat(32u);
v___x_1348_ = lean_mk_empty_array_with_capacity(v___x_1347_);
v___x_1349_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__0);
v___x_1350_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1346_);
lean_ctor_set(v___x_1350_, 3, v___x_1346_);
lean_ctor_set_usize(v___x_1350_, 4, v___x_1345_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg(lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v_traceState_1354_; lean_object* v_traces_1355_; lean_object* v___x_1356_; lean_object* v_traceState_1357_; lean_object* v_env_1358_; lean_object* v_nextMacroScope_1359_; lean_object* v_ngen_1360_; lean_object* v_auxDeclNGen_1361_; lean_object* v_cache_1362_; lean_object* v_messages_1363_; lean_object* v_infoState_1364_; lean_object* v_snapshotTasks_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1384_; 
v___x_1353_ = lean_st_ref_get(v___y_1351_);
v_traceState_1354_ = lean_ctor_get(v___x_1353_, 4);
lean_inc_ref(v_traceState_1354_);
lean_dec(v___x_1353_);
v_traces_1355_ = lean_ctor_get(v_traceState_1354_, 0);
lean_inc_ref(v_traces_1355_);
lean_dec_ref(v_traceState_1354_);
v___x_1356_ = lean_st_ref_take(v___y_1351_);
v_traceState_1357_ = lean_ctor_get(v___x_1356_, 4);
v_env_1358_ = lean_ctor_get(v___x_1356_, 0);
v_nextMacroScope_1359_ = lean_ctor_get(v___x_1356_, 1);
v_ngen_1360_ = lean_ctor_get(v___x_1356_, 2);
v_auxDeclNGen_1361_ = lean_ctor_get(v___x_1356_, 3);
v_cache_1362_ = lean_ctor_get(v___x_1356_, 5);
v_messages_1363_ = lean_ctor_get(v___x_1356_, 6);
v_infoState_1364_ = lean_ctor_get(v___x_1356_, 7);
v_snapshotTasks_1365_ = lean_ctor_get(v___x_1356_, 8);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1367_ = v___x_1356_;
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snapshotTasks_1365_);
lean_inc(v_infoState_1364_);
lean_inc(v_messages_1363_);
lean_inc(v_cache_1362_);
lean_inc(v_traceState_1357_);
lean_inc(v_auxDeclNGen_1361_);
lean_inc(v_ngen_1360_);
lean_inc(v_nextMacroScope_1359_);
lean_inc(v_env_1358_);
lean_dec(v___x_1356_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
uint64_t v_tid_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1382_; 
v_tid_1369_ = lean_ctor_get_uint64(v_traceState_1357_, sizeof(void*)*1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_traceState_1357_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_traceState_1357_, 0);
lean_dec(v_unused_1383_);
v___x_1371_ = v_traceState_1357_;
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_traceState_1357_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___closed__1);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1373_);
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1373_);
lean_ctor_set_uint64(v_reuseFailAlloc_1381_, sizeof(void*)*1, v_tid_1369_);
v___x_1375_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v___x_1375_);
v___x_1377_ = v___x_1367_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_env_1358_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_nextMacroScope_1359_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_ngen_1360_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_auxDeclNGen_1361_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1380_, 5, v_cache_1362_);
lean_ctor_set(v_reuseFailAlloc_1380_, 6, v_messages_1363_);
lean_ctor_set(v_reuseFailAlloc_1380_, 7, v_infoState_1364_);
lean_ctor_set(v_reuseFailAlloc_1380_, 8, v_snapshotTasks_1365_);
v___x_1377_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_st_ref_set(v___y_1351_, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_traces_1355_);
return v___x_1379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg___boxed(lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg(v___y_1385_);
lean_dec(v___y_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9(lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg(v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___boxed(lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9(v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Lean_Meta_wrapInstance___lam__0___closed__0));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object* v_expectedType_1403_, lean_object* v_x_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = lean_obj_once(&l_Lean_Meta_wrapInstance___lam__0___closed__1, &l_Lean_Meta_wrapInstance___lam__0___closed__1_once, _init_l_Lean_Meta_wrapInstance___lam__0___closed__1);
v___x_1411_ = l_Lean_MessageData_ofExpr(v_expectedType_1403_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object* v_expectedType_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Meta_wrapInstance___lam__0(v_expectedType_1414_, v_x_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v_x_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___redArg(lean_object* v_ref_1422_, lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_fileName_1429_; lean_object* v_fileMap_1430_; lean_object* v_options_1431_; lean_object* v_currRecDepth_1432_; lean_object* v_maxRecDepth_1433_; lean_object* v_ref_1434_; lean_object* v_currNamespace_1435_; lean_object* v_openDecls_1436_; lean_object* v_initHeartbeats_1437_; lean_object* v_maxHeartbeats_1438_; lean_object* v_quotContext_1439_; lean_object* v_currMacroScope_1440_; uint8_t v_diag_1441_; lean_object* v_cancelTk_x3f_1442_; uint8_t v_suppressElabErrors_1443_; lean_object* v_inheritedTraceOptions_1444_; lean_object* v_ref_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_fileName_1429_ = lean_ctor_get(v___y_1426_, 0);
v_fileMap_1430_ = lean_ctor_get(v___y_1426_, 1);
v_options_1431_ = lean_ctor_get(v___y_1426_, 2);
v_currRecDepth_1432_ = lean_ctor_get(v___y_1426_, 3);
v_maxRecDepth_1433_ = lean_ctor_get(v___y_1426_, 4);
v_ref_1434_ = lean_ctor_get(v___y_1426_, 5);
v_currNamespace_1435_ = lean_ctor_get(v___y_1426_, 6);
v_openDecls_1436_ = lean_ctor_get(v___y_1426_, 7);
v_initHeartbeats_1437_ = lean_ctor_get(v___y_1426_, 8);
v_maxHeartbeats_1438_ = lean_ctor_get(v___y_1426_, 9);
v_quotContext_1439_ = lean_ctor_get(v___y_1426_, 10);
v_currMacroScope_1440_ = lean_ctor_get(v___y_1426_, 11);
v_diag_1441_ = lean_ctor_get_uint8(v___y_1426_, sizeof(void*)*14);
v_cancelTk_x3f_1442_ = lean_ctor_get(v___y_1426_, 12);
v_suppressElabErrors_1443_ = lean_ctor_get_uint8(v___y_1426_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1444_ = lean_ctor_get(v___y_1426_, 13);
v_ref_1445_ = l_Lean_replaceRef(v_ref_1422_, v_ref_1434_);
lean_inc_ref(v_inheritedTraceOptions_1444_);
lean_inc(v_cancelTk_x3f_1442_);
lean_inc(v_currMacroScope_1440_);
lean_inc(v_quotContext_1439_);
lean_inc(v_maxHeartbeats_1438_);
lean_inc(v_initHeartbeats_1437_);
lean_inc(v_openDecls_1436_);
lean_inc(v_currNamespace_1435_);
lean_inc(v_maxRecDepth_1433_);
lean_inc(v_currRecDepth_1432_);
lean_inc_ref(v_options_1431_);
lean_inc_ref(v_fileMap_1430_);
lean_inc_ref(v_fileName_1429_);
v___x_1446_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1446_, 0, v_fileName_1429_);
lean_ctor_set(v___x_1446_, 1, v_fileMap_1430_);
lean_ctor_set(v___x_1446_, 2, v_options_1431_);
lean_ctor_set(v___x_1446_, 3, v_currRecDepth_1432_);
lean_ctor_set(v___x_1446_, 4, v_maxRecDepth_1433_);
lean_ctor_set(v___x_1446_, 5, v_ref_1445_);
lean_ctor_set(v___x_1446_, 6, v_currNamespace_1435_);
lean_ctor_set(v___x_1446_, 7, v_openDecls_1436_);
lean_ctor_set(v___x_1446_, 8, v_initHeartbeats_1437_);
lean_ctor_set(v___x_1446_, 9, v_maxHeartbeats_1438_);
lean_ctor_set(v___x_1446_, 10, v_quotContext_1439_);
lean_ctor_set(v___x_1446_, 11, v_currMacroScope_1440_);
lean_ctor_set(v___x_1446_, 12, v_cancelTk_x3f_1442_);
lean_ctor_set(v___x_1446_, 13, v_inheritedTraceOptions_1444_);
lean_ctor_set_uint8(v___x_1446_, sizeof(void*)*14, v_diag_1441_);
lean_ctor_set_uint8(v___x_1446_, sizeof(void*)*14 + 1, v_suppressElabErrors_1443_);
v___x_1447_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_1423_, v___y_1424_, v___y_1425_, v___x_1446_, v___y_1427_);
lean_dec_ref(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___redArg___boxed(lean_object* v_ref_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___redArg(v_ref_1448_, v_msg_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v_ref_1448_);
return v_res_1455_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__0);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
lean_ctor_set(v___x_1461_, 2, v___x_1460_);
lean_ctor_set(v___x_1461_, 3, v___x_1460_);
lean_ctor_set(v___x_1461_, 4, v___x_1459_);
lean_ctor_set(v___x_1461_, 5, v___x_1459_);
lean_ctor_set(v___x_1461_, 6, v___x_1459_);
lean_ctor_set(v___x_1461_, 7, v___x_1459_);
lean_ctor_set(v___x_1461_, 8, v___x_1459_);
lean_ctor_set(v___x_1461_, 9, v___x_1459_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_unsigned_to_nat(32u);
v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1465_ = ((size_t)5ULL);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_unsigned_to_nat(32u);
v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
v___x_1469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__3);
v___x_1470_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v___x_1468_);
lean_ctor_set(v___x_1470_, 2, v___x_1466_);
lean_ctor_set(v___x_1470_, 3, v___x_1466_);
lean_ctor_set_usize(v___x_1470_, 4, v___x_1465_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_box(1);
v___x_1472_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__4);
v___x_1473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__1);
v___x_1474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
lean_ctor_set(v___x_1474_, 2, v___x_1471_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__6));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__8));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__10));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__12));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__14));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__16));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__18));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg(lean_object* v_msg_1496_, lean_object* v_declHint_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v_env_1501_; uint8_t v___x_1502_; 
v___x_1500_ = lean_st_ref_get(v___y_1498_);
v_env_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_ref(v_env_1501_);
lean_dec(v___x_1500_);
v___x_1502_ = l_Lean_Name_isAnonymous(v_declHint_1497_);
if (v___x_1502_ == 0)
{
uint8_t v_isExporting_1503_; 
v_isExporting_1503_ = lean_ctor_get_uint8(v_env_1501_, sizeof(void*)*8);
if (v_isExporting_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_dec_ref(v_env_1501_);
lean_dec(v_declHint_1497_);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_msg_1496_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
lean_inc_ref(v_env_1501_);
v___x_1505_ = l_Lean_Environment_setExporting(v_env_1501_, v___x_1502_);
lean_inc(v_declHint_1497_);
lean_inc_ref(v___x_1505_);
v___x_1506_ = l_Lean_Environment_contains(v___x_1505_, v_declHint_1497_, v_isExporting_1503_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_dec_ref(v___x_1505_);
lean_dec_ref(v_env_1501_);
lean_dec(v_declHint_1497_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_msg_1496_);
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_c_1513_; lean_object* v___x_1514_; 
v___x_1508_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__2);
v___x_1509_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__5);
v___x_1510_ = l_Lean_Options_empty;
v___x_1511_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1505_);
lean_ctor_set(v___x_1511_, 1, v___x_1508_);
lean_ctor_set(v___x_1511_, 2, v___x_1509_);
lean_ctor_set(v___x_1511_, 3, v___x_1510_);
lean_inc(v_declHint_1497_);
v___x_1512_ = l_Lean_MessageData_ofConstName(v_declHint_1497_, v___x_1502_);
v_c_1513_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1513_, 0, v___x_1511_);
lean_ctor_set(v_c_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1501_, v_declHint_1497_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec_ref(v_env_1501_);
lean_dec(v_declHint_1497_);
v___x_1515_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v_c_1513_);
v___x_1517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__9);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = l_Lean_MessageData_note(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1520_, 0, v_msg_1496_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
else
{
lean_object* v_val_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1557_; 
v_val_1522_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1524_ = v___x_1514_;
v_isShared_1525_ = v_isSharedCheck_1557_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_val_1522_);
lean_dec(v___x_1514_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1557_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_mod_1529_; uint8_t v___x_1530_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = l_Lean_Environment_header(v_env_1501_);
lean_dec_ref(v_env_1501_);
v___x_1528_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1527_);
v_mod_1529_ = lean_array_get(v___x_1526_, v___x_1528_, v_val_1522_);
lean_dec(v_val_1522_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = l_Lean_isPrivateName(v_declHint_1497_);
lean_dec(v_declHint_1497_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__11);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_c_1513_);
v___x_1533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__13);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = l_Lean_MessageData_ofName(v_mod_1529_);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__15);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_MessageData_note(v___x_1538_);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_msg_1496_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1540_);
v___x_1542_ = v___x_1524_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1544_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__7);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v_c_1513_);
v___x_1546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__17);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_MessageData_ofName(v_mod_1529_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___closed__19);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_MessageData_note(v___x_1551_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_msg_1496_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1553_);
v___x_1555_ = v___x_1524_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1558_; 
lean_dec_ref(v_env_1501_);
lean_dec(v_declHint_1497_);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_msg_1496_);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg___boxed(lean_object* v_msg_1559_, lean_object* v_declHint_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg(v_msg_1559_, v_declHint_1560_, v___y_1561_);
lean_dec(v___y_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25(lean_object* v_msg_1564_, lean_object* v_declHint_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1581_; 
v___x_1571_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg(v_msg_1564_, v_declHint_1565_, v___y_1569_);
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1576_ = l_Lean_unknownIdentifierMessageTag;
v___x_1577_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v_a_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1577_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25___boxed(lean_object* v_msg_1582_, lean_object* v_declHint_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25(v_msg_1582_, v_declHint_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___redArg(lean_object* v_ref_1590_, lean_object* v_msg_1591_, lean_object* v_declHint_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_a_1599_; lean_object* v___x_1600_; 
v___x_1598_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25(v_msg_1591_, v_declHint_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___redArg(v_ref_1590_, v_a_1599_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___redArg___boxed(lean_object* v_ref_1601_, lean_object* v_msg_1602_, lean_object* v_declHint_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___redArg(v_ref_1601_, v_msg_1602_, v_declHint_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v_ref_1601_);
return v_res_1609_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__0));
v___x_1612_ = l_Lean_stringToMessageData(v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg(lean_object* v_ref_1613_, lean_object* v_constName_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1620_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___closed__1);
v___x_1621_ = 0;
lean_inc(v_constName_1614_);
v___x_1622_ = l_Lean_MessageData_ofConstName(v_constName_1614_, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1620_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___redArg(v_ref_1613_, v___x_1625_, v_constName_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1627_, lean_object* v_constName_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg(v_ref_1627_, v_constName_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v_ref_1627_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(lean_object* v_constName_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_ref_1641_; lean_object* v___x_1642_; 
v_ref_1641_ = lean_ctor_get(v___y_1638_, 5);
v___x_1642_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg(v_ref_1641_, v_constName_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg___boxed(lean_object* v_constName_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object* v_constName_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v_env_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = lean_st_ref_get(v___y_1654_);
v_env_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc_ref(v_env_1657_);
lean_dec(v___x_1656_);
v___x_1658_ = 0;
lean_inc(v_constName_1650_);
v___x_1659_ = l_Lean_Environment_find_x3f(v_env_1657_, v_constName_1650_, v___x_1658_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1660_;
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_constName_1650_);
v_val_1661_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_val_1661_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 0);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_val_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object* v_constName_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_constName_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object* v_cls_1676_, lean_object* v_msg_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_ref_1683_; lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1729_; 
v_ref_1683_ = lean_ctor_get(v___y_1680_, 5);
v___x_1684_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1729_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1729_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v_traceState_1690_; lean_object* v_env_1691_; lean_object* v_nextMacroScope_1692_; lean_object* v_ngen_1693_; lean_object* v_auxDeclNGen_1694_; lean_object* v_cache_1695_; lean_object* v_messages_1696_; lean_object* v_infoState_1697_; lean_object* v_snapshotTasks_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1728_; 
v___x_1689_ = lean_st_ref_take(v___y_1681_);
v_traceState_1690_ = lean_ctor_get(v___x_1689_, 4);
v_env_1691_ = lean_ctor_get(v___x_1689_, 0);
v_nextMacroScope_1692_ = lean_ctor_get(v___x_1689_, 1);
v_ngen_1693_ = lean_ctor_get(v___x_1689_, 2);
v_auxDeclNGen_1694_ = lean_ctor_get(v___x_1689_, 3);
v_cache_1695_ = lean_ctor_get(v___x_1689_, 5);
v_messages_1696_ = lean_ctor_get(v___x_1689_, 6);
v_infoState_1697_ = lean_ctor_get(v___x_1689_, 7);
v_snapshotTasks_1698_ = lean_ctor_get(v___x_1689_, 8);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1700_ = v___x_1689_;
v_isShared_1701_ = v_isSharedCheck_1728_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snapshotTasks_1698_);
lean_inc(v_infoState_1697_);
lean_inc(v_messages_1696_);
lean_inc(v_cache_1695_);
lean_inc(v_traceState_1690_);
lean_inc(v_auxDeclNGen_1694_);
lean_inc(v_ngen_1693_);
lean_inc(v_nextMacroScope_1692_);
lean_inc(v_env_1691_);
lean_dec(v___x_1689_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1728_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
uint64_t v_tid_1702_; lean_object* v_traces_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1727_; 
v_tid_1702_ = lean_ctor_get_uint64(v_traceState_1690_, sizeof(void*)*1);
v_traces_1703_ = lean_ctor_get(v_traceState_1690_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_traceState_1690_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1705_ = v_traceState_1690_;
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_traces_1703_);
lean_dec(v_traceState_1690_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; double v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
v___x_1709_ = 0;
v___x_1710_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_1711_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1711_, 0, v_cls_1676_);
lean_ctor_set(v___x_1711_, 1, v___x_1707_);
lean_ctor_set(v___x_1711_, 2, v___x_1710_);
lean_ctor_set_float(v___x_1711_, sizeof(void*)*3, v___x_1708_);
lean_ctor_set_float(v___x_1711_, sizeof(void*)*3 + 8, v___x_1708_);
lean_ctor_set_uint8(v___x_1711_, sizeof(void*)*3 + 16, v___x_1709_);
v___x_1712_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2));
v___x_1713_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v_a_1685_);
lean_ctor_set(v___x_1713_, 2, v___x_1712_);
lean_inc(v_ref_1683_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_ref_1683_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = l_Lean_PersistentArray_push___redArg(v_traces_1703_, v___x_1714_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1715_);
v___x_1717_ = v___x_1705_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1715_);
lean_ctor_set_uint64(v_reuseFailAlloc_1726_, sizeof(void*)*1, v_tid_1702_);
v___x_1717_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 4, v___x_1717_);
v___x_1719_ = v___x_1700_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_env_1691_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1692_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1693_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1694_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1725_, 5, v_cache_1695_);
lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_messages_1696_);
lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_infoState_1697_);
lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_snapshotTasks_1698_);
v___x_1719_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = lean_st_ref_set(v___y_1681_, v___x_1719_);
v___x_1721_ = lean_box(0);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1721_);
v___x_1723_ = v___x_1687_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object* v_cls_1730_, lean_object* v_msg_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1730_, v_msg_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(size_t v_sz_1738_, size_t v_i_1739_, lean_object* v_bs_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1739_, v_sz_1738_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_bs_1740_);
return v___x_1744_;
}
else
{
lean_object* v_v_1745_; lean_object* v___x_1746_; 
v_v_1745_ = lean_array_uget_borrowed(v_bs_1740_, v_i_1739_);
lean_inc(v_v_1745_);
v___x_1746_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_v_1745_, v___y_1741_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v_bs_x27_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v_bs_x27_1749_ = lean_array_uset(v_bs_1740_, v_i_1739_, v___x_1748_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1739_, v___x_1750_);
v___x_1752_ = lean_array_uset(v_bs_x27_1749_, v_i_1739_, v_a_1747_);
v_i_1739_ = v___x_1751_;
v_bs_1740_ = v___x_1752_;
goto _start;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_bs_1740_);
v_a_1754_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1746_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1746_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object* v_sz_1762_, lean_object* v_i_1763_, lean_object* v_bs_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1762_);
lean_dec(v_sz_1762_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_boxed_1767_, v_i_boxed_1768_, v_bs_1764_, v___y_1765_);
lean_dec(v___y_1765_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
if (lean_obj_tag(v_a_1770_) == 0)
{
lean_object* v___x_1772_; 
v___x_1772_ = l_List_reverse___redArg(v_a_1771_);
return v___x_1772_;
}
else
{
lean_object* v_head_1773_; lean_object* v_tail_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1783_; 
v_head_1773_ = lean_ctor_get(v_a_1770_, 0);
v_tail_1774_ = lean_ctor_get(v_a_1770_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_a_1770_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1776_ = v_a_1770_;
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_tail_1774_);
lean_inc(v_head_1773_);
lean_dec(v_a_1770_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = l_Lean_MessageData_ofExpr(v_head_1773_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 1, v_a_1771_);
lean_ctor_set(v___x_1776_, 0, v___x_1778_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_a_1771_);
v___x_1780_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
v_a_1770_ = v_tail_1774_;
v_a_1771_ = v___x_1780_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(lean_object* v_snd_1784_, lean_object* v_a_1785_, lean_object* v___x_1786_, lean_object* v_____r_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_fieldName_1793_; lean_object* v___x_1794_; 
v_fieldName_1793_ = lean_ctor_get(v_snd_1784_, 0);
lean_inc(v_fieldName_1793_);
lean_dec_ref(v_snd_1784_);
v___x_1794_ = l_Lean_Meta_mkProjection(v_a_1785_, v_fieldName_1793_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref(v___x_1794_);
v___x_1796_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1786_, v_a_1795_, v___y_1789_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1804_; 
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v___x_1796_, 0);
lean_dec(v_unused_1805_);
v___x_1798_ = v___x_1796_;
v_isShared_1799_ = v_isSharedCheck_1804_;
goto v_resetjp_1797_;
}
else
{
lean_dec(v___x_1796_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1804_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1800_ = lean_box(0);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1800_);
v___x_1802_ = v___x_1798_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1806_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1796_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1796_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v___x_1786_);
v_a_1814_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1794_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1794_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed(lean_object* v_snd_1822_, lean_object* v_a_1823_, lean_object* v___x_1824_, lean_object* v_____r_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v_snd_1822_, v_a_1823_, v___x_1824_, v_____r_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__0));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__2));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__4));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__6));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(lean_object* v_val_1844_, lean_object* v_fst_1845_, lean_object* v_expectedType_1846_, lean_object* v___f_1847_, lean_object* v___f_1848_, lean_object* v___x_1849_, lean_object* v_cls_1850_, lean_object* v_snd_1851_, lean_object* v___x_1852_, lean_object* v_____r_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___y_1860_; uint8_t v___y_1861_; lean_object* v_a_1894_; lean_object* v___y_1898_; lean_object* v___x_1911_; 
lean_inc(v_fst_1845_);
v___x_1911_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_val_1844_, v_fst_1845_, v_expectedType_1846_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
if (lean_obj_tag(v_a_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_val_1913_ = lean_ctor_get(v_a_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v_a_1912_);
v___x_1914_ = lean_box(0);
v___x_1915_ = l_Lean_Meta_trySynthInstance(v_val_1913_, v___x_1914_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
if (lean_obj_tag(v_a_1916_) == 1)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v_a_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_inc_ref(v___f_1847_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1918_ = lean_apply_5(v___f_1847_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; uint8_t v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = lean_unbox(v_a_1919_);
lean_dec(v_a_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
v___x_1921_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v_snd_1851_, v_a_1917_, v___x_1852_, v___x_1849_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
v___y_1898_ = v___x_1921_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1922_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5);
lean_inc(v_a_1917_);
v___x_1923_ = l_Lean_MessageData_ofExpr(v_a_1917_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
lean_inc(v_cls_1850_);
v___x_1927_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1850_, v___x_1926_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v_snd_1851_, v_a_1917_, v___x_1852_, v_a_1928_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
v___y_1898_ = v___x_1929_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_1930_; 
lean_dec(v_a_1917_);
lean_dec(v___x_1852_);
lean_dec_ref(v_snd_1851_);
v_a_1930_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1927_);
v_a_1894_ = v_a_1930_;
goto v___jp_1893_;
}
}
}
else
{
lean_object* v_a_1931_; 
lean_dec(v_a_1917_);
lean_dec(v___x_1852_);
lean_dec_ref(v_snd_1851_);
v_a_1931_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1918_);
v_a_1894_ = v_a_1931_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_options_1932_; uint8_t v_hasTrace_1933_; 
lean_dec(v_a_1916_);
lean_dec(v___x_1852_);
lean_dec_ref(v_snd_1851_);
v_options_1932_ = lean_ctor_get(v___y_1856_, 2);
v_hasTrace_1933_ = lean_ctor_get_uint8(v_options_1932_, sizeof(void*)*1);
if (v_hasTrace_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1847_);
lean_dec(v_fst_1845_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1934_ = lean_apply_6(v___f_1848_, v___x_1849_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1934_;
}
else
{
lean_object* v_inheritedTraceOptions_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v_inheritedTraceOptions_1935_ = lean_ctor_get(v___y_1856_, 13);
v___x_1936_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1));
lean_inc(v_cls_1850_);
v___x_1937_ = l_Lean_Name_append(v___x_1936_, v_cls_1850_);
v___x_1938_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1935_, v_options_1932_, v___x_1937_);
lean_dec(v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1847_);
lean_dec(v_fst_1845_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1939_ = lean_apply_6(v___f_1848_, v___x_1849_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1939_;
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1940_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7);
lean_inc(v_fst_1845_);
v___x_1941_ = l_Lean_MessageData_ofName(v_fst_1845_);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
lean_inc(v_cls_1850_);
v___x_1945_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1850_, v___x_1944_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1947_; 
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1847_);
lean_dec(v_fst_1845_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1947_ = lean_apply_6(v___f_1848_, v_a_1946_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1947_;
}
else
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1945_);
v_a_1894_ = v_a_1948_;
goto v___jp_1893_;
}
}
}
}
}
else
{
lean_object* v_a_1949_; 
lean_dec(v___x_1852_);
lean_dec_ref(v_snd_1851_);
v_a_1949_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1915_);
v_a_1894_ = v_a_1949_;
goto v___jp_1893_;
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v_a_1912_);
lean_dec(v___x_1852_);
lean_dec_ref(v_snd_1851_);
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1847_);
lean_dec(v_fst_1845_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1950_ = lean_apply_6(v___f_1848_, v___x_1849_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1950_;
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v___x_1852_);
lean_dec_ref(v_snd_1851_);
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1848_);
lean_dec_ref(v___f_1847_);
lean_dec(v_fst_1845_);
v_a_1951_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1911_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1911_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
v___jp_1859_:
{
if (v___y_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1862_ = lean_apply_5(v___f_1847_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; uint8_t v___x_1864_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref(v___x_1862_);
v___x_1864_ = lean_unbox(v_a_1863_);
lean_dec(v_a_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_dec_ref(v___y_1860_);
lean_dec(v_cls_1850_);
lean_dec(v_fst_1845_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1865_ = lean_apply_6(v___f_1848_, v___x_1849_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1866_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1);
v___x_1867_ = l_Lean_MessageData_ofName(v_fst_1845_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_Exception_toMessageData(v___y_1860_);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1850_, v___x_1872_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1873_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1875_ = lean_apply_6(v___f_1848_, v_a_1874_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1875_;
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v___f_1848_);
v_a_1876_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1873_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1873_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v___y_1860_);
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1848_);
lean_dec(v_fst_1845_);
v_a_1884_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1862_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1862_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v___x_1892_; 
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1848_);
lean_dec_ref(v___f_1847_);
lean_dec(v_fst_1845_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___y_1860_);
return v___x_1892_;
}
}
v___jp_1893_:
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Lean_Exception_isInterrupt(v_a_1894_);
if (v___x_1895_ == 0)
{
uint8_t v___x_1896_; 
lean_inc_ref(v_a_1894_);
v___x_1896_ = l_Lean_Exception_isRuntime(v_a_1894_);
v___y_1860_ = v_a_1894_;
v___y_1861_ = v___x_1896_;
goto v___jp_1859_;
}
else
{
v___y_1860_ = v_a_1894_;
v___y_1861_ = v___x_1895_;
goto v___jp_1859_;
}
}
v___jp_1897_:
{
if (lean_obj_tag(v___y_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_cls_1850_);
lean_dec_ref(v___f_1847_);
lean_dec(v_fst_1845_);
v_a_1899_ = lean_ctor_get(v___y_1898_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1898_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1901_ = v___y_1898_;
v_isShared_1902_ = v_isSharedCheck_1909_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___y_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1909_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
if (lean_obj_tag(v_a_1899_) == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
lean_dec_ref(v___f_1848_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1849_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
lean_del_object(v___x_1901_);
v_a_1907_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v_a_1899_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
v___x_1908_ = lean_apply_6(v___f_1848_, v_a_1907_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1908_;
}
}
}
else
{
lean_object* v_a_1910_; 
v_a_1910_ = lean_ctor_get(v___y_1898_, 0);
lean_inc(v_a_1910_);
lean_dec_ref(v___y_1898_);
v_a_1894_ = v_a_1910_;
goto v___jp_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___boxed(lean_object* v_val_1959_, lean_object* v_fst_1960_, lean_object* v_expectedType_1961_, lean_object* v___f_1962_, lean_object* v___f_1963_, lean_object* v___x_1964_, lean_object* v_cls_1965_, lean_object* v_snd_1966_, lean_object* v___x_1967_, lean_object* v_____r_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(v_val_1959_, v_fst_1960_, v_expectedType_1961_, v___f_1962_, v___f_1963_, v___x_1964_, v_cls_1965_, v_snd_1966_, v___x_1967_, v_____r_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(lean_object* v___x_1978_, lean_object* v___x_1979_, lean_object* v___x_1980_, lean_object* v_a_1981_, uint8_t v___x_1982_, uint8_t v___x_1983_, uint8_t v_compile_1984_, uint8_t v_logCompileErrors_1985_, uint8_t v_isMeta_1986_, lean_object* v_____r_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_options_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_options_1993_ = lean_ctor_get(v___y_1990_, 2);
v___x_1994_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1995_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec_ref(v_a_1981_);
v___x_1996_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1978_, v___x_1979_, v___y_1989_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1996_, 0);
lean_dec(v_unused_2005_);
v___x_1998_ = v___x_1996_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v___x_1996_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1980_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v_a_2006_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1996_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1996_);
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
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc_ref(v___x_1979_);
v___x_2014_ = lean_infer_type(v___x_1979_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
lean_inc_ref(v_a_1981_);
v___x_2016_ = l_Lean_Meta_isExprDefEq(v_a_1981_, v_a_2015_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; uint8_t v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = lean_unbox(v_a_2017_);
lean_dec(v_a_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_2020_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2019_, v___y_1991_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___x_2058_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_n(v_a_2021_, 2);
lean_dec_ref(v___x_2020_);
v___x_2058_ = l_Lean_Meta_mkAuxDefinition(v_a_2021_, v_a_1981_, v___x_1979_, v___x_1982_, v___x_1982_, v___x_1983_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2058_);
v___x_2060_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1978_, v_a_2059_, v___y_1989_);
if (lean_obj_tag(v___x_2060_) == 0)
{
uint8_t v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v___x_2060_);
v___x_2061_ = 0;
lean_inc(v_a_2021_);
v___x_2062_ = l_Lean_Meta_setInlineAttribute(v_a_2021_, v___x_2061_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_dec_ref(v___x_2062_);
if (v_isMeta_1986_ == 0)
{
v___y_2044_ = v___y_1990_;
v___y_2045_ = v___y_1991_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2063_; lean_object* v_env_2064_; lean_object* v_nextMacroScope_2065_; lean_object* v_ngen_2066_; lean_object* v_auxDeclNGen_2067_; lean_object* v_traceState_2068_; lean_object* v_messages_2069_; lean_object* v_infoState_2070_; lean_object* v_snapshotTasks_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2096_; 
v___x_2063_ = lean_st_ref_take(v___y_1991_);
v_env_2064_ = lean_ctor_get(v___x_2063_, 0);
v_nextMacroScope_2065_ = lean_ctor_get(v___x_2063_, 1);
v_ngen_2066_ = lean_ctor_get(v___x_2063_, 2);
v_auxDeclNGen_2067_ = lean_ctor_get(v___x_2063_, 3);
v_traceState_2068_ = lean_ctor_get(v___x_2063_, 4);
v_messages_2069_ = lean_ctor_get(v___x_2063_, 6);
v_infoState_2070_ = lean_ctor_get(v___x_2063_, 7);
v_snapshotTasks_2071_ = lean_ctor_get(v___x_2063_, 8);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v___x_2063_, 5);
lean_dec(v_unused_2097_);
v___x_2073_ = v___x_2063_;
v_isShared_2074_ = v_isSharedCheck_2096_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snapshotTasks_2071_);
lean_inc(v_infoState_2070_);
lean_inc(v_messages_2069_);
lean_inc(v_traceState_2068_);
lean_inc(v_auxDeclNGen_2067_);
lean_inc(v_ngen_2066_);
lean_inc(v_nextMacroScope_2065_);
lean_inc(v_env_2064_);
lean_dec(v___x_2063_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2096_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_inc(v_a_2021_);
v___x_2075_ = l_Lean_markMeta(v_env_2064_, v_a_2021_);
v___x_2076_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 5, v___x_2076_);
lean_ctor_set(v___x_2073_, 0, v___x_2075_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_nextMacroScope_2065_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_ngen_2066_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_auxDeclNGen_2067_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_traceState_2068_);
lean_ctor_set(v_reuseFailAlloc_2095_, 5, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2095_, 6, v_messages_2069_);
lean_ctor_set(v_reuseFailAlloc_2095_, 7, v_infoState_2070_);
lean_ctor_set(v_reuseFailAlloc_2095_, 8, v_snapshotTasks_2071_);
v___x_2078_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_mctx_2081_; lean_object* v_zetaDeltaFVarIds_2082_; lean_object* v_postponed_2083_; lean_object* v_diag_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2093_; 
v___x_2079_ = lean_st_ref_set(v___y_1991_, v___x_2078_);
v___x_2080_ = lean_st_ref_take(v___y_1989_);
v_mctx_2081_ = lean_ctor_get(v___x_2080_, 0);
v_zetaDeltaFVarIds_2082_ = lean_ctor_get(v___x_2080_, 2);
v_postponed_2083_ = lean_ctor_get(v___x_2080_, 3);
v_diag_2084_ = lean_ctor_get(v___x_2080_, 4);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v___x_2080_, 1);
lean_dec(v_unused_2094_);
v___x_2086_ = v___x_2080_;
v_isShared_2087_ = v_isSharedCheck_2093_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_diag_2084_);
lean_inc(v_postponed_2083_);
lean_inc(v_zetaDeltaFVarIds_2082_);
lean_inc(v_mctx_2081_);
lean_dec(v___x_2080_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2093_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v___x_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_mctx_2081_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_zetaDeltaFVarIds_2082_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_postponed_2083_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_diag_2084_);
v___x_2090_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_st_ref_set(v___y_1989_, v___x_2090_);
v___y_2044_ = v___y_1990_;
v___y_2045_ = v___y_1991_;
goto v___jp_2043_;
}
}
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_a_2021_);
v_a_2098_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2062_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2062_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_a_2021_);
v_a_2106_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2060_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2060_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_a_2021_);
lean_dec(v___x_1978_);
v_a_2114_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2058_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2058_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
v___jp_2022_:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_enableRealizationsForConst(v_a_2021_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2033_; 
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v___x_2025_, 0);
lean_dec(v_unused_2034_);
v___x_2027_ = v___x_2025_;
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v___x_2025_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_1980_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2029_);
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2025_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2025_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
v___jp_2043_:
{
if (v_compile_1984_ == 0)
{
v___y_2023_ = v___y_2044_;
v___y_2024_ = v___y_2045_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_mk_empty_array_with_capacity(v___x_2046_);
lean_inc(v_a_2021_);
v___x_2048_ = lean_array_push(v___x_2047_, v_a_2021_);
v___x_2049_ = l_Lean_compileDecls(v___x_2048_, v_logCompileErrors_1985_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_dec_ref(v___x_2049_);
v___y_2023_ = v___y_2044_;
v___y_2024_ = v___y_2045_;
goto v___jp_2022_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_a_2021_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_a_1981_);
lean_dec_ref(v___x_1979_);
lean_dec(v___x_1978_);
v_a_2122_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2020_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2020_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v___x_2130_; 
lean_dec_ref(v_a_1981_);
v___x_2130_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1978_, v___x_1979_, v___y_1989_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2138_; 
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; 
v_unused_2139_ = lean_ctor_get(v___x_2130_, 0);
lean_dec(v_unused_2139_);
v___x_2132_ = v___x_2130_;
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v___x_2130_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_1980_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2130_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2130_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_a_1981_);
lean_dec_ref(v___x_1979_);
lean_dec(v___x_1978_);
v_a_2148_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2016_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2016_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v_a_1981_);
lean_dec_ref(v___x_1979_);
lean_dec(v___x_1978_);
v_a_2156_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2014_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2014_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed(lean_object* v___x_2164_, lean_object* v___x_2165_, lean_object* v___x_2166_, lean_object* v_a_2167_, lean_object* v___x_2168_, lean_object* v___x_2169_, lean_object* v_compile_2170_, lean_object* v_logCompileErrors_2171_, lean_object* v_isMeta_2172_, lean_object* v_____r_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v___x_157495__boxed_2179_; uint8_t v___x_157496__boxed_2180_; uint8_t v_compile_boxed_2181_; uint8_t v_logCompileErrors_boxed_2182_; uint8_t v_isMeta_boxed_2183_; lean_object* v_res_2184_; 
v___x_157495__boxed_2179_ = lean_unbox(v___x_2168_);
v___x_157496__boxed_2180_ = lean_unbox(v___x_2169_);
v_compile_boxed_2181_ = lean_unbox(v_compile_2170_);
v_logCompileErrors_boxed_2182_ = lean_unbox(v_logCompileErrors_2171_);
v_isMeta_boxed_2183_ = lean_unbox(v_isMeta_2172_);
v_res_2184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2164_, v___x_2165_, v___x_2166_, v_a_2167_, v___x_157495__boxed_2179_, v___x_157496__boxed_2180_, v_compile_boxed_2181_, v_logCompileErrors_boxed_2182_, v_isMeta_boxed_2183_, v_____r_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(lean_object* v___x_2185_, lean_object* v_a_2186_, lean_object* v_____r_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2185_, v_a_2186_, v___y_2189_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2201_; 
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; 
v_unused_2202_ = lean_ctor_get(v___x_2193_, 0);
lean_dec(v_unused_2202_);
v___x_2195_ = v___x_2193_;
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
else
{
lean_dec(v___x_2193_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_box(0);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2197_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_a_2203_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2193_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2193_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5___boxed(lean_object* v___x_2211_, lean_object* v_a_2212_, lean_object* v_____r_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_2211_, v_a_2212_, v_____r_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1(lean_object* v___x_2220_, lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v_a_2223_, uint8_t v___x_2224_, uint8_t v_compile_2225_, uint8_t v_logCompileErrors_2226_, uint8_t v_isMeta_2227_, lean_object* v_____r_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_options_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v_options_2234_ = lean_ctor_get(v___y_2231_, 2);
v___x_2235_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2236_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2234_, v___x_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; 
lean_dec_ref(v_a_2223_);
v___x_2237_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2220_, v___x_2221_, v___y_2230_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2245_; 
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v___x_2237_, 0);
lean_dec(v_unused_2246_);
v___x_2239_ = v___x_2237_;
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v___x_2237_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2222_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2237_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
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
else
{
lean_object* v___x_2255_; 
lean_inc(v___y_2232_);
lean_inc_ref(v___y_2231_);
lean_inc(v___y_2230_);
lean_inc_ref(v___y_2229_);
lean_inc_ref(v___x_2221_);
v___x_2255_ = lean_infer_type(v___x_2221_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___x_2255_);
lean_inc_ref(v_a_2223_);
v___x_2257_ = l_Lean_Meta_isExprDefEq(v_a_2223_, v_a_2256_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; uint8_t v___x_2259_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = lean_unbox(v_a_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_2261_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2260_, v___y_2232_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2285_; lean_object* v___y_2286_; uint8_t v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_n(v_a_2262_, 2);
lean_dec_ref(v___x_2261_);
v___x_2299_ = lean_unbox(v_a_2258_);
v___x_2300_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
v___x_2301_ = l_Lean_Meta_mkAuxDefinition(v_a_2262_, v_a_2223_, v___x_2221_, v___x_2299_, v___x_2300_, v___x_2224_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2220_, v_a_2302_, v___y_2230_);
if (lean_obj_tag(v___x_2303_) == 0)
{
uint8_t v___x_2304_; lean_object* v___x_2305_; 
lean_dec_ref(v___x_2303_);
v___x_2304_ = 0;
lean_inc(v_a_2262_);
v___x_2305_ = l_Lean_Meta_setInlineAttribute(v_a_2262_, v___x_2304_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_dec_ref(v___x_2305_);
if (v_isMeta_2227_ == 0)
{
v___y_2285_ = v___y_2231_;
v___y_2286_ = v___y_2232_;
goto v___jp_2284_;
}
else
{
lean_object* v___x_2306_; lean_object* v_env_2307_; lean_object* v_nextMacroScope_2308_; lean_object* v_ngen_2309_; lean_object* v_auxDeclNGen_2310_; lean_object* v_traceState_2311_; lean_object* v_messages_2312_; lean_object* v_infoState_2313_; lean_object* v_snapshotTasks_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2339_; 
v___x_2306_ = lean_st_ref_take(v___y_2232_);
v_env_2307_ = lean_ctor_get(v___x_2306_, 0);
v_nextMacroScope_2308_ = lean_ctor_get(v___x_2306_, 1);
v_ngen_2309_ = lean_ctor_get(v___x_2306_, 2);
v_auxDeclNGen_2310_ = lean_ctor_get(v___x_2306_, 3);
v_traceState_2311_ = lean_ctor_get(v___x_2306_, 4);
v_messages_2312_ = lean_ctor_get(v___x_2306_, 6);
v_infoState_2313_ = lean_ctor_get(v___x_2306_, 7);
v_snapshotTasks_2314_ = lean_ctor_get(v___x_2306_, 8);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v___x_2306_, 5);
lean_dec(v_unused_2340_);
v___x_2316_ = v___x_2306_;
v_isShared_2317_ = v_isSharedCheck_2339_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snapshotTasks_2314_);
lean_inc(v_infoState_2313_);
lean_inc(v_messages_2312_);
lean_inc(v_traceState_2311_);
lean_inc(v_auxDeclNGen_2310_);
lean_inc(v_ngen_2309_);
lean_inc(v_nextMacroScope_2308_);
lean_inc(v_env_2307_);
lean_dec(v___x_2306_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2339_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
lean_inc(v_a_2262_);
v___x_2318_ = l_Lean_markMeta(v_env_2307_, v_a_2262_);
v___x_2319_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 5, v___x_2319_);
lean_ctor_set(v___x_2316_, 0, v___x_2318_);
v___x_2321_ = v___x_2316_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_nextMacroScope_2308_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_ngen_2309_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_auxDeclNGen_2310_);
lean_ctor_set(v_reuseFailAlloc_2338_, 4, v_traceState_2311_);
lean_ctor_set(v_reuseFailAlloc_2338_, 5, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2338_, 6, v_messages_2312_);
lean_ctor_set(v_reuseFailAlloc_2338_, 7, v_infoState_2313_);
lean_ctor_set(v_reuseFailAlloc_2338_, 8, v_snapshotTasks_2314_);
v___x_2321_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_mctx_2324_; lean_object* v_zetaDeltaFVarIds_2325_; lean_object* v_postponed_2326_; lean_object* v_diag_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2336_; 
v___x_2322_ = lean_st_ref_set(v___y_2232_, v___x_2321_);
v___x_2323_ = lean_st_ref_take(v___y_2230_);
v_mctx_2324_ = lean_ctor_get(v___x_2323_, 0);
v_zetaDeltaFVarIds_2325_ = lean_ctor_get(v___x_2323_, 2);
v_postponed_2326_ = lean_ctor_get(v___x_2323_, 3);
v_diag_2327_ = lean_ctor_get(v___x_2323_, 4);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v___x_2323_, 1);
lean_dec(v_unused_2337_);
v___x_2329_ = v___x_2323_;
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_diag_2327_);
lean_inc(v_postponed_2326_);
lean_inc(v_zetaDeltaFVarIds_2325_);
lean_inc(v_mctx_2324_);
lean_dec(v___x_2323_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 1, v___x_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_mctx_2324_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_zetaDeltaFVarIds_2325_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_postponed_2326_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_diag_2327_);
v___x_2333_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_st_ref_set(v___y_2230_, v___x_2333_);
v___y_2285_ = v___y_2231_;
v___y_2286_ = v___y_2232_;
goto v___jp_2284_;
}
}
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2262_);
v_a_2341_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2305_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2305_);
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
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2262_);
v_a_2349_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2303_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2303_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2262_);
lean_dec(v___x_2220_);
v_a_2357_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2301_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2301_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
v___jp_2263_:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_enableRealizationsForConst(v_a_2262_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2274_; 
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2274_ == 0)
{
lean_object* v_unused_2275_; 
v_unused_2275_ = lean_ctor_get(v___x_2266_, 0);
lean_dec(v_unused_2275_);
v___x_2268_ = v___x_2266_;
v_isShared_2269_ = v_isSharedCheck_2274_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v___x_2266_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2274_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2222_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2270_);
v___x_2272_ = v___x_2268_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_a_2276_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2266_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2266_);
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
v___jp_2284_:
{
if (v_compile_2225_ == 0)
{
v___y_2264_ = v___y_2285_;
v___y_2265_ = v___y_2286_;
goto v___jp_2263_;
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_mk_empty_array_with_capacity(v___x_2287_);
lean_inc(v_a_2262_);
v___x_2289_ = lean_array_push(v___x_2288_, v_a_2262_);
v___x_2290_ = l_Lean_compileDecls(v___x_2289_, v_logCompileErrors_2226_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_dec_ref(v___x_2290_);
v___y_2264_ = v___y_2285_;
v___y_2265_ = v___y_2286_;
goto v___jp_2263_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2262_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v___x_2220_);
v_a_2365_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2261_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2261_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v___x_2373_; 
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2223_);
v___x_2373_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2220_, v___x_2221_, v___y_2230_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2381_; 
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v___x_2373_, 0);
lean_dec(v_unused_2382_);
v___x_2375_ = v___x_2373_;
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
else
{
lean_dec(v___x_2373_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2222_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_a_2383_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2373_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2373_);
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
lean_dec_ref(v_a_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v___x_2220_);
v_a_2391_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2257_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2257_);
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
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v_a_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v___x_2220_);
v_a_2399_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2255_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2255_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1___boxed(lean_object* v___x_2407_, lean_object* v___x_2408_, lean_object* v___x_2409_, lean_object* v_a_2410_, lean_object* v___x_2411_, lean_object* v_compile_2412_, lean_object* v_logCompileErrors_2413_, lean_object* v_isMeta_2414_, lean_object* v_____r_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v___x_157932__boxed_2421_; uint8_t v_compile_boxed_2422_; uint8_t v_logCompileErrors_boxed_2423_; uint8_t v_isMeta_boxed_2424_; lean_object* v_res_2425_; 
v___x_157932__boxed_2421_ = lean_unbox(v___x_2411_);
v_compile_boxed_2422_ = lean_unbox(v_compile_2412_);
v_logCompileErrors_boxed_2423_ = lean_unbox(v_logCompileErrors_2413_);
v_isMeta_boxed_2424_ = lean_unbox(v_isMeta_2414_);
v_res_2425_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1(v___x_2407_, v___x_2408_, v___x_2409_, v_a_2410_, v___x_157932__boxed_2421_, v_compile_boxed_2422_, v_logCompileErrors_boxed_2423_, v_isMeta_boxed_2424_, v_____r_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6(lean_object* v___x_2426_, lean_object* v_____r_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2426_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6___boxed(lean_object* v___x_2435_, lean_object* v_____r_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6(v___x_2435_, v_____r_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(lean_object* v_cls_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_options_2449_; uint8_t v_hasTrace_2450_; 
v_options_2449_ = lean_ctor_get(v___y_2446_, 2);
v_hasTrace_2450_ = lean_ctor_get_uint8(v_options_2449_, sizeof(void*)*1);
if (v_hasTrace_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_dec(v_cls_2443_);
v___x_2451_ = lean_box(v_hasTrace_2450_);
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
else
{
lean_object* v_inheritedTraceOptions_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_inheritedTraceOptions_2453_ = lean_ctor_get(v___y_2446_, 13);
v___x_2454_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1));
v___x_2455_ = l_Lean_Name_append(v___x_2454_, v_cls_2443_);
v___x_2456_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2453_, v_options_2449_, v___x_2455_);
lean_dec(v___x_2455_);
v___x_2457_ = lean_box(v___x_2456_);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0___boxed(lean_object* v_cls_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(lean_object* v_a_2466_, lean_object* v___x_2467_, uint8_t v___x_2468_, lean_object* v___x_2469_, lean_object* v___f_2470_, lean_object* v_____r_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_box(0);
v___x_2478_ = l_Lean_Meta_mkAuxTheorem(v_a_2466_, v___x_2467_, v___x_2468_, v___x_2477_, v___x_2468_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2469_, v_a_2479_, v___y_2473_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2482_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref(v___x_2480_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc(v___y_2473_);
lean_inc_ref(v___y_2472_);
v___x_2482_ = lean_apply_6(v___f_2470_, v_a_2481_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, lean_box(0));
return v___x_2482_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v___f_2470_);
v_a_2483_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2480_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2480_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v___f_2470_);
lean_dec(v___x_2469_);
v_a_2491_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2478_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2478_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7___boxed(lean_object* v_a_2499_, lean_object* v___x_2500_, lean_object* v___x_2501_, lean_object* v___x_2502_, lean_object* v___f_2503_, lean_object* v_____r_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
uint8_t v___x_158352__boxed_2510_; lean_object* v_res_2511_; 
v___x_158352__boxed_2510_ = lean_unbox(v___x_2501_);
v_res_2511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_2499_, v___x_2500_, v___x_158352__boxed_2510_, v___x_2502_, v___f_2503_, v_____r_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13_spec__15(size_t v_sz_2512_, size_t v_i_2513_, lean_object* v_bs_2514_){
_start:
{
uint8_t v___x_2515_; 
v___x_2515_ = lean_usize_dec_lt(v_i_2513_, v_sz_2512_);
if (v___x_2515_ == 0)
{
return v_bs_2514_;
}
else
{
lean_object* v_v_2516_; lean_object* v_msg_2517_; lean_object* v___x_2518_; lean_object* v_bs_x27_2519_; size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v_v_2516_ = lean_array_uget_borrowed(v_bs_2514_, v_i_2513_);
v_msg_2517_ = lean_ctor_get(v_v_2516_, 1);
lean_inc_ref(v_msg_2517_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v_bs_x27_2519_ = lean_array_uset(v_bs_2514_, v_i_2513_, v___x_2518_);
v___x_2520_ = ((size_t)1ULL);
v___x_2521_ = lean_usize_add(v_i_2513_, v___x_2520_);
v___x_2522_ = lean_array_uset(v_bs_x27_2519_, v_i_2513_, v_msg_2517_);
v_i_2513_ = v___x_2521_;
v_bs_2514_ = v___x_2522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13_spec__15___boxed(lean_object* v_sz_2524_, lean_object* v_i_2525_, lean_object* v_bs_2526_){
_start:
{
size_t v_sz_boxed_2527_; size_t v_i_boxed_2528_; lean_object* v_res_2529_; 
v_sz_boxed_2527_ = lean_unbox_usize(v_sz_2524_);
lean_dec(v_sz_2524_);
v_i_boxed_2528_ = lean_unbox_usize(v_i_2525_);
lean_dec(v_i_2525_);
v_res_2529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13_spec__15(v_sz_boxed_2527_, v_i_boxed_2528_, v_bs_2526_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13(lean_object* v_oldTraces_2530_, lean_object* v_data_2531_, lean_object* v_ref_2532_, lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_fileName_2539_; lean_object* v_fileMap_2540_; lean_object* v_options_2541_; lean_object* v_currRecDepth_2542_; lean_object* v_maxRecDepth_2543_; lean_object* v_ref_2544_; lean_object* v_currNamespace_2545_; lean_object* v_openDecls_2546_; lean_object* v_initHeartbeats_2547_; lean_object* v_maxHeartbeats_2548_; lean_object* v_quotContext_2549_; lean_object* v_currMacroScope_2550_; uint8_t v_diag_2551_; lean_object* v_cancelTk_x3f_2552_; uint8_t v_suppressElabErrors_2553_; lean_object* v_inheritedTraceOptions_2554_; lean_object* v___x_2555_; lean_object* v_traceState_2556_; lean_object* v_traces_2557_; lean_object* v_ref_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; size_t v_sz_2561_; size_t v___x_2562_; lean_object* v___x_2563_; lean_object* v_msg_2564_; lean_object* v___x_2565_; lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2603_; 
v_fileName_2539_ = lean_ctor_get(v___y_2536_, 0);
v_fileMap_2540_ = lean_ctor_get(v___y_2536_, 1);
v_options_2541_ = lean_ctor_get(v___y_2536_, 2);
v_currRecDepth_2542_ = lean_ctor_get(v___y_2536_, 3);
v_maxRecDepth_2543_ = lean_ctor_get(v___y_2536_, 4);
v_ref_2544_ = lean_ctor_get(v___y_2536_, 5);
v_currNamespace_2545_ = lean_ctor_get(v___y_2536_, 6);
v_openDecls_2546_ = lean_ctor_get(v___y_2536_, 7);
v_initHeartbeats_2547_ = lean_ctor_get(v___y_2536_, 8);
v_maxHeartbeats_2548_ = lean_ctor_get(v___y_2536_, 9);
v_quotContext_2549_ = lean_ctor_get(v___y_2536_, 10);
v_currMacroScope_2550_ = lean_ctor_get(v___y_2536_, 11);
v_diag_2551_ = lean_ctor_get_uint8(v___y_2536_, sizeof(void*)*14);
v_cancelTk_x3f_2552_ = lean_ctor_get(v___y_2536_, 12);
v_suppressElabErrors_2553_ = lean_ctor_get_uint8(v___y_2536_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2554_ = lean_ctor_get(v___y_2536_, 13);
v___x_2555_ = lean_st_ref_get(v___y_2537_);
v_traceState_2556_ = lean_ctor_get(v___x_2555_, 4);
lean_inc_ref(v_traceState_2556_);
lean_dec(v___x_2555_);
v_traces_2557_ = lean_ctor_get(v_traceState_2556_, 0);
lean_inc_ref(v_traces_2557_);
lean_dec_ref(v_traceState_2556_);
v_ref_2558_ = l_Lean_replaceRef(v_ref_2532_, v_ref_2544_);
lean_inc_ref(v_inheritedTraceOptions_2554_);
lean_inc(v_cancelTk_x3f_2552_);
lean_inc(v_currMacroScope_2550_);
lean_inc(v_quotContext_2549_);
lean_inc(v_maxHeartbeats_2548_);
lean_inc(v_initHeartbeats_2547_);
lean_inc(v_openDecls_2546_);
lean_inc(v_currNamespace_2545_);
lean_inc(v_maxRecDepth_2543_);
lean_inc(v_currRecDepth_2542_);
lean_inc_ref(v_options_2541_);
lean_inc_ref(v_fileMap_2540_);
lean_inc_ref(v_fileName_2539_);
v___x_2559_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2559_, 0, v_fileName_2539_);
lean_ctor_set(v___x_2559_, 1, v_fileMap_2540_);
lean_ctor_set(v___x_2559_, 2, v_options_2541_);
lean_ctor_set(v___x_2559_, 3, v_currRecDepth_2542_);
lean_ctor_set(v___x_2559_, 4, v_maxRecDepth_2543_);
lean_ctor_set(v___x_2559_, 5, v_ref_2558_);
lean_ctor_set(v___x_2559_, 6, v_currNamespace_2545_);
lean_ctor_set(v___x_2559_, 7, v_openDecls_2546_);
lean_ctor_set(v___x_2559_, 8, v_initHeartbeats_2547_);
lean_ctor_set(v___x_2559_, 9, v_maxHeartbeats_2548_);
lean_ctor_set(v___x_2559_, 10, v_quotContext_2549_);
lean_ctor_set(v___x_2559_, 11, v_currMacroScope_2550_);
lean_ctor_set(v___x_2559_, 12, v_cancelTk_x3f_2552_);
lean_ctor_set(v___x_2559_, 13, v_inheritedTraceOptions_2554_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*14, v_diag_2551_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*14 + 1, v_suppressElabErrors_2553_);
v___x_2560_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2557_);
lean_dec_ref(v_traces_2557_);
v_sz_2561_ = lean_array_size(v___x_2560_);
v___x_2562_ = ((size_t)0ULL);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13_spec__15(v_sz_2561_, v___x_2562_, v___x_2560_);
v_msg_2564_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2564_, 0, v_data_2531_);
lean_ctor_set(v_msg_2564_, 1, v_msg_2533_);
lean_ctor_set(v_msg_2564_, 2, v___x_2563_);
v___x_2565_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_2564_, v___y_2534_, v___y_2535_, v___x_2559_, v___y_2537_);
lean_dec_ref(v___x_2559_);
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2603_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2603_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v_traceState_2571_; lean_object* v_env_2572_; lean_object* v_nextMacroScope_2573_; lean_object* v_ngen_2574_; lean_object* v_auxDeclNGen_2575_; lean_object* v_cache_2576_; lean_object* v_messages_2577_; lean_object* v_infoState_2578_; lean_object* v_snapshotTasks_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2602_; 
v___x_2570_ = lean_st_ref_take(v___y_2537_);
v_traceState_2571_ = lean_ctor_get(v___x_2570_, 4);
v_env_2572_ = lean_ctor_get(v___x_2570_, 0);
v_nextMacroScope_2573_ = lean_ctor_get(v___x_2570_, 1);
v_ngen_2574_ = lean_ctor_get(v___x_2570_, 2);
v_auxDeclNGen_2575_ = lean_ctor_get(v___x_2570_, 3);
v_cache_2576_ = lean_ctor_get(v___x_2570_, 5);
v_messages_2577_ = lean_ctor_get(v___x_2570_, 6);
v_infoState_2578_ = lean_ctor_get(v___x_2570_, 7);
v_snapshotTasks_2579_ = lean_ctor_get(v___x_2570_, 8);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2581_ = v___x_2570_;
v_isShared_2582_ = v_isSharedCheck_2602_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_snapshotTasks_2579_);
lean_inc(v_infoState_2578_);
lean_inc(v_messages_2577_);
lean_inc(v_cache_2576_);
lean_inc(v_traceState_2571_);
lean_inc(v_auxDeclNGen_2575_);
lean_inc(v_ngen_2574_);
lean_inc(v_nextMacroScope_2573_);
lean_inc(v_env_2572_);
lean_dec(v___x_2570_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2602_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
uint64_t v_tid_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2600_; 
v_tid_2583_ = lean_ctor_get_uint64(v_traceState_2571_, sizeof(void*)*1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_traceState_2571_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v_traceState_2571_, 0);
lean_dec(v_unused_2601_);
v___x_2585_ = v_traceState_2571_;
v_isShared_2586_ = v_isSharedCheck_2600_;
goto v_resetjp_2584_;
}
else
{
lean_dec(v_traceState_2571_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2600_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_ref_2532_);
lean_ctor_set(v___x_2587_, 1, v_a_2566_);
v___x_2588_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2530_, v___x_2587_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2588_);
v___x_2590_ = v___x_2585_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2588_);
lean_ctor_set_uint64(v_reuseFailAlloc_2599_, sizeof(void*)*1, v_tid_2583_);
v___x_2590_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2592_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 4, v___x_2590_);
v___x_2592_ = v___x_2581_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_env_2572_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_nextMacroScope_2573_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_ngen_2574_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_auxDeclNGen_2575_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2598_, 5, v_cache_2576_);
lean_ctor_set(v_reuseFailAlloc_2598_, 6, v_messages_2577_);
lean_ctor_set(v_reuseFailAlloc_2598_, 7, v_infoState_2578_);
lean_ctor_set(v_reuseFailAlloc_2598_, 8, v_snapshotTasks_2579_);
v___x_2592_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = lean_st_ref_set(v___y_2537_, v___x_2592_);
v___x_2594_ = lean_box(0);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2594_);
v___x_2596_ = v___x_2568_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13___boxed(lean_object* v_oldTraces_2604_, lean_object* v_data_2605_, lean_object* v_ref_2606_, lean_object* v_msg_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13(v_oldTraces_2604_, v_data_2605_, v_ref_2606_, v_msg_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__15(lean_object* v_opts_2614_, lean_object* v_opt_2615_){
_start:
{
lean_object* v_name_2616_; lean_object* v_defValue_2617_; lean_object* v_map_2618_; lean_object* v___x_2619_; 
v_name_2616_ = lean_ctor_get(v_opt_2615_, 0);
v_defValue_2617_ = lean_ctor_get(v_opt_2615_, 1);
v_map_2618_ = lean_ctor_get(v_opts_2614_, 0);
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2618_, v_name_2616_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_inc(v_defValue_2617_);
return v_defValue_2617_;
}
else
{
lean_object* v_val_2620_; 
v_val_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_val_2620_);
lean_dec_ref(v___x_2619_);
if (lean_obj_tag(v_val_2620_) == 3)
{
lean_object* v_v_2621_; 
v_v_2621_ = lean_ctor_get(v_val_2620_, 0);
lean_inc(v_v_2621_);
lean_dec_ref(v_val_2620_);
return v_v_2621_;
}
else
{
lean_dec(v_val_2620_);
lean_inc(v_defValue_2617_);
return v_defValue_2617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__15___boxed(lean_object* v_opts_2622_, lean_object* v_opt_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__15(v_opts_2622_, v_opt_2623_);
lean_dec_ref(v_opt_2623_);
lean_dec_ref(v_opts_2622_);
return v_res_2624_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__12(lean_object* v_e_2625_){
_start:
{
if (lean_obj_tag(v_e_2625_) == 0)
{
uint8_t v___x_2626_; 
v___x_2626_ = 2;
return v___x_2626_;
}
else
{
uint8_t v___x_2627_; 
v___x_2627_ = 0;
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__12___boxed(lean_object* v_e_2628_){
_start:
{
uint8_t v_res_2629_; lean_object* v_r_2630_; 
v_res_2629_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__12(v_e_2628_);
lean_dec_ref(v_e_2628_);
v_r_2630_ = lean_box(v_res_2629_);
return v_r_2630_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg(lean_object* v_x_2631_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
v_a_2633_ = lean_ctor_get(v_x_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_x_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v_x_2631_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v_x_2631_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
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
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v_x_2631_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_x_2631_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v_x_2631_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v_x_2631_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 0);
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg___boxed(lean_object* v_x_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg(v_x_2649_);
return v_res_2651_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__0));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__3(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__2));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__4(void){
_start:
{
lean_object* v___x_2658_; double v___x_2659_; 
v___x_2658_ = lean_unsigned_to_nat(1000u);
v___x_2659_ = lean_float_of_nat(v___x_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10(lean_object* v_cls_2660_, uint8_t v_collapsed_2661_, lean_object* v_tag_2662_, lean_object* v_opts_2663_, uint8_t v_clsEnabled_2664_, lean_object* v_oldTraces_2665_, lean_object* v_msg_2666_, lean_object* v_resStartStop_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_fst_2673_; lean_object* v_snd_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2772_; 
v_fst_2673_ = lean_ctor_get(v_resStartStop_2667_, 0);
v_snd_2674_ = lean_ctor_get(v_resStartStop_2667_, 1);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_resStartStop_2667_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2676_ = v_resStartStop_2667_;
v_isShared_2677_ = v_isSharedCheck_2772_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_snd_2674_);
lean_inc(v_fst_2673_);
lean_dec(v_resStartStop_2667_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2772_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v_data_2681_; lean_object* v_fst_2692_; lean_object* v_snd_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2771_; 
v_fst_2692_ = lean_ctor_get(v_snd_2674_, 0);
v_snd_2693_ = lean_ctor_get(v_snd_2674_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_snd_2674_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2695_ = v_snd_2674_;
v_isShared_2696_ = v_isSharedCheck_2771_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_snd_2693_);
lean_inc(v_fst_2692_);
lean_dec(v_snd_2674_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2771_;
goto v_resetjp_2694_;
}
v___jp_2678_:
{
lean_object* v___x_2682_; 
lean_inc(v___y_2679_);
v___x_2682_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__13(v_oldTraces_2665_, v_data_2681_, v___y_2679_, v___y_2680_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref(v___x_2682_);
v___x_2683_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg(v_fst_2673_);
return v___x_2683_;
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_fst_2673_);
v_a_2684_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2682_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2682_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; uint8_t v___x_2698_; lean_object* v___y_2700_; lean_object* v_a_2701_; uint8_t v___y_2725_; double v___y_2756_; 
v___x_2697_ = l_Lean_trace_profiler;
v___x_2698_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2663_, v___x_2697_);
if (v___x_2698_ == 0)
{
v___y_2725_ = v___x_2698_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2762_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2663_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; double v___x_2765_; double v___x_2766_; double v___x_2767_; 
v___x_2763_ = l_Lean_trace_profiler_threshold;
v___x_2764_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__15(v_opts_2663_, v___x_2763_);
v___x_2765_ = lean_float_of_nat(v___x_2764_);
v___x_2766_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__4);
v___x_2767_ = lean_float_div(v___x_2765_, v___x_2766_);
v___y_2756_ = v___x_2767_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; double v___x_2770_; 
v___x_2768_ = l_Lean_trace_profiler_threshold;
v___x_2769_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__15(v_opts_2663_, v___x_2768_);
v___x_2770_ = lean_float_of_nat(v___x_2769_);
v___y_2756_ = v___x_2770_;
goto v___jp_2755_;
}
}
v___jp_2699_:
{
uint8_t v_result_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v_result_2702_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__12(v_fst_2673_);
v___x_2703_ = l_Lean_TraceResult_toEmoji(v_result_2702_);
v___x_2704_ = l_Lean_stringToMessageData(v___x_2703_);
v___x_2705_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__1);
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 7);
lean_ctor_set(v___x_2695_, 1, v___x_2705_);
lean_ctor_set(v___x_2695_, 0, v___x_2704_);
v___x_2707_ = v___x_2695_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v_m_2709_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set_tag(v___x_2676_, 7);
lean_ctor_set(v___x_2676_, 1, v_a_2701_);
lean_ctor_set(v___x_2676_, 0, v___x_2707_);
v_m_2709_ = v___x_2676_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2701_);
v_m_2709_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; double v___x_2712_; lean_object* v_data_2713_; 
v___x_2710_ = lean_box(v_result_2702_);
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
v___x_2712_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
lean_inc_ref(v_tag_2662_);
lean_inc_ref(v___x_2711_);
lean_inc(v_cls_2660_);
v_data_2713_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2713_, 0, v_cls_2660_);
lean_ctor_set(v_data_2713_, 1, v___x_2711_);
lean_ctor_set(v_data_2713_, 2, v_tag_2662_);
lean_ctor_set_float(v_data_2713_, sizeof(void*)*3, v___x_2712_);
lean_ctor_set_float(v_data_2713_, sizeof(void*)*3 + 8, v___x_2712_);
lean_ctor_set_uint8(v_data_2713_, sizeof(void*)*3 + 16, v_collapsed_2661_);
if (v___x_2698_ == 0)
{
lean_dec_ref(v___x_2711_);
lean_dec(v_snd_2693_);
lean_dec(v_fst_2692_);
lean_dec_ref(v_tag_2662_);
lean_dec(v_cls_2660_);
v___y_2679_ = v___y_2700_;
v___y_2680_ = v_m_2709_;
v_data_2681_ = v_data_2713_;
goto v___jp_2678_;
}
else
{
lean_object* v_data_2714_; double v___x_2715_; double v___x_2716_; 
lean_dec_ref(v_data_2713_);
v_data_2714_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2714_, 0, v_cls_2660_);
lean_ctor_set(v_data_2714_, 1, v___x_2711_);
lean_ctor_set(v_data_2714_, 2, v_tag_2662_);
v___x_2715_ = lean_unbox_float(v_fst_2692_);
lean_dec(v_fst_2692_);
lean_ctor_set_float(v_data_2714_, sizeof(void*)*3, v___x_2715_);
v___x_2716_ = lean_unbox_float(v_snd_2693_);
lean_dec(v_snd_2693_);
lean_ctor_set_float(v_data_2714_, sizeof(void*)*3 + 8, v___x_2716_);
lean_ctor_set_uint8(v_data_2714_, sizeof(void*)*3 + 16, v_collapsed_2661_);
v___y_2679_ = v___y_2700_;
v___y_2680_ = v_m_2709_;
v_data_2681_ = v_data_2714_;
goto v___jp_2678_;
}
}
}
}
v___jp_2719_:
{
lean_object* v_ref_2720_; lean_object* v___x_2721_; 
v_ref_2720_ = lean_ctor_get(v___y_2670_, 5);
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
lean_inc(v___y_2669_);
lean_inc_ref(v___y_2668_);
lean_inc(v_fst_2673_);
v___x_2721_ = lean_apply_6(v_msg_2666_, v_fst_2673_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, lean_box(0));
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref(v___x_2721_);
v___y_2700_ = v_ref_2720_;
v_a_2701_ = v_a_2722_;
goto v___jp_2699_;
}
else
{
lean_object* v___x_2723_; 
lean_dec_ref(v___x_2721_);
v___x_2723_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___closed__3);
v___y_2700_ = v_ref_2720_;
v_a_2701_ = v___x_2723_;
goto v___jp_2699_;
}
}
v___jp_2724_:
{
if (v_clsEnabled_2664_ == 0)
{
if (v___y_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v_traceState_2727_; lean_object* v_env_2728_; lean_object* v_nextMacroScope_2729_; lean_object* v_ngen_2730_; lean_object* v_auxDeclNGen_2731_; lean_object* v_cache_2732_; lean_object* v_messages_2733_; lean_object* v_infoState_2734_; lean_object* v_snapshotTasks_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2754_; 
lean_del_object(v___x_2695_);
lean_dec(v_snd_2693_);
lean_dec(v_fst_2692_);
lean_del_object(v___x_2676_);
lean_dec_ref(v_msg_2666_);
lean_dec_ref(v_tag_2662_);
lean_dec(v_cls_2660_);
v___x_2726_ = lean_st_ref_take(v___y_2671_);
v_traceState_2727_ = lean_ctor_get(v___x_2726_, 4);
v_env_2728_ = lean_ctor_get(v___x_2726_, 0);
v_nextMacroScope_2729_ = lean_ctor_get(v___x_2726_, 1);
v_ngen_2730_ = lean_ctor_get(v___x_2726_, 2);
v_auxDeclNGen_2731_ = lean_ctor_get(v___x_2726_, 3);
v_cache_2732_ = lean_ctor_get(v___x_2726_, 5);
v_messages_2733_ = lean_ctor_get(v___x_2726_, 6);
v_infoState_2734_ = lean_ctor_get(v___x_2726_, 7);
v_snapshotTasks_2735_ = lean_ctor_get(v___x_2726_, 8);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2737_ = v___x_2726_;
v_isShared_2738_ = v_isSharedCheck_2754_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_snapshotTasks_2735_);
lean_inc(v_infoState_2734_);
lean_inc(v_messages_2733_);
lean_inc(v_cache_2732_);
lean_inc(v_traceState_2727_);
lean_inc(v_auxDeclNGen_2731_);
lean_inc(v_ngen_2730_);
lean_inc(v_nextMacroScope_2729_);
lean_inc(v_env_2728_);
lean_dec(v___x_2726_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2754_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
uint64_t v_tid_2739_; lean_object* v_traces_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2753_; 
v_tid_2739_ = lean_ctor_get_uint64(v_traceState_2727_, sizeof(void*)*1);
v_traces_2740_ = lean_ctor_get(v_traceState_2727_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_traceState_2727_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2742_ = v_traceState_2727_;
v_isShared_2743_ = v_isSharedCheck_2753_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_traces_2740_);
lean_dec(v_traceState_2727_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2753_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2744_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2665_, v_traces_2740_);
lean_dec_ref(v_traces_2740_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2744_);
v___x_2746_ = v___x_2742_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2744_);
lean_ctor_set_uint64(v_reuseFailAlloc_2752_, sizeof(void*)*1, v_tid_2739_);
v___x_2746_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2748_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 4, v___x_2746_);
v___x_2748_ = v___x_2737_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_env_2728_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_nextMacroScope_2729_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_ngen_2730_);
lean_ctor_set(v_reuseFailAlloc_2751_, 3, v_auxDeclNGen_2731_);
lean_ctor_set(v_reuseFailAlloc_2751_, 4, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2751_, 5, v_cache_2732_);
lean_ctor_set(v_reuseFailAlloc_2751_, 6, v_messages_2733_);
lean_ctor_set(v_reuseFailAlloc_2751_, 7, v_infoState_2734_);
lean_ctor_set(v_reuseFailAlloc_2751_, 8, v_snapshotTasks_2735_);
v___x_2748_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_st_ref_set(v___y_2671_, v___x_2748_);
v___x_2750_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg(v_fst_2673_);
return v___x_2750_;
}
}
}
}
}
else
{
goto v___jp_2719_;
}
}
else
{
goto v___jp_2719_;
}
}
v___jp_2755_:
{
double v___x_2757_; double v___x_2758_; double v___x_2759_; uint8_t v___x_2760_; 
v___x_2757_ = lean_unbox_float(v_snd_2693_);
v___x_2758_ = lean_unbox_float(v_fst_2692_);
v___x_2759_ = lean_float_sub(v___x_2757_, v___x_2758_);
v___x_2760_ = lean_float_decLt(v___y_2756_, v___x_2759_);
v___y_2725_ = v___x_2760_;
goto v___jp_2724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object* v_cls_2773_, lean_object* v_collapsed_2774_, lean_object* v_tag_2775_, lean_object* v_opts_2776_, lean_object* v_clsEnabled_2777_, lean_object* v_oldTraces_2778_, lean_object* v_msg_2779_, lean_object* v_resStartStop_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
uint8_t v_collapsed_boxed_2786_; uint8_t v_clsEnabled_boxed_2787_; lean_object* v_res_2788_; 
v_collapsed_boxed_2786_ = lean_unbox(v_collapsed_2774_);
v_clsEnabled_boxed_2787_ = lean_unbox(v_clsEnabled_2777_);
v_res_2788_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10(v_cls_2773_, v_collapsed_boxed_2786_, v_tag_2775_, v_opts_2776_, v_clsEnabled_boxed_2787_, v_oldTraces_2778_, v_msg_2779_, v_resStartStop_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v_opts_2776_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(lean_object* v_val_2789_, lean_object* v_fst_2790_, lean_object* v_expectedType_2791_, lean_object* v___f_2792_, lean_object* v___f_2793_, lean_object* v___x_2794_, lean_object* v_cls_2795_, lean_object* v_snd_2796_, lean_object* v___x_2797_, lean_object* v_____r_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v_a_2839_; lean_object* v___y_2843_; lean_object* v___x_2856_; 
lean_inc(v_fst_2790_);
v___x_2856_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_val_2789_, v_fst_2790_, v_expectedType_2791_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref(v___x_2856_);
if (lean_obj_tag(v_a_2857_) == 1)
{
lean_object* v_val_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_val_2858_ = lean_ctor_get(v_a_2857_, 0);
lean_inc(v_val_2858_);
lean_dec_ref(v_a_2857_);
v___x_2859_ = lean_box(0);
v___x_2860_ = l_Lean_Meta_trySynthInstance(v_val_2858_, v___x_2859_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
if (lean_obj_tag(v_a_2861_) == 1)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; 
v_a_2862_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_inc_ref(v___f_2792_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2863_ = lean_apply_5(v___f_2792_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; uint8_t v___x_2865_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2863_);
v___x_2865_ = lean_unbox(v_a_2864_);
lean_dec(v_a_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
v___x_2866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v_snd_2796_, v_a_2862_, v___x_2797_, v___x_2794_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
v___y_2843_ = v___x_2866_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2867_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__5);
lean_inc(v_a_2862_);
v___x_2868_ = l_Lean_MessageData_ofExpr(v_a_2862_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_2871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
lean_inc(v_cls_2795_);
v___x_2872_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2795_, v___x_2871_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v_snd_2796_, v_a_2862_, v___x_2797_, v_a_2873_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
v___y_2843_ = v___x_2874_;
goto v___jp_2842_;
}
else
{
lean_object* v_a_2875_; 
lean_dec(v_a_2862_);
lean_dec(v___x_2797_);
lean_dec_ref(v_snd_2796_);
v_a_2875_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2872_);
v_a_2839_ = v_a_2875_;
goto v___jp_2838_;
}
}
}
else
{
lean_object* v_a_2876_; 
lean_dec(v_a_2862_);
lean_dec(v___x_2797_);
lean_dec_ref(v_snd_2796_);
v_a_2876_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2863_);
v_a_2839_ = v_a_2876_;
goto v___jp_2838_;
}
}
else
{
lean_object* v_options_2877_; uint8_t v_hasTrace_2878_; 
lean_dec(v_a_2861_);
lean_dec(v___x_2797_);
lean_dec_ref(v_snd_2796_);
v_options_2877_ = lean_ctor_get(v___y_2801_, 2);
v_hasTrace_2878_ = lean_ctor_get_uint8(v_options_2877_, sizeof(void*)*1);
if (v_hasTrace_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2792_);
lean_dec(v_fst_2790_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2879_ = lean_apply_6(v___f_2793_, v___x_2794_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2879_;
}
else
{
lean_object* v_inheritedTraceOptions_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_inheritedTraceOptions_2880_ = lean_ctor_get(v___y_2801_, 13);
v___x_2881_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1));
lean_inc(v_cls_2795_);
v___x_2882_ = l_Lean_Name_append(v___x_2881_, v_cls_2795_);
v___x_2883_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2880_, v_options_2877_, v___x_2882_);
lean_dec(v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; 
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2792_);
lean_dec(v_fst_2790_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2884_ = lean_apply_6(v___f_2793_, v___x_2794_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2884_;
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2885_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__7);
lean_inc(v_fst_2790_);
v___x_2886_ = l_Lean_MessageData_ofName(v_fst_2790_);
v___x_2887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
lean_inc(v_cls_2795_);
v___x_2890_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2795_, v___x_2889_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2792_);
lean_dec(v_fst_2790_);
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref(v___x_2890_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2892_ = lean_apply_6(v___f_2793_, v_a_2891_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2892_;
}
else
{
lean_object* v_a_2893_; 
v_a_2893_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2893_);
lean_dec_ref(v___x_2890_);
v_a_2839_ = v_a_2893_;
goto v___jp_2838_;
}
}
}
}
}
else
{
lean_object* v_a_2894_; 
lean_dec(v___x_2797_);
lean_dec_ref(v_snd_2796_);
v_a_2894_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2860_);
v_a_2839_ = v_a_2894_;
goto v___jp_2838_;
}
}
else
{
lean_object* v___x_2895_; 
lean_dec(v_a_2857_);
lean_dec(v___x_2797_);
lean_dec_ref(v_snd_2796_);
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2792_);
lean_dec(v_fst_2790_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2895_ = lean_apply_6(v___f_2793_, v___x_2794_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2895_;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v___x_2797_);
lean_dec_ref(v_snd_2796_);
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2793_);
lean_dec_ref(v___f_2792_);
lean_dec(v_fst_2790_);
v_a_2896_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2856_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2856_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
v___jp_2804_:
{
if (v___y_2806_ == 0)
{
lean_object* v___x_2807_; 
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2807_ = lean_apply_5(v___f_2792_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; uint8_t v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v___x_2807_);
v___x_2809_ = lean_unbox(v_a_2808_);
lean_dec(v_a_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref(v___y_2805_);
lean_dec(v_cls_2795_);
lean_dec(v_fst_2790_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2810_ = lean_apply_6(v___f_2793_, v___x_2794_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2811_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__1);
v___x_2812_ = l_Lean_MessageData_ofName(v_fst_2790_);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = l_Lean_Exception_toMessageData(v___y_2805_);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2795_, v___x_2817_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2820_ = lean_apply_6(v___f_2793_, v_a_2819_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2820_;
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref(v___f_2793_);
v_a_2821_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2818_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2818_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v___y_2805_);
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2793_);
lean_dec(v_fst_2790_);
v_a_2829_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2807_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2807_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v___x_2837_; 
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2793_);
lean_dec_ref(v___f_2792_);
lean_dec(v_fst_2790_);
v___x_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___y_2805_);
return v___x_2837_;
}
}
v___jp_2838_:
{
uint8_t v___x_2840_; 
v___x_2840_ = l_Lean_Exception_isInterrupt(v_a_2839_);
if (v___x_2840_ == 0)
{
uint8_t v___x_2841_; 
lean_inc_ref(v_a_2839_);
v___x_2841_ = l_Lean_Exception_isRuntime(v_a_2839_);
v___y_2805_ = v_a_2839_;
v___y_2806_ = v___x_2841_;
goto v___jp_2804_;
}
else
{
v___y_2805_ = v_a_2839_;
v___y_2806_ = v___x_2840_;
goto v___jp_2804_;
}
}
v___jp_2842_:
{
if (lean_obj_tag(v___y_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_cls_2795_);
lean_dec_ref(v___f_2792_);
lean_dec(v_fst_2790_);
v_a_2844_ = lean_ctor_get(v___y_2843_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___y_2843_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2846_ = v___y_2843_;
v_isShared_2847_ = v_isSharedCheck_2854_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___y_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2854_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_a_2844_) == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_dec_ref(v___f_2793_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2794_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2848_);
v___x_2850_ = v___x_2846_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2853_; 
lean_del_object(v___x_2846_);
v_a_2852_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v_a_2844_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2853_ = lean_apply_6(v___f_2793_, v_a_2852_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2853_;
}
}
}
else
{
lean_object* v_a_2855_; 
v_a_2855_ = lean_ctor_get(v___y_2843_, 0);
lean_inc(v_a_2855_);
lean_dec_ref(v___y_2843_);
v_a_2839_ = v_a_2855_;
goto v___jp_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3___boxed(lean_object* v_val_2904_, lean_object* v_fst_2905_, lean_object* v_expectedType_2906_, lean_object* v___f_2907_, lean_object* v___f_2908_, lean_object* v___x_2909_, lean_object* v_cls_2910_, lean_object* v_snd_2911_, lean_object* v___x_2912_, lean_object* v_____r_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_val_2904_, v_fst_2905_, v_expectedType_2906_, v___f_2907_, v___f_2908_, v___x_2909_, v_cls_2910_, v_snd_2911_, v___x_2912_, v_____r_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2919_;
}
}
static uint64_t _init_l_Lean_Meta_wrapInstance___closed__0(void){
_start:
{
uint8_t v___x_2920_; uint64_t v___x_2921_; 
v___x_2920_ = 3;
v___x_2921_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2920_);
return v___x_2921_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__0));
v___x_2924_ = l_Lean_stringToMessageData(v___x_2923_);
return v___x_2924_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__3));
v___x_2929_ = l_Lean_stringToMessageData(v___x_2928_);
return v___x_2929_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__5));
v___x_2932_ = l_Lean_stringToMessageData(v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1));
v___x_2935_ = l_Lean_stringToMessageData(v___x_2934_);
return v___x_2935_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__8));
v___x_2940_ = l_Lean_stringToMessageData(v___x_2939_);
return v___x_2940_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__10));
v___x_2943_ = l_Lean_stringToMessageData(v___x_2942_);
return v___x_2943_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__12));
v___x_2946_ = l_Lean_stringToMessageData(v___x_2945_);
return v___x_2946_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__14));
v___x_2949_ = l_Lean_stringToMessageData(v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(lean_object* v_upperBound_2950_, lean_object* v_fst_2951_, lean_object* v_args_2952_, uint8_t v_compile_2953_, uint8_t v_logCompileErrors_2954_, uint8_t v___x_2955_, uint8_t v_isMeta_2956_, lean_object* v_val_2957_, lean_object* v_expectedType_2958_, lean_object* v_a_2959_, lean_object* v_b_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_a_2967_; lean_object* v___y_2972_; uint8_t v___x_2991_; 
v___x_2991_ = lean_nat_dec_lt(v_a_2959_, v_upperBound_2950_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_b_2960_);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = lean_array_fget_borrowed(v_fst_2951_, v_a_2959_);
v___x_2994_ = l_Lean_Expr_mvarId_x21(v___x_2993_);
lean_inc(v___x_2994_);
v___x_2995_ = l_Lean_MVarId_getDecl(v___x_2994_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v_userName_2997_; lean_object* v_type_2998_; lean_object* v___x_2999_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
v_userName_2997_ = lean_ctor_get(v_a_2996_, 0);
lean_inc(v_userName_2997_);
v_type_2998_ = lean_ctor_get(v_a_2996_, 2);
lean_inc_ref(v_type_2998_);
lean_dec(v_a_2996_);
v___x_2999_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2998_, v___y_2962_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_n(v_a_3000_, 2);
lean_dec_ref(v___x_2999_);
v___x_3001_ = l_Lean_Meta_isProp(v_a_3000_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v_cls_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref(v___x_3001_);
v___x_3003_ = lean_box(0);
v_cls_3004_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3005_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0));
v___x_3006_ = lean_array_fget_borrowed(v_args_2952_, v_a_2959_);
v___x_3007_ = lean_unbox(v_a_3002_);
lean_dec(v_a_3002_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_inc(v_a_3000_);
v___x_3008_ = l_Lean_Meta_isClass_x3f(v_a_3000_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3107_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3107_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3107_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
if (lean_obj_tag(v_a_3009_) == 0)
{
lean_object* v_options_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
lean_del_object(v___x_3011_);
v_options_3013_ = lean_ctor_get(v___y_2963_, 2);
v___x_3014_ = lean_box(v___x_2955_);
v___x_3015_ = lean_box(v___x_2991_);
v___x_3016_ = lean_box(v_compile_2953_);
v___x_3017_ = lean_box(v_logCompileErrors_2954_);
v___x_3018_ = lean_box(v_isMeta_2956_);
lean_inc(v_a_3000_);
lean_inc(v___x_3006_);
lean_inc(v___x_2994_);
v___f_3019_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3019_, 0, v___x_2994_);
lean_closure_set(v___f_3019_, 1, v___x_3006_);
lean_closure_set(v___f_3019_, 2, v___x_3003_);
lean_closure_set(v___f_3019_, 3, v_a_3000_);
lean_closure_set(v___f_3019_, 4, v___x_3014_);
lean_closure_set(v___f_3019_, 5, v___x_3015_);
lean_closure_set(v___f_3019_, 6, v___x_3016_);
lean_closure_set(v___f_3019_, 7, v___x_3017_);
lean_closure_set(v___f_3019_, 8, v___x_3018_);
v___x_3020_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3021_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3013_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
lean_dec_ref(v___f_3019_);
lean_dec(v_userName_2997_);
lean_inc(v___x_3006_);
v___x_3022_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2994_, v___x_3006_, v___x_3003_, v_a_3000_, v___x_2955_, v___x_2991_, v_compile_2953_, v_logCompileErrors_2954_, v_isMeta_2956_, v___x_3003_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3022_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3023_; 
lean_inc(v_userName_2997_);
lean_inc(v_val_2957_);
v___x_3023_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_2957_, v_userName_2997_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v_fst_3027_; lean_object* v_snd_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3059_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref(v___x_3023_);
v_fst_3027_ = lean_ctor_get(v_a_3024_, 0);
v_snd_3028_ = lean_ctor_get(v_a_3024_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3030_ = v_a_3024_;
v_isShared_3031_ = v_isSharedCheck_3059_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_snd_3028_);
lean_inc(v_fst_3027_);
lean_dec(v_a_3024_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3059_;
goto v_resetjp_3029_;
}
v___jp_3025_:
{
lean_object* v___x_3026_; 
lean_inc(v___x_3006_);
v___x_3026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2994_, v___x_3006_, v___x_3003_, v_a_3000_, v___x_2955_, v___x_2991_, v_compile_2953_, v_logCompileErrors_2954_, v_isMeta_2956_, v___x_3003_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3026_;
goto v___jp_2971_;
}
v_resetjp_3029_:
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_name_eq(v_fst_3027_, v_val_2957_);
if (v___x_3032_ == 0)
{
if (v___x_3021_ == 0)
{
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_dec_ref(v___f_3019_);
lean_dec(v_userName_2997_);
goto v___jp_3025_;
}
else
{
lean_object* v___x_3033_; 
lean_dec(v_a_3000_);
v___x_3033_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_3004_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; uint8_t v___x_3035_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = lean_unbox(v_a_3034_);
lean_dec(v_a_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
lean_del_object(v___x_3030_);
lean_dec(v_userName_2997_);
lean_inc_ref(v_expectedType_2958_);
lean_inc(v_val_2957_);
v___x_3036_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_val_2957_, v_fst_3027_, v_expectedType_2958_, v___f_3005_, v___f_3019_, v___x_3003_, v_cls_3004_, v_snd_3028_, v___x_2994_, v___x_3003_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3036_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3037_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4);
v___x_3038_ = l_Lean_MessageData_ofName(v_userName_2997_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 7);
lean_ctor_set(v___x_3030_, 1, v___x_3038_);
lean_ctor_set(v___x_3030_, 0, v___x_3037_);
v___x_3040_ = v___x_3030_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3041_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
lean_inc(v_fst_3027_);
v___x_3043_ = l_Lean_MessageData_ofName(v_fst_3027_);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3004_, v___x_3046_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
lean_inc_ref(v_expectedType_2958_);
lean_inc(v_val_2957_);
v___x_3049_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_val_2957_, v_fst_3027_, v_expectedType_2958_, v___f_3005_, v___f_3019_, v___x_3003_, v_cls_3004_, v_snd_3028_, v___x_2994_, v_a_3048_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3049_;
goto v___jp_2971_;
}
else
{
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_dec_ref(v___f_3019_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_dec_ref(v___f_3019_);
lean_dec(v_userName_2997_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3051_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3033_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3033_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
else
{
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_dec_ref(v___f_3019_);
lean_dec(v_userName_2997_);
goto v___jp_3025_;
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v___f_3019_);
lean_dec(v_a_3000_);
lean_dec(v_userName_2997_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3060_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3023_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3023_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_object* v_options_3068_; lean_object* v_a_3070_; lean_object* v___y_3073_; uint8_t v___y_3074_; lean_object* v_a_3079_; lean_object* v___y_3083_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
lean_dec_ref(v_a_3009_);
lean_dec(v_userName_2997_);
v_options_3068_ = lean_ctor_get(v___y_2963_, 2);
v___x_3087_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3088_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3068_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
lean_del_object(v___x_3011_);
lean_inc(v___x_3006_);
v___x_3089_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_3006_, v_a_3000_, v_compile_2953_, v_logCompileErrors_2954_, v_isMeta_2956_, v___x_2994_, v___x_3003_, v___x_3003_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3089_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_box(0);
lean_inc(v_a_3000_);
v___x_3091_ = l_Lean_Meta_trySynthInstance(v_a_3000_, v___x_3090_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref(v___x_3091_);
if (lean_obj_tag(v_a_3092_) == 1)
{
lean_object* v_a_3093_; lean_object* v___x_3094_; 
v_a_3093_ = lean_ctor_get(v_a_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref(v_a_3092_);
v___x_3094_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_3004_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; uint8_t v___x_3096_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref(v___x_3094_);
v___x_3096_ = lean_unbox(v_a_3095_);
lean_dec(v_a_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; 
lean_inc(v___x_2994_);
v___x_3097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_2994_, v_a_3093_, v___x_3003_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_3083_ = v___x_3097_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3098_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2);
lean_inc(v_a_3093_);
v___x_3099_ = l_Lean_MessageData_ofExpr(v_a_3093_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3004_, v___x_3100_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref(v___x_3101_);
lean_inc(v___x_2994_);
v___x_3103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_2994_, v_a_3093_, v_a_3102_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_3083_ = v___x_3103_;
goto v___jp_3082_;
}
else
{
lean_object* v_a_3104_; 
lean_dec(v_a_3093_);
v_a_3104_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3104_);
lean_dec_ref(v___x_3101_);
v_a_3079_ = v_a_3104_;
goto v___jp_3078_;
}
}
}
else
{
lean_object* v_a_3105_; 
lean_dec(v_a_3093_);
v_a_3105_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3105_);
lean_dec_ref(v___x_3094_);
v_a_3079_ = v_a_3105_;
goto v___jp_3078_;
}
}
else
{
lean_dec(v_a_3092_);
lean_del_object(v___x_3011_);
v_a_3070_ = v___x_3003_;
goto v___jp_3069_;
}
}
else
{
lean_object* v_a_3106_; 
v_a_3106_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v___x_3091_);
v_a_3079_ = v_a_3106_;
goto v___jp_3078_;
}
}
v___jp_3069_:
{
lean_object* v___x_3071_; 
lean_inc(v___x_3006_);
v___x_3071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_3006_, v_a_3000_, v_compile_2953_, v_logCompileErrors_2954_, v_isMeta_2956_, v___x_2994_, v___x_3003_, v_a_3070_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3071_;
goto v___jp_2971_;
}
v___jp_3072_:
{
if (v___y_3074_ == 0)
{
lean_dec_ref(v___y_3073_);
lean_del_object(v___x_3011_);
v_a_3070_ = v___x_3003_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3076_; 
lean_dec(v_a_3000_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 1);
lean_ctor_set(v___x_3011_, 0, v___y_3073_);
v___x_3076_ = v___x_3011_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___y_3073_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
v___jp_3078_:
{
uint8_t v___x_3080_; 
v___x_3080_ = l_Lean_Exception_isInterrupt(v_a_3079_);
if (v___x_3080_ == 0)
{
uint8_t v___x_3081_; 
lean_inc_ref(v_a_3079_);
v___x_3081_ = l_Lean_Exception_isRuntime(v_a_3079_);
v___y_3073_ = v_a_3079_;
v___y_3074_ = v___x_3081_;
goto v___jp_3072_;
}
else
{
v___y_3073_ = v_a_3079_;
v___y_3074_ = v___x_3080_;
goto v___jp_3072_;
}
}
v___jp_3082_:
{
if (lean_obj_tag(v___y_3083_) == 0)
{
lean_object* v_a_3084_; 
lean_del_object(v___x_3011_);
v_a_3084_ = lean_ctor_get(v___y_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___y_3083_);
if (lean_obj_tag(v_a_3084_) == 0)
{
lean_dec(v_a_3000_);
lean_dec(v___x_2994_);
v_a_2967_ = v___x_3003_;
goto v___jp_2966_;
}
else
{
lean_object* v_a_3085_; 
v_a_3085_ = lean_ctor_get(v_a_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref(v_a_3084_);
v_a_3070_ = v_a_3085_;
goto v___jp_3069_;
}
}
else
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___y_3083_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___y_3083_);
v_a_3079_ = v_a_3086_;
goto v___jp_3078_;
}
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3000_);
lean_dec(v_userName_2997_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3108_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3008_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3008_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v___x_3116_; 
lean_dec(v_userName_2997_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
lean_inc(v___x_3006_);
v___x_3116_ = lean_infer_type(v___x_3006_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3118_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc_n(v_a_3117_, 2);
lean_dec_ref(v___x_3116_);
lean_inc(v_a_3000_);
v___x_3118_ = l_Lean_Meta_isExprDefEq(v_a_3000_, v_a_3117_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___f_3120_; uint8_t v___x_3121_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref(v___x_3118_);
v___f_3120_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__7));
v___x_3121_ = lean_unbox(v_a_3119_);
lean_dec(v_a_3119_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_3004_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; uint8_t v___x_3124_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref(v___x_3122_);
v___x_3124_ = lean_unbox(v_a_3123_);
lean_dec(v_a_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
lean_dec(v_a_3117_);
lean_inc(v___x_3006_);
v___x_3125_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_3000_, v___x_3006_, v___x_2991_, v___x_2994_, v___f_3120_, v___x_3003_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3125_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3126_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9);
lean_inc(v_a_2959_);
v___x_3127_ = l_Nat_reprFast(v_a_2959_);
v___x_3128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
v___x_3129_ = l_Lean_MessageData_ofFormat(v___x_3128_);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3126_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11);
v___x_3132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3130_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
lean_inc(v_a_3000_);
v___x_3133_ = l_Lean_MessageData_ofExpr(v_a_3000_);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_MessageData_ofExpr(v_a_3117_);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
lean_inc(v___x_3006_);
v___x_3141_ = l_Lean_MessageData_ofExpr(v___x_3006_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3004_, v___x_3142_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3145_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3143_);
lean_inc(v___x_3006_);
v___x_3145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_3000_, v___x_3006_, v___x_2991_, v___x_2994_, v___f_3120_, v_a_3144_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3145_;
goto v___jp_2971_;
}
else
{
lean_dec(v_a_3000_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
return v___x_3143_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_a_3117_);
lean_dec(v_a_3000_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3146_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3122_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3122_);
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
else
{
lean_object* v___x_3154_; 
lean_dec(v_a_3117_);
lean_dec(v_a_3000_);
lean_inc(v___x_3006_);
v___x_3154_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2994_, v___x_3006_, v___y_2962_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6(v___x_3003_, v_a_3155_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
v___y_2972_ = v___x_3156_;
goto v___jp_2971_;
}
else
{
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
return v___x_3154_;
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec(v_a_3117_);
lean_dec(v_a_3000_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3157_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3118_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3118_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec(v_a_3000_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3165_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3116_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3116_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v_a_3000_);
lean_dec(v_userName_2997_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3173_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3001_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3001_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_userName_2997_);
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3181_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_2999_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_2999_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v___x_2994_);
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_3189_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_2995_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_2995_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
v___jp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_unsigned_to_nat(1u);
v___x_2969_ = lean_nat_add(v_a_2959_, v___x_2968_);
lean_dec(v_a_2959_);
v_a_2959_ = v___x_2969_;
v_b_2960_ = v_a_2967_;
goto _start;
}
v___jp_2971_:
{
if (lean_obj_tag(v___y_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2982_; 
v_a_2973_ = lean_ctor_get(v___y_2972_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___y_2972_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2975_ = v___y_2972_;
v_isShared_2976_ = v_isSharedCheck_2982_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___y_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2982_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
if (lean_obj_tag(v_a_2973_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2979_; 
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_2977_ = lean_ctor_get(v_a_2973_, 0);
lean_inc(v_a_2977_);
lean_dec_ref(v_a_2973_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v_a_2977_);
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
else
{
lean_object* v_a_2981_; 
lean_del_object(v___x_2975_);
v_a_2981_ = lean_ctor_get(v_a_2973_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v_a_2973_);
v_a_2967_ = v_a_2981_;
goto v___jp_2966_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2959_);
lean_dec_ref(v_expectedType_2958_);
lean_dec(v_val_2957_);
v_a_2983_ = lean_ctor_get(v___y_2972_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___y_2972_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___y_2972_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___y_2972_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__2));
v___x_3199_ = l_Lean_stringToMessageData(v___x_3198_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__4));
v___x_3202_ = l_Lean_stringToMessageData(v___x_3201_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__6));
v___x_3205_ = l_Lean_stringToMessageData(v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8_spec__9(lean_object* v_inst_3206_, lean_object* v_expectedType_3207_, uint8_t v___x_3208_, uint8_t v_compile_3209_, uint8_t v_logCompileErrors_3210_, uint8_t v_isMeta_3211_, lean_object* v_val_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; 
if (lean_obj_tag(v_x_3213_) == 5)
{
lean_object* v_fn_3260_; lean_object* v_arg_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_fn_3260_ = lean_ctor_get(v_x_3213_, 0);
lean_inc_ref(v_fn_3260_);
v_arg_3261_ = lean_ctor_get(v_x_3213_, 1);
lean_inc_ref(v_arg_3261_);
lean_dec_ref(v_x_3213_);
v___x_3262_ = lean_array_set(v_x_3214_, v_x_3215_, v_arg_3261_);
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3264_ = lean_nat_sub(v_x_3215_, v___x_3263_);
lean_dec(v_x_3215_);
v_x_3213_ = v_fn_3260_;
v_x_3214_ = v___x_3262_;
v_x_3215_ = v___x_3264_;
goto _start;
}
else
{
uint8_t v___x_3266_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v_options_3271_; lean_object* v___y_3272_; lean_object* v_cls_3338_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___x_3361_; 
lean_dec(v_x_3215_);
v___x_3266_ = 1;
v_cls_3338_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3361_ = l_Lean_Expr_constName_x3f(v_x_3213_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_dec_ref(v_x_3214_);
lean_dec_ref(v_x_3213_);
lean_dec(v_val_3212_);
v___y_3340_ = v___y_3216_;
v___y_3341_ = v___y_3217_;
v___y_3342_ = v___y_3218_;
v___y_3343_ = v___y_3219_;
goto v___jp_3339_;
}
else
{
lean_object* v_val_3362_; lean_object* v___x_3363_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_val_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3362_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref(v___x_3363_);
if (lean_obj_tag(v_a_3364_) == 6)
{
lean_object* v_val_3365_; lean_object* v___x_3366_; 
lean_dec_ref(v_inst_3206_);
v_val_3365_ = lean_ctor_get(v_a_3364_, 0);
lean_inc_ref(v_val_3365_);
lean_dec_ref(v_a_3364_);
lean_inc(v___y_3219_);
lean_inc_ref(v___y_3218_);
lean_inc(v___y_3217_);
lean_inc_ref(v___y_3216_);
lean_inc_ref(v_x_3213_);
v___x_3366_ = lean_infer_type(v_x_3213_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref(v___x_3366_);
v___x_3368_ = 0;
v___x_3369_ = l_Lean_Meta_forallMetaTelescope(v_a_3367_, v___x_3368_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v_snd_3371_; lean_object* v_fst_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3471_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3369_);
v_snd_3371_ = lean_ctor_get(v_a_3370_, 1);
v_fst_3372_ = lean_ctor_get(v_a_3370_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_a_3370_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3374_ = v_a_3370_;
v_isShared_3375_ = v_isSharedCheck_3471_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_snd_3371_);
lean_inc(v_fst_3372_);
lean_dec(v_a_3370_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3471_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_snd_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3469_; 
v_snd_3376_ = lean_ctor_get(v_snd_3371_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_snd_3371_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v_snd_3371_, 0);
lean_dec(v_unused_3470_);
v___x_3378_ = v_snd_3371_;
v_isShared_3379_ = v_isSharedCheck_3469_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_snd_3376_);
lean_dec(v_snd_3371_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3469_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3380_ = lean_array_get_size(v_x_3214_);
v___x_3417_ = lean_array_get_size(v_fst_3372_);
v___x_3418_ = lean_nat_dec_eq(v___x_3380_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
lean_dec(v_snd_3376_);
lean_dec(v_fst_3372_);
lean_dec_ref(v_val_3365_);
lean_dec(v_val_3212_);
lean_dec_ref(v_expectedType_3207_);
v___x_3419_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3);
v___x_3420_ = l_Lean_MessageData_ofExpr(v_x_3213_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 7);
lean_ctor_set(v___x_3378_, 1, v___x_3420_);
lean_ctor_set(v___x_3378_, 0, v___x_3419_);
v___x_3422_ = v___x_3378_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3423_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 7);
lean_ctor_set(v___x_3374_, 1, v___x_3423_);
lean_ctor_set(v___x_3374_, 0, v___x_3422_);
v___x_3425_ = v___x_3374_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3426_ = lean_array_to_list(v_x_3214_);
v___x_3427_ = lean_box(0);
v___x_3428_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(v___x_3426_, v___x_3427_);
v___x_3429_ = l_Lean_MessageData_ofList(v___x_3428_);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3425_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3430_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3431_;
}
}
}
else
{
lean_object* v___x_3434_; 
lean_inc_ref(v_expectedType_3207_);
v___x_3434_ = l_Lean_Meta_isExprDefEq(v_expectedType_3207_, v_snd_3376_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; uint8_t v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref(v___x_3434_);
v___x_3436_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
if (v___x_3436_ == 0)
{
lean_object* v_toConstantVal_3437_; lean_object* v_name_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_dec(v_fst_3372_);
lean_dec_ref(v_x_3214_);
lean_dec_ref(v_x_3213_);
lean_dec(v_val_3212_);
v_toConstantVal_3437_ = lean_ctor_get(v_val_3365_, 0);
lean_inc_ref(v_toConstantVal_3437_);
lean_dec_ref(v_val_3365_);
v_name_3438_ = lean_ctor_get(v_toConstantVal_3437_, 0);
lean_inc(v_name_3438_);
lean_dec_ref(v_toConstantVal_3437_);
v___x_3439_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5);
v___x_3440_ = l_Lean_MessageData_ofExpr(v_expectedType_3207_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 7);
lean_ctor_set(v___x_3378_, 1, v___x_3440_);
lean_ctor_set(v___x_3378_, 0, v___x_3439_);
v___x_3442_ = v___x_3378_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 7);
lean_ctor_set(v___x_3374_, 1, v___x_3443_);
lean_ctor_set(v___x_3374_, 0, v___x_3442_);
v___x_3445_ = v___x_3374_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v___x_3446_ = l_Lean_MessageData_ofConstName(v_name_3438_, v___x_3208_);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3447_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3449_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
else
{
lean_del_object(v___x_3378_);
lean_del_object(v___x_3374_);
v___y_3382_ = v___y_3216_;
v___y_3383_ = v___y_3217_;
v___y_3384_ = v___y_3218_;
v___y_3385_ = v___y_3219_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_del_object(v___x_3378_);
lean_del_object(v___x_3374_);
lean_dec(v_fst_3372_);
lean_dec_ref(v_val_3365_);
lean_dec_ref(v_x_3214_);
lean_dec_ref(v_x_3213_);
lean_dec(v_val_3212_);
lean_dec_ref(v_expectedType_3207_);
v_a_3461_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3434_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3434_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
v___jp_3381_:
{
lean_object* v_numParams_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_numParams_3386_ = lean_ctor_get(v_val_3365_, 3);
lean_inc(v_numParams_3386_);
lean_dec_ref(v_val_3365_);
v___x_3387_ = lean_box(0);
v___x_3388_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_3380_, v_fst_3372_, v_x_3214_, v_compile_3209_, v_logCompileErrors_3210_, v___x_3208_, v_isMeta_3211_, v_val_3212_, v_expectedType_3207_, v_numParams_3386_, v___x_3387_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec_ref(v_x_3214_);
if (lean_obj_tag(v___x_3388_) == 0)
{
size_t v_sz_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
lean_dec_ref(v___x_3388_);
v_sz_3389_ = lean_array_size(v_fst_3372_);
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_3389_, v___x_3390_, v_fst_3372_, v___y_3383_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3400_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3400_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3400_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3396_ = l_Lean_mkAppN(v_x_3213_, v_a_3392_);
lean_dec(v_a_3392_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v___x_3396_);
v___x_3398_ = v___x_3394_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec_ref(v_x_3213_);
v_a_3401_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3391_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3391_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_fst_3372_);
lean_dec_ref(v_x_3213_);
v_a_3409_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3388_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3388_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v_val_3365_);
lean_dec_ref(v_x_3214_);
lean_dec_ref(v_x_3213_);
lean_dec(v_val_3212_);
lean_dec_ref(v_expectedType_3207_);
v_a_3472_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3369_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3369_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_dec_ref(v_val_3365_);
lean_dec_ref(v_x_3214_);
lean_dec_ref(v_x_3213_);
lean_dec(v_val_3212_);
lean_dec_ref(v_expectedType_3207_);
return v___x_3366_;
}
}
else
{
lean_dec(v_a_3364_);
lean_dec_ref(v_x_3214_);
lean_dec_ref(v_x_3213_);
lean_dec(v_val_3212_);
v___y_3340_ = v___y_3216_;
v___y_3341_ = v___y_3217_;
v___y_3342_ = v___y_3218_;
v___y_3343_ = v___y_3219_;
goto v___jp_3339_;
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec_ref(v_x_3214_);
lean_dec_ref(v_x_3213_);
lean_dec(v_val_3212_);
lean_dec_ref(v_expectedType_3207_);
lean_dec_ref(v_inst_3206_);
v_a_3480_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3363_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3363_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
v___jp_3267_:
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3274_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3271_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
lean_dec_ref(v_expectedType_3207_);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_inst_3206_);
return v___x_3275_;
}
else
{
lean_object* v___x_3276_; 
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc_ref(v___y_3268_);
lean_inc_ref(v_inst_3206_);
v___x_3276_ = lean_infer_type(v_inst_3206_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3272_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
lean_inc_ref(v_expectedType_3207_);
v___x_3278_ = l_Lean_Meta_isExprDefEq(v_expectedType_3207_, v_a_3277_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3272_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3329_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3329_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3329_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
uint8_t v___x_3283_; 
v___x_3283_ = lean_unbox(v_a_3279_);
lean_dec(v_a_3279_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_a_3286_; lean_object* v___x_3287_; 
lean_del_object(v___x_3281_);
v___x_3284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_3285_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3284_, v___y_3272_);
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc_n(v_a_3286_, 2);
lean_dec_ref(v___x_3285_);
v___x_3287_ = l_Lean_Meta_mkAuxDefinition(v_a_3286_, v_expectedType_3207_, v_inst_3206_, v___x_3208_, v___x_3208_, v___x_3266_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3272_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref(v___x_3287_);
v___x_3289_ = 3;
lean_inc(v_a_3286_);
v___x_3290_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3286_, v___x_3289_, v___y_3269_, v___y_3272_);
lean_dec_ref(v___x_3290_);
if (v_isMeta_3211_ == 0)
{
v___y_3244_ = v_a_3286_;
v___y_3245_ = v_a_3288_;
v___y_3246_ = v___y_3270_;
v___y_3247_ = v___y_3272_;
goto v___jp_3243_;
}
else
{
lean_object* v___x_3291_; lean_object* v_env_3292_; lean_object* v_nextMacroScope_3293_; lean_object* v_ngen_3294_; lean_object* v_auxDeclNGen_3295_; lean_object* v_traceState_3296_; lean_object* v_messages_3297_; lean_object* v_infoState_3298_; lean_object* v_snapshotTasks_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3324_; 
v___x_3291_ = lean_st_ref_take(v___y_3272_);
v_env_3292_ = lean_ctor_get(v___x_3291_, 0);
v_nextMacroScope_3293_ = lean_ctor_get(v___x_3291_, 1);
v_ngen_3294_ = lean_ctor_get(v___x_3291_, 2);
v_auxDeclNGen_3295_ = lean_ctor_get(v___x_3291_, 3);
v_traceState_3296_ = lean_ctor_get(v___x_3291_, 4);
v_messages_3297_ = lean_ctor_get(v___x_3291_, 6);
v_infoState_3298_ = lean_ctor_get(v___x_3291_, 7);
v_snapshotTasks_3299_ = lean_ctor_get(v___x_3291_, 8);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; 
v_unused_3325_ = lean_ctor_get(v___x_3291_, 5);
lean_dec(v_unused_3325_);
v___x_3301_ = v___x_3291_;
v_isShared_3302_ = v_isSharedCheck_3324_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_snapshotTasks_3299_);
lean_inc(v_infoState_3298_);
lean_inc(v_messages_3297_);
lean_inc(v_traceState_3296_);
lean_inc(v_auxDeclNGen_3295_);
lean_inc(v_ngen_3294_);
lean_inc(v_nextMacroScope_3293_);
lean_inc(v_env_3292_);
lean_dec(v___x_3291_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3324_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
lean_inc(v_a_3286_);
v___x_3303_ = l_Lean_markMeta(v_env_3292_, v_a_3286_);
v___x_3304_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 5, v___x_3304_);
lean_ctor_set(v___x_3301_, 0, v___x_3303_);
v___x_3306_ = v___x_3301_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3303_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_nextMacroScope_3293_);
lean_ctor_set(v_reuseFailAlloc_3323_, 2, v_ngen_3294_);
lean_ctor_set(v_reuseFailAlloc_3323_, 3, v_auxDeclNGen_3295_);
lean_ctor_set(v_reuseFailAlloc_3323_, 4, v_traceState_3296_);
lean_ctor_set(v_reuseFailAlloc_3323_, 5, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3323_, 6, v_messages_3297_);
lean_ctor_set(v_reuseFailAlloc_3323_, 7, v_infoState_3298_);
lean_ctor_set(v_reuseFailAlloc_3323_, 8, v_snapshotTasks_3299_);
v___x_3306_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_mctx_3309_; lean_object* v_zetaDeltaFVarIds_3310_; lean_object* v_postponed_3311_; lean_object* v_diag_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3321_; 
v___x_3307_ = lean_st_ref_set(v___y_3272_, v___x_3306_);
v___x_3308_ = lean_st_ref_take(v___y_3269_);
v_mctx_3309_ = lean_ctor_get(v___x_3308_, 0);
v_zetaDeltaFVarIds_3310_ = lean_ctor_get(v___x_3308_, 2);
v_postponed_3311_ = lean_ctor_get(v___x_3308_, 3);
v_diag_3312_ = lean_ctor_get(v___x_3308_, 4);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v___x_3308_, 1);
lean_dec(v_unused_3322_);
v___x_3314_ = v___x_3308_;
v_isShared_3315_ = v_isSharedCheck_3321_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_diag_3312_);
lean_inc(v_postponed_3311_);
lean_inc(v_zetaDeltaFVarIds_3310_);
lean_inc(v_mctx_3309_);
lean_dec(v___x_3308_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3321_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 1, v___x_3316_);
v___x_3318_ = v___x_3314_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_mctx_3309_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_zetaDeltaFVarIds_3310_);
lean_ctor_set(v_reuseFailAlloc_3320_, 3, v_postponed_3311_);
lean_ctor_set(v_reuseFailAlloc_3320_, 4, v_diag_3312_);
v___x_3318_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_st_ref_set(v___y_3269_, v___x_3318_);
v___y_3244_ = v_a_3286_;
v___y_3245_ = v_a_3288_;
v___y_3246_ = v___y_3270_;
v___y_3247_ = v___y_3272_;
goto v___jp_3243_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3286_);
return v___x_3287_;
}
}
else
{
lean_object* v___x_3327_; 
lean_dec_ref(v_expectedType_3207_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v_inst_3206_);
v___x_3327_ = v___x_3281_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_inst_3206_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v_expectedType_3207_);
lean_dec_ref(v_inst_3206_);
v_a_3330_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3278_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3278_);
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
else
{
lean_dec_ref(v_expectedType_3207_);
lean_dec_ref(v_inst_3206_);
return v___x_3276_;
}
}
}
v___jp_3339_:
{
lean_object* v_options_3344_; uint8_t v_hasTrace_3345_; 
v_options_3344_ = lean_ctor_get(v___y_3342_, 2);
v_hasTrace_3345_ = lean_ctor_get_uint8(v_options_3344_, sizeof(void*)*1);
if (v_hasTrace_3345_ == 0)
{
v___y_3268_ = v___y_3340_;
v___y_3269_ = v___y_3341_;
v___y_3270_ = v___y_3342_;
v_options_3271_ = v_options_3344_;
v___y_3272_ = v___y_3343_;
goto v___jp_3267_;
}
else
{
lean_object* v_inheritedTraceOptions_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v_inheritedTraceOptions_3346_ = lean_ctor_get(v___y_3342_, 13);
v___x_3347_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_3348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3346_, v_options_3344_, v___x_3347_);
if (v___x_3348_ == 0)
{
v___y_3268_ = v___y_3340_;
v___y_3269_ = v___y_3341_;
v___y_3270_ = v___y_3342_;
v_options_3271_ = v_options_3344_;
v___y_3272_ = v___y_3343_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3349_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1);
lean_inc_ref(v_inst_3206_);
v___x_3350_ = l_Lean_MessageData_ofExpr(v_inst_3206_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3338_, v___x_3351_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_dec_ref(v___x_3352_);
v___y_3268_ = v___y_3340_;
v___y_3269_ = v___y_3341_;
v___y_3270_ = v___y_3342_;
v_options_3271_ = v_options_3344_;
v___y_3272_ = v___y_3343_;
goto v___jp_3267_;
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v_expectedType_3207_);
lean_dec_ref(v_inst_3206_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
}
}
v___jp_3221_:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_enableRealizationsForConst(v___y_3222_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v___x_3226_, 0);
lean_dec(v_unused_3234_);
v___x_3228_ = v___x_3226_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v___x_3226_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___y_3223_);
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___y_3223_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v___y_3223_);
v_a_3235_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3226_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3226_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
v___jp_3243_:
{
if (v_compile_3209_ == 0)
{
v___y_3222_ = v___y_3244_;
v___y_3223_ = v___y_3245_;
v___y_3224_ = v___y_3246_;
v___y_3225_ = v___y_3247_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3248_ = lean_unsigned_to_nat(1u);
v___x_3249_ = lean_mk_empty_array_with_capacity(v___x_3248_);
lean_inc(v___y_3244_);
v___x_3250_ = lean_array_push(v___x_3249_, v___y_3244_);
v___x_3251_ = l_Lean_compileDecls(v___x_3250_, v_logCompileErrors_3210_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_dec_ref(v___x_3251_);
v___y_3222_ = v___y_3244_;
v___y_3223_ = v___y_3245_;
v___y_3224_ = v___y_3246_;
v___y_3225_ = v___y_3247_;
goto v___jp_3221_;
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8(lean_object* v_inst_3488_, lean_object* v_expectedType_3489_, uint8_t v___x_3490_, uint8_t v_compile_3491_, uint8_t v_logCompileErrors_3492_, uint8_t v_isMeta_3493_, lean_object* v_val_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; 
if (lean_obj_tag(v_x_3495_) == 5)
{
lean_object* v_fn_3542_; lean_object* v_arg_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_fn_3542_ = lean_ctor_get(v_x_3495_, 0);
lean_inc_ref(v_fn_3542_);
v_arg_3543_ = lean_ctor_get(v_x_3495_, 1);
lean_inc_ref(v_arg_3543_);
lean_dec_ref(v_x_3495_);
v___x_3544_ = lean_array_set(v_x_3496_, v_x_3497_, v_arg_3543_);
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = lean_nat_sub(v_x_3497_, v___x_3545_);
v___x_3547_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8_spec__9(v_inst_3488_, v_expectedType_3489_, v___x_3490_, v_compile_3491_, v_logCompileErrors_3492_, v_isMeta_3493_, v_val_3494_, v_fn_3542_, v___x_3544_, v___x_3546_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
return v___x_3547_;
}
else
{
uint8_t v___x_3548_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v_options_3553_; lean_object* v___y_3554_; lean_object* v_cls_3620_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___x_3643_; 
v___x_3548_ = 1;
v_cls_3620_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3643_ = l_Lean_Expr_constName_x3f(v_x_3495_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3495_);
lean_dec(v_val_3494_);
v___y_3622_ = v___y_3498_;
v___y_3623_ = v___y_3499_;
v___y_3624_ = v___y_3500_;
v___y_3625_ = v___y_3501_;
goto v___jp_3621_;
}
else
{
lean_object* v_val_3644_; lean_object* v___x_3645_; 
v_val_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_val_3644_);
lean_dec_ref(v___x_3643_);
v___x_3645_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3644_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3645_);
if (lean_obj_tag(v_a_3646_) == 6)
{
lean_object* v_val_3647_; lean_object* v___x_3648_; 
lean_dec_ref(v_inst_3488_);
v_val_3647_ = lean_ctor_get(v_a_3646_, 0);
lean_inc_ref(v_val_3647_);
lean_dec_ref(v_a_3646_);
lean_inc(v___y_3501_);
lean_inc_ref(v___y_3500_);
lean_inc(v___y_3499_);
lean_inc_ref(v___y_3498_);
lean_inc_ref(v_x_3495_);
v___x_3648_ = lean_infer_type(v_x_3495_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; uint8_t v___x_3650_; lean_object* v___x_3651_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = 0;
v___x_3651_ = l_Lean_Meta_forallMetaTelescope(v_a_3649_, v___x_3650_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v_snd_3653_; lean_object* v_fst_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3753_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref(v___x_3651_);
v_snd_3653_ = lean_ctor_get(v_a_3652_, 1);
v_fst_3654_ = lean_ctor_get(v_a_3652_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_a_3652_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3656_ = v_a_3652_;
v_isShared_3657_ = v_isSharedCheck_3753_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_snd_3653_);
lean_inc(v_fst_3654_);
lean_dec(v_a_3652_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3753_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v_snd_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3751_; 
v_snd_3658_ = lean_ctor_get(v_snd_3653_, 1);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_snd_3653_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; 
v_unused_3752_ = lean_ctor_get(v_snd_3653_, 0);
lean_dec(v_unused_3752_);
v___x_3660_ = v_snd_3653_;
v_isShared_3661_ = v_isSharedCheck_3751_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_snd_3658_);
lean_dec(v_snd_3653_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3751_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3662_ = lean_array_get_size(v_x_3496_);
v___x_3699_ = lean_array_get_size(v_fst_3654_);
v___x_3700_ = lean_nat_dec_eq(v___x_3662_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
lean_dec(v_snd_3658_);
lean_dec(v_fst_3654_);
lean_dec_ref(v_val_3647_);
lean_dec(v_val_3494_);
lean_dec_ref(v_expectedType_3489_);
v___x_3701_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3);
v___x_3702_ = l_Lean_MessageData_ofExpr(v_x_3495_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set_tag(v___x_3660_, 7);
lean_ctor_set(v___x_3660_, 1, v___x_3702_);
lean_ctor_set(v___x_3660_, 0, v___x_3701_);
v___x_3704_ = v___x_3660_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; lean_object* v___x_3707_; 
v___x_3705_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
if (v_isShared_3657_ == 0)
{
lean_ctor_set_tag(v___x_3656_, 7);
lean_ctor_set(v___x_3656_, 1, v___x_3705_);
lean_ctor_set(v___x_3656_, 0, v___x_3704_);
v___x_3707_ = v___x_3656_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3708_ = lean_array_to_list(v_x_3496_);
v___x_3709_ = lean_box(0);
v___x_3710_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(v___x_3708_, v___x_3709_);
v___x_3711_ = l_Lean_MessageData_ofList(v___x_3710_);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3707_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3712_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
return v___x_3713_;
}
}
}
else
{
lean_object* v___x_3716_; 
lean_inc_ref(v_expectedType_3489_);
v___x_3716_ = l_Lean_Meta_isExprDefEq(v_expectedType_3489_, v_snd_3658_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; uint8_t v___x_3718_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref(v___x_3716_);
v___x_3718_ = lean_unbox(v_a_3717_);
lean_dec(v_a_3717_);
if (v___x_3718_ == 0)
{
lean_object* v_toConstantVal_3719_; lean_object* v_name_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
lean_dec(v_fst_3654_);
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3495_);
lean_dec(v_val_3494_);
v_toConstantVal_3719_ = lean_ctor_get(v_val_3647_, 0);
lean_inc_ref(v_toConstantVal_3719_);
lean_dec_ref(v_val_3647_);
v_name_3720_ = lean_ctor_get(v_toConstantVal_3719_, 0);
lean_inc(v_name_3720_);
lean_dec_ref(v_toConstantVal_3719_);
v___x_3721_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5);
v___x_3722_ = l_Lean_MessageData_ofExpr(v_expectedType_3489_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set_tag(v___x_3660_, 7);
lean_ctor_set(v___x_3660_, 1, v___x_3722_);
lean_ctor_set(v___x_3660_, 0, v___x_3721_);
v___x_3724_ = v___x_3660_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3725_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7);
if (v_isShared_3657_ == 0)
{
lean_ctor_set_tag(v___x_3656_, 7);
lean_ctor_set(v___x_3656_, 1, v___x_3725_);
lean_ctor_set(v___x_3656_, 0, v___x_3724_);
v___x_3727_ = v___x_3656_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
v___x_3728_ = l_Lean_MessageData_ofConstName(v_name_3720_, v___x_3490_);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3731_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
else
{
lean_del_object(v___x_3660_);
lean_del_object(v___x_3656_);
v___y_3664_ = v___y_3498_;
v___y_3665_ = v___y_3499_;
v___y_3666_ = v___y_3500_;
v___y_3667_ = v___y_3501_;
goto v___jp_3663_;
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3660_);
lean_del_object(v___x_3656_);
lean_dec(v_fst_3654_);
lean_dec_ref(v_val_3647_);
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3495_);
lean_dec(v_val_3494_);
lean_dec_ref(v_expectedType_3489_);
v_a_3743_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3716_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3716_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
v___jp_3663_:
{
lean_object* v_numParams_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_numParams_3668_ = lean_ctor_get(v_val_3647_, 3);
lean_inc(v_numParams_3668_);
lean_dec_ref(v_val_3647_);
v___x_3669_ = lean_box(0);
v___x_3670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_3662_, v_fst_3654_, v_x_3496_, v_compile_3491_, v_logCompileErrors_3492_, v___x_3490_, v_isMeta_3493_, v_val_3494_, v_expectedType_3489_, v_numParams_3668_, v___x_3669_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec_ref(v_x_3496_);
if (lean_obj_tag(v___x_3670_) == 0)
{
size_t v_sz_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
lean_dec_ref(v___x_3670_);
v_sz_3671_ = lean_array_size(v_fst_3654_);
v___x_3672_ = ((size_t)0ULL);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_3671_, v___x_3672_, v_fst_3654_, v___y_3665_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3682_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3682_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3682_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3678_ = l_Lean_mkAppN(v_x_3495_, v_a_3674_);
lean_dec(v_a_3674_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v___x_3678_);
v___x_3680_ = v___x_3676_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v_x_3495_);
v_a_3683_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3673_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3673_);
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
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_fst_3654_);
lean_dec_ref(v_x_3495_);
v_a_3691_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3670_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3670_);
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
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref(v_val_3647_);
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3495_);
lean_dec(v_val_3494_);
lean_dec_ref(v_expectedType_3489_);
v_a_3754_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3651_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3651_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_dec_ref(v_val_3647_);
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3495_);
lean_dec(v_val_3494_);
lean_dec_ref(v_expectedType_3489_);
return v___x_3648_;
}
}
else
{
lean_dec(v_a_3646_);
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3495_);
lean_dec(v_val_3494_);
v___y_3622_ = v___y_3498_;
v___y_3623_ = v___y_3499_;
v___y_3624_ = v___y_3500_;
v___y_3625_ = v___y_3501_;
goto v___jp_3621_;
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3495_);
lean_dec(v_val_3494_);
lean_dec_ref(v_expectedType_3489_);
lean_dec_ref(v_inst_3488_);
v_a_3762_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3645_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3645_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
v___jp_3549_:
{
lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3555_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3556_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3553_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
lean_dec_ref(v_expectedType_3489_);
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_inst_3488_);
return v___x_3557_;
}
else
{
lean_object* v___x_3558_; 
lean_inc(v___y_3554_);
lean_inc_ref(v___y_3552_);
lean_inc(v___y_3551_);
lean_inc_ref(v___y_3550_);
lean_inc_ref(v_inst_3488_);
v___x_3558_ = lean_infer_type(v_inst_3488_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3554_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3560_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref(v___x_3558_);
lean_inc_ref(v_expectedType_3489_);
v___x_3560_ = l_Lean_Meta_isExprDefEq(v_expectedType_3489_, v_a_3559_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3554_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3611_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3563_ = v___x_3560_;
v_isShared_3564_ = v_isSharedCheck_3611_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3560_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3611_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
uint8_t v___x_3565_; 
v___x_3565_ = lean_unbox(v_a_3561_);
lean_dec(v_a_3561_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v_a_3568_; lean_object* v___x_3569_; 
lean_del_object(v___x_3563_);
v___x_3566_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_3567_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3566_, v___y_3554_);
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc_n(v_a_3568_, 2);
lean_dec_ref(v___x_3567_);
v___x_3569_ = l_Lean_Meta_mkAuxDefinition(v_a_3568_, v_expectedType_3489_, v_inst_3488_, v___x_3490_, v___x_3490_, v___x_3548_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3554_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = 3;
lean_inc(v_a_3568_);
v___x_3572_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3568_, v___x_3571_, v___y_3551_, v___y_3554_);
lean_dec_ref(v___x_3572_);
if (v_isMeta_3493_ == 0)
{
v___y_3526_ = v_a_3570_;
v___y_3527_ = v_a_3568_;
v___y_3528_ = v___y_3552_;
v___y_3529_ = v___y_3554_;
goto v___jp_3525_;
}
else
{
lean_object* v___x_3573_; lean_object* v_env_3574_; lean_object* v_nextMacroScope_3575_; lean_object* v_ngen_3576_; lean_object* v_auxDeclNGen_3577_; lean_object* v_traceState_3578_; lean_object* v_messages_3579_; lean_object* v_infoState_3580_; lean_object* v_snapshotTasks_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3606_; 
v___x_3573_ = lean_st_ref_take(v___y_3554_);
v_env_3574_ = lean_ctor_get(v___x_3573_, 0);
v_nextMacroScope_3575_ = lean_ctor_get(v___x_3573_, 1);
v_ngen_3576_ = lean_ctor_get(v___x_3573_, 2);
v_auxDeclNGen_3577_ = lean_ctor_get(v___x_3573_, 3);
v_traceState_3578_ = lean_ctor_get(v___x_3573_, 4);
v_messages_3579_ = lean_ctor_get(v___x_3573_, 6);
v_infoState_3580_ = lean_ctor_get(v___x_3573_, 7);
v_snapshotTasks_3581_ = lean_ctor_get(v___x_3573_, 8);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___x_3573_, 5);
lean_dec(v_unused_3607_);
v___x_3583_ = v___x_3573_;
v_isShared_3584_ = v_isSharedCheck_3606_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_snapshotTasks_3581_);
lean_inc(v_infoState_3580_);
lean_inc(v_messages_3579_);
lean_inc(v_traceState_3578_);
lean_inc(v_auxDeclNGen_3577_);
lean_inc(v_ngen_3576_);
lean_inc(v_nextMacroScope_3575_);
lean_inc(v_env_3574_);
lean_dec(v___x_3573_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3606_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
lean_inc(v_a_3568_);
v___x_3585_ = l_Lean_markMeta(v_env_3574_, v_a_3568_);
v___x_3586_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 5, v___x_3586_);
lean_ctor_set(v___x_3583_, 0, v___x_3585_);
v___x_3588_ = v___x_3583_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_nextMacroScope_3575_);
lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_ngen_3576_);
lean_ctor_set(v_reuseFailAlloc_3605_, 3, v_auxDeclNGen_3577_);
lean_ctor_set(v_reuseFailAlloc_3605_, 4, v_traceState_3578_);
lean_ctor_set(v_reuseFailAlloc_3605_, 5, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3605_, 6, v_messages_3579_);
lean_ctor_set(v_reuseFailAlloc_3605_, 7, v_infoState_3580_);
lean_ctor_set(v_reuseFailAlloc_3605_, 8, v_snapshotTasks_3581_);
v___x_3588_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v_mctx_3591_; lean_object* v_zetaDeltaFVarIds_3592_; lean_object* v_postponed_3593_; lean_object* v_diag_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3603_; 
v___x_3589_ = lean_st_ref_set(v___y_3554_, v___x_3588_);
v___x_3590_ = lean_st_ref_take(v___y_3551_);
v_mctx_3591_ = lean_ctor_get(v___x_3590_, 0);
v_zetaDeltaFVarIds_3592_ = lean_ctor_get(v___x_3590_, 2);
v_postponed_3593_ = lean_ctor_get(v___x_3590_, 3);
v_diag_3594_ = lean_ctor_get(v___x_3590_, 4);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3590_, 1);
lean_dec(v_unused_3604_);
v___x_3596_ = v___x_3590_;
v_isShared_3597_ = v_isSharedCheck_3603_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_diag_3594_);
lean_inc(v_postponed_3593_);
lean_inc(v_zetaDeltaFVarIds_3592_);
lean_inc(v_mctx_3591_);
lean_dec(v___x_3590_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3603_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; lean_object* v___x_3600_; 
v___x_3598_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v___x_3598_);
v___x_3600_ = v___x_3596_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_mctx_3591_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v___x_3598_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_zetaDeltaFVarIds_3592_);
lean_ctor_set(v_reuseFailAlloc_3602_, 3, v_postponed_3593_);
lean_ctor_set(v_reuseFailAlloc_3602_, 4, v_diag_3594_);
v___x_3600_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3601_; 
v___x_3601_ = lean_st_ref_set(v___y_3551_, v___x_3600_);
v___y_3526_ = v_a_3570_;
v___y_3527_ = v_a_3568_;
v___y_3528_ = v___y_3552_;
v___y_3529_ = v___y_3554_;
goto v___jp_3525_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3568_);
return v___x_3569_;
}
}
else
{
lean_object* v___x_3609_; 
lean_dec_ref(v_expectedType_3489_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v_inst_3488_);
v___x_3609_ = v___x_3563_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_inst_3488_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec_ref(v_expectedType_3489_);
lean_dec_ref(v_inst_3488_);
v_a_3612_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3560_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3560_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3489_);
lean_dec_ref(v_inst_3488_);
return v___x_3558_;
}
}
}
v___jp_3621_:
{
lean_object* v_options_3626_; uint8_t v_hasTrace_3627_; 
v_options_3626_ = lean_ctor_get(v___y_3624_, 2);
v_hasTrace_3627_ = lean_ctor_get_uint8(v_options_3626_, sizeof(void*)*1);
if (v_hasTrace_3627_ == 0)
{
v___y_3550_ = v___y_3622_;
v___y_3551_ = v___y_3623_;
v___y_3552_ = v___y_3624_;
v_options_3553_ = v_options_3626_;
v___y_3554_ = v___y_3625_;
goto v___jp_3549_;
}
else
{
lean_object* v_inheritedTraceOptions_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v_inheritedTraceOptions_3628_ = lean_ctor_get(v___y_3624_, 13);
v___x_3629_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_3630_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3628_, v_options_3626_, v___x_3629_);
if (v___x_3630_ == 0)
{
v___y_3550_ = v___y_3622_;
v___y_3551_ = v___y_3623_;
v___y_3552_ = v___y_3624_;
v_options_3553_ = v_options_3626_;
v___y_3554_ = v___y_3625_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3631_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1);
lean_inc_ref(v_inst_3488_);
v___x_3632_ = l_Lean_MessageData_ofExpr(v_inst_3488_);
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3631_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3620_, v___x_3633_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_dec_ref(v___x_3634_);
v___y_3550_ = v___y_3622_;
v___y_3551_ = v___y_3623_;
v___y_3552_ = v___y_3624_;
v_options_3553_ = v_options_3626_;
v___y_3554_ = v___y_3625_;
goto v___jp_3549_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_expectedType_3489_);
lean_dec_ref(v_inst_3488_);
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
}
}
v___jp_3503_:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_enableRealizationsForConst(v___y_3505_, v___y_3506_, v___y_3507_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; 
v_unused_3516_ = lean_ctor_get(v___x_3508_, 0);
lean_dec(v_unused_3516_);
v___x_3510_ = v___x_3508_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_dec(v___x_3508_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___y_3504_);
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___y_3504_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v___y_3504_);
v_a_3517_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3508_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3508_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
v___jp_3525_:
{
if (v_compile_3491_ == 0)
{
v___y_3504_ = v___y_3526_;
v___y_3505_ = v___y_3527_;
v___y_3506_ = v___y_3528_;
v___y_3507_ = v___y_3529_;
goto v___jp_3503_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3530_ = lean_unsigned_to_nat(1u);
v___x_3531_ = lean_mk_empty_array_with_capacity(v___x_3530_);
lean_inc(v___y_3527_);
v___x_3532_ = lean_array_push(v___x_3531_, v___y_3527_);
v___x_3533_ = l_Lean_compileDecls(v___x_3532_, v_logCompileErrors_3492_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_dec_ref(v___x_3533_);
v___y_3504_ = v___y_3526_;
v___y_3505_ = v___y_3527_;
v___y_3506_ = v___y_3528_;
v___y_3507_ = v___y_3529_;
goto v___jp_3503_;
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
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
}
}
static double _init_l_Lean_Meta_wrapInstance___closed__1(void){
_start:
{
lean_object* v___x_3770_; double v___x_3771_; 
v___x_3770_ = lean_unsigned_to_nat(1000000000u);
v___x_3771_ = lean_float_of_nat(v___x_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___redArg(lean_object* v_upperBound_3772_, lean_object* v_fst_3773_, lean_object* v_args_3774_, uint8_t v___x_3775_, uint8_t v_compile_3776_, uint8_t v_logCompileErrors_3777_, uint8_t v___x_3778_, uint8_t v_isMeta_3779_, lean_object* v_val_3780_, lean_object* v_expectedType_3781_, lean_object* v_a_3782_, lean_object* v_b_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_a_3790_; lean_object* v___y_3795_; uint8_t v___x_3814_; 
v___x_3814_ = lean_nat_dec_lt(v_a_3782_, v_upperBound_3772_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_b_3783_);
return v___x_3815_;
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = lean_array_fget_borrowed(v_fst_3773_, v_a_3782_);
v___x_3817_ = l_Lean_Expr_mvarId_x21(v___x_3816_);
lean_inc(v___x_3817_);
v___x_3818_ = l_Lean_MVarId_getDecl(v___x_3817_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v_userName_3820_; lean_object* v_type_3821_; lean_object* v___x_3822_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
v_userName_3820_ = lean_ctor_get(v_a_3819_, 0);
lean_inc(v_userName_3820_);
v_type_3821_ = lean_ctor_get(v_a_3819_, 2);
lean_inc_ref(v_type_3821_);
lean_dec(v_a_3819_);
v___x_3822_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_3821_, v___y_3785_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3824_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc_n(v_a_3823_, 2);
lean_dec_ref(v___x_3822_);
v___x_3824_ = l_Lean_Meta_isProp(v_a_3823_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; lean_object* v_cls_3827_; lean_object* v___f_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref(v___x_3824_);
v___x_3826_ = lean_box(0);
v_cls_3827_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3828_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0));
v___x_3829_ = lean_array_fget_borrowed(v_args_3774_, v_a_3782_);
v___x_3830_ = lean_unbox(v_a_3825_);
lean_dec(v_a_3825_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; 
lean_inc(v_a_3823_);
v___x_3831_ = l_Lean_Meta_isClass_x3f(v_a_3823_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3930_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3930_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3930_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v_a_3837_; lean_object* v___y_3840_; uint8_t v___y_3841_; lean_object* v_a_3846_; lean_object* v___y_3850_; 
if (lean_obj_tag(v_a_3832_) == 0)
{
if (v___x_3778_ == 0)
{
lean_object* v_options_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___f_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; 
lean_del_object(v___x_3834_);
v_options_3876_ = lean_ctor_get(v___y_3786_, 2);
v___x_3877_ = lean_box(v___x_3778_);
v___x_3878_ = lean_box(v___x_3775_);
v___x_3879_ = lean_box(v_compile_3776_);
v___x_3880_ = lean_box(v_logCompileErrors_3777_);
v___x_3881_ = lean_box(v_isMeta_3779_);
lean_inc(v_a_3823_);
lean_inc(v___x_3829_);
lean_inc(v___x_3817_);
v___f_3882_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3882_, 0, v___x_3817_);
lean_closure_set(v___f_3882_, 1, v___x_3829_);
lean_closure_set(v___f_3882_, 2, v___x_3826_);
lean_closure_set(v___f_3882_, 3, v_a_3823_);
lean_closure_set(v___f_3882_, 4, v___x_3877_);
lean_closure_set(v___f_3882_, 5, v___x_3878_);
lean_closure_set(v___f_3882_, 6, v___x_3879_);
lean_closure_set(v___f_3882_, 7, v___x_3880_);
lean_closure_set(v___f_3882_, 8, v___x_3881_);
v___x_3883_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3884_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3876_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_dec_ref(v___f_3882_);
lean_dec(v_userName_3820_);
lean_inc(v___x_3829_);
v___x_3885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_3817_, v___x_3829_, v___x_3826_, v_a_3823_, v___x_3778_, v___x_3775_, v_compile_3776_, v_logCompileErrors_3777_, v_isMeta_3779_, v___x_3826_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3885_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3886_; 
lean_inc(v_userName_3820_);
lean_inc(v_val_3780_);
v___x_3886_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_3780_, v_userName_3820_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v_fst_3888_; lean_object* v_snd_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3921_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref(v___x_3886_);
v_fst_3888_ = lean_ctor_get(v_a_3887_, 0);
v_snd_3889_ = lean_ctor_get(v_a_3887_, 1);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_a_3887_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3891_ = v_a_3887_;
v_isShared_3892_ = v_isSharedCheck_3921_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_snd_3889_);
lean_inc(v_fst_3888_);
lean_dec(v_a_3887_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3921_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
uint8_t v___x_3893_; 
v___x_3893_ = lean_name_eq(v_fst_3888_, v_val_3780_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
lean_dec(v_a_3823_);
v___x_3894_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_3827_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; uint8_t v___x_3896_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref(v___x_3894_);
v___x_3896_ = lean_unbox(v_a_3895_);
lean_dec(v_a_3895_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; 
lean_del_object(v___x_3891_);
lean_dec(v_userName_3820_);
lean_inc_ref(v_expectedType_3781_);
lean_inc(v_val_3780_);
v___x_3897_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(v_val_3780_, v_fst_3888_, v_expectedType_3781_, v___f_3828_, v___f_3882_, v___x_3826_, v_cls_3827_, v_snd_3889_, v___x_3817_, v___x_3826_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3897_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3898_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4);
v___x_3899_ = l_Lean_MessageData_ofName(v_userName_3820_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 7);
lean_ctor_set(v___x_3891_, 1, v___x_3899_);
lean_ctor_set(v___x_3891_, 0, v___x_3898_);
v___x_3901_ = v___x_3891_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3902_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6);
v___x_3903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3901_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
lean_inc(v_fst_3888_);
v___x_3904_ = l_Lean_MessageData_ofName(v_fst_3888_);
v___x_3905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3903_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
v___x_3906_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3827_, v___x_3907_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3908_);
lean_inc_ref(v_expectedType_3781_);
lean_inc(v_val_3780_);
v___x_3910_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(v_val_3780_, v_fst_3888_, v_expectedType_3781_, v___f_3828_, v___f_3882_, v___x_3826_, v_cls_3827_, v_snd_3889_, v___x_3817_, v_a_3909_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3910_;
goto v___jp_3794_;
}
else
{
lean_dec(v_snd_3889_);
lean_dec(v_fst_3888_);
lean_dec_ref(v___f_3882_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
return v___x_3908_;
}
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_del_object(v___x_3891_);
lean_dec(v_snd_3889_);
lean_dec(v_fst_3888_);
lean_dec_ref(v___f_3882_);
lean_dec(v_userName_3820_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3912_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3894_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3894_);
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
lean_del_object(v___x_3891_);
lean_dec(v_snd_3889_);
lean_dec(v_fst_3888_);
lean_dec_ref(v___f_3882_);
lean_dec(v_userName_3820_);
lean_inc(v___x_3829_);
v___x_3920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_3817_, v___x_3829_, v___x_3826_, v_a_3823_, v___x_3778_, v___x_3775_, v_compile_3776_, v_logCompileErrors_3777_, v_isMeta_3779_, v___x_3826_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3920_;
goto v___jp_3794_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec_ref(v___f_3882_);
lean_dec(v_a_3823_);
lean_dec(v_userName_3820_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3922_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3886_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3886_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
else
{
lean_dec(v_userName_3820_);
goto v___jp_3854_;
}
}
else
{
lean_dec_ref(v_a_3832_);
lean_dec(v_userName_3820_);
goto v___jp_3854_;
}
v___jp_3836_:
{
lean_object* v___x_3838_; 
lean_inc(v___x_3829_);
v___x_3838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_3829_, v_a_3823_, v_compile_3776_, v_logCompileErrors_3777_, v_isMeta_3779_, v___x_3817_, v___x_3826_, v_a_3837_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3838_;
goto v___jp_3794_;
}
v___jp_3839_:
{
if (v___y_3841_ == 0)
{
lean_dec_ref(v___y_3840_);
lean_del_object(v___x_3834_);
v_a_3837_ = v___x_3826_;
goto v___jp_3836_;
}
else
{
lean_object* v___x_3843_; 
lean_dec(v_a_3823_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set_tag(v___x_3834_, 1);
lean_ctor_set(v___x_3834_, 0, v___y_3840_);
v___x_3843_ = v___x_3834_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___y_3840_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
v___jp_3845_:
{
uint8_t v___x_3847_; 
v___x_3847_ = l_Lean_Exception_isInterrupt(v_a_3846_);
if (v___x_3847_ == 0)
{
uint8_t v___x_3848_; 
lean_inc_ref(v_a_3846_);
v___x_3848_ = l_Lean_Exception_isRuntime(v_a_3846_);
v___y_3840_ = v_a_3846_;
v___y_3841_ = v___x_3848_;
goto v___jp_3839_;
}
else
{
v___y_3840_ = v_a_3846_;
v___y_3841_ = v___x_3847_;
goto v___jp_3839_;
}
}
v___jp_3849_:
{
if (lean_obj_tag(v___y_3850_) == 0)
{
lean_object* v_a_3851_; 
lean_del_object(v___x_3834_);
v_a_3851_ = lean_ctor_get(v___y_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref(v___y_3850_);
if (lean_obj_tag(v_a_3851_) == 0)
{
lean_dec(v_a_3823_);
lean_dec(v___x_3817_);
v_a_3790_ = v___x_3826_;
goto v___jp_3789_;
}
else
{
lean_object* v_a_3852_; 
v_a_3852_ = lean_ctor_get(v_a_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref(v_a_3851_);
v_a_3837_ = v_a_3852_;
goto v___jp_3836_;
}
}
else
{
lean_object* v_a_3853_; 
v_a_3853_ = lean_ctor_get(v___y_3850_, 0);
lean_inc(v_a_3853_);
lean_dec_ref(v___y_3850_);
v_a_3846_ = v_a_3853_;
goto v___jp_3845_;
}
}
v___jp_3854_:
{
lean_object* v_options_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v_options_3855_ = lean_ctor_get(v___y_3786_, 2);
v___x_3856_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3857_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3855_, v___x_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; 
lean_del_object(v___x_3834_);
lean_inc(v___x_3829_);
v___x_3858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_3829_, v_a_3823_, v_compile_3776_, v_logCompileErrors_3777_, v_isMeta_3779_, v___x_3817_, v___x_3826_, v___x_3826_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3858_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_box(0);
lean_inc(v_a_3823_);
v___x_3860_ = l_Lean_Meta_trySynthInstance(v_a_3823_, v___x_3859_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3860_);
if (lean_obj_tag(v_a_3861_) == 1)
{
lean_object* v_a_3862_; lean_object* v___x_3863_; 
v_a_3862_ = lean_ctor_get(v_a_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref(v_a_3861_);
v___x_3863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_3827_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; uint8_t v___x_3865_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref(v___x_3863_);
v___x_3865_ = lean_unbox(v_a_3864_);
lean_dec(v_a_3864_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; 
lean_inc(v___x_3817_);
v___x_3866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_3817_, v_a_3862_, v___x_3826_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3850_ = v___x_3866_;
goto v___jp_3849_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3867_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2);
lean_inc(v_a_3862_);
v___x_3868_ = l_Lean_MessageData_ofExpr(v_a_3862_);
v___x_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3827_, v___x_3869_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
lean_inc(v___x_3817_);
v___x_3872_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_3817_, v_a_3862_, v_a_3871_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3850_ = v___x_3872_;
goto v___jp_3849_;
}
else
{
lean_object* v_a_3873_; 
lean_dec(v_a_3862_);
v_a_3873_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3873_);
lean_dec_ref(v___x_3870_);
v_a_3846_ = v_a_3873_;
goto v___jp_3845_;
}
}
}
else
{
lean_object* v_a_3874_; 
lean_dec(v_a_3862_);
v_a_3874_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3874_);
lean_dec_ref(v___x_3863_);
v_a_3846_ = v_a_3874_;
goto v___jp_3845_;
}
}
else
{
lean_dec(v_a_3861_);
lean_del_object(v___x_3834_);
v_a_3837_ = v___x_3826_;
goto v___jp_3836_;
}
}
else
{
lean_object* v_a_3875_; 
v_a_3875_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3860_);
v_a_3846_ = v_a_3875_;
goto v___jp_3845_;
}
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_a_3823_);
lean_dec(v_userName_3820_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3931_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3831_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3831_);
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
else
{
lean_object* v___x_3939_; 
lean_dec(v_userName_3820_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
lean_inc(v___y_3785_);
lean_inc_ref(v___y_3784_);
lean_inc(v___x_3829_);
v___x_3939_ = lean_infer_type(v___x_3829_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3941_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc_n(v_a_3940_, 2);
lean_dec_ref(v___x_3939_);
lean_inc(v_a_3823_);
v___x_3941_ = l_Lean_Meta_isExprDefEq(v_a_3823_, v_a_3940_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___f_3943_; uint8_t v___x_3944_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref(v___x_3941_);
v___f_3943_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__7));
v___x_3944_ = lean_unbox(v_a_3942_);
lean_dec(v_a_3942_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; 
v___x_3945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_3827_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; uint8_t v___x_3947_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref(v___x_3945_);
v___x_3947_ = lean_unbox(v_a_3946_);
lean_dec(v_a_3946_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; 
lean_dec(v_a_3940_);
lean_inc(v___x_3829_);
v___x_3948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_3823_, v___x_3829_, v___x_3775_, v___x_3817_, v___f_3943_, v___x_3826_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3948_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3949_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9);
lean_inc(v_a_3782_);
v___x_3950_ = l_Nat_reprFast(v_a_3782_);
v___x_3951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
v___x_3952_ = l_Lean_MessageData_ofFormat(v___x_3951_);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3949_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
lean_inc(v_a_3823_);
v___x_3956_ = l_Lean_MessageData_ofExpr(v_a_3823_);
v___x_3957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13);
v___x_3959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = l_Lean_MessageData_ofExpr(v_a_3940_);
v___x_3961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15);
v___x_3963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3961_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
lean_inc(v___x_3829_);
v___x_3964_ = l_Lean_MessageData_ofExpr(v___x_3829_);
v___x_3965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3963_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3827_, v___x_3965_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref(v___x_3966_);
lean_inc(v___x_3829_);
v___x_3968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_3823_, v___x_3829_, v___x_3775_, v___x_3817_, v___f_3943_, v_a_3967_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3968_;
goto v___jp_3794_;
}
else
{
lean_dec(v_a_3823_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
return v___x_3966_;
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v_a_3940_);
lean_dec(v_a_3823_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3969_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3945_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3945_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_object* v___x_3977_; 
lean_dec(v_a_3940_);
lean_dec(v_a_3823_);
lean_inc(v___x_3829_);
v___x_3977_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3817_, v___x_3829_, v___y_3785_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3979_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref(v___x_3977_);
v___x_3979_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6(v___x_3826_, v_a_3978_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v___y_3795_ = v___x_3979_;
goto v___jp_3794_;
}
else
{
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
return v___x_3977_;
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_a_3940_);
lean_dec(v_a_3823_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3980_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3941_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3941_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_a_3823_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3988_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3939_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3939_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec(v_a_3823_);
lean_dec(v_userName_3820_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3996_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3824_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3824_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec(v_userName_3820_);
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_4004_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3822_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3822_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec(v___x_3817_);
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_4012_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_3818_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_3818_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
v___jp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_unsigned_to_nat(1u);
v___x_3792_ = lean_nat_add(v_a_3782_, v___x_3791_);
lean_dec(v_a_3782_);
v_a_3782_ = v___x_3792_;
v_b_3783_ = v_a_3790_;
goto _start;
}
v___jp_3794_:
{
if (lean_obj_tag(v___y_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3805_; 
v_a_3796_ = lean_ctor_get(v___y_3795_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___y_3795_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3798_ = v___y_3795_;
v_isShared_3799_ = v_isSharedCheck_3805_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___y_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3805_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
if (lean_obj_tag(v_a_3796_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; 
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3800_ = lean_ctor_get(v_a_3796_, 0);
lean_inc(v_a_3800_);
lean_dec_ref(v_a_3796_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v_a_3800_);
v___x_3802_ = v___x_3798_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
else
{
lean_object* v_a_3804_; 
lean_del_object(v___x_3798_);
v_a_3804_ = lean_ctor_get(v_a_3796_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v_a_3796_);
v_a_3790_ = v_a_3804_;
goto v___jp_3789_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_a_3782_);
lean_dec_ref(v_expectedType_3781_);
lean_dec(v_val_3780_);
v_a_3806_ = lean_ctor_get(v___y_3795_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___y_3795_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___y_3795_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___y_3795_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object* v_upperBound_4020_, lean_object* v_fst_4021_, lean_object* v_args_4022_, uint8_t v___x_4023_, uint8_t v_compile_4024_, uint8_t v_logCompileErrors_4025_, uint8_t v___x_4026_, uint8_t v_isMeta_4027_, lean_object* v_val_4028_, lean_object* v_expectedType_4029_, lean_object* v_a_4030_, lean_object* v_b_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_a_4038_; lean_object* v___y_4043_; uint8_t v___x_4062_; 
v___x_4062_ = lean_nat_dec_lt(v_a_4030_, v_upperBound_4020_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; 
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v_b_4031_);
return v___x_4063_;
}
else
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4064_ = lean_array_fget_borrowed(v_fst_4021_, v_a_4030_);
v___x_4065_ = l_Lean_Expr_mvarId_x21(v___x_4064_);
lean_inc(v___x_4065_);
v___x_4066_ = l_Lean_MVarId_getDecl(v___x_4065_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v_userName_4068_; lean_object* v_type_4069_; lean_object* v___x_4070_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref(v___x_4066_);
v_userName_4068_ = lean_ctor_get(v_a_4067_, 0);
lean_inc(v_userName_4068_);
v_type_4069_ = lean_ctor_get(v_a_4067_, 2);
lean_inc_ref(v_type_4069_);
lean_dec(v_a_4067_);
v___x_4070_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_4069_, v___y_4033_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc_n(v_a_4071_, 2);
lean_dec_ref(v___x_4070_);
v___x_4072_ = l_Lean_Meta_isProp(v_a_4071_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4074_; lean_object* v_cls_4075_; lean_object* v___f_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref(v___x_4072_);
v___x_4074_ = lean_box(0);
v_cls_4075_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_4076_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0));
v___x_4077_ = lean_array_fget_borrowed(v_args_4022_, v_a_4030_);
v___x_4078_ = lean_unbox(v_a_4073_);
lean_dec(v_a_4073_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; 
lean_inc(v_a_4071_);
v___x_4079_ = l_Lean_Meta_isClass_x3f(v_a_4071_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4178_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4178_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4178_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v_a_4085_; lean_object* v___y_4088_; uint8_t v___y_4089_; lean_object* v_a_4094_; lean_object* v___y_4098_; 
if (lean_obj_tag(v_a_4080_) == 0)
{
if (v___x_4026_ == 0)
{
lean_object* v_options_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___f_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
lean_del_object(v___x_4082_);
v_options_4124_ = lean_ctor_get(v___y_4034_, 2);
v___x_4125_ = lean_box(v___x_4026_);
v___x_4126_ = lean_box(v___x_4023_);
v___x_4127_ = lean_box(v_compile_4024_);
v___x_4128_ = lean_box(v_logCompileErrors_4025_);
v___x_4129_ = lean_box(v_isMeta_4027_);
lean_inc(v_a_4071_);
lean_inc(v___x_4077_);
lean_inc(v___x_4065_);
v___f_4130_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_4130_, 0, v___x_4065_);
lean_closure_set(v___f_4130_, 1, v___x_4077_);
lean_closure_set(v___f_4130_, 2, v___x_4074_);
lean_closure_set(v___f_4130_, 3, v_a_4071_);
lean_closure_set(v___f_4130_, 4, v___x_4125_);
lean_closure_set(v___f_4130_, 5, v___x_4126_);
lean_closure_set(v___f_4130_, 6, v___x_4127_);
lean_closure_set(v___f_4130_, 7, v___x_4128_);
lean_closure_set(v___f_4130_, 8, v___x_4129_);
v___x_4131_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4132_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4124_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; 
lean_dec_ref(v___f_4130_);
lean_dec(v_userName_4068_);
lean_inc(v___x_4077_);
v___x_4133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4065_, v___x_4077_, v___x_4074_, v_a_4071_, v___x_4026_, v___x_4023_, v_compile_4024_, v_logCompileErrors_4025_, v_isMeta_4027_, v___x_4074_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4133_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4134_; 
lean_inc(v_userName_4068_);
lean_inc(v_val_4028_);
v___x_4134_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_4028_, v_userName_4068_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v_fst_4136_; lean_object* v_snd_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4169_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref(v___x_4134_);
v_fst_4136_ = lean_ctor_get(v_a_4135_, 0);
v_snd_4137_ = lean_ctor_get(v_a_4135_, 1);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_a_4135_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4139_ = v_a_4135_;
v_isShared_4140_ = v_isSharedCheck_4169_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_snd_4137_);
lean_inc(v_fst_4136_);
lean_dec(v_a_4135_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4169_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
uint8_t v___x_4141_; 
v___x_4141_ = lean_name_eq(v_fst_4136_, v_val_4028_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; 
lean_dec(v_a_4071_);
v___x_4142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_4075_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; uint8_t v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = lean_unbox(v_a_4143_);
lean_dec(v_a_4143_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; 
lean_del_object(v___x_4139_);
lean_dec(v_userName_4068_);
lean_inc_ref(v_expectedType_4029_);
lean_inc(v_val_4028_);
v___x_4145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(v_val_4028_, v_fst_4136_, v_expectedType_4029_, v___f_4076_, v___f_4130_, v___x_4074_, v_cls_4075_, v_snd_4137_, v___x_4065_, v___x_4074_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4145_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4149_; 
v___x_4146_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4);
v___x_4147_ = l_Lean_MessageData_ofName(v_userName_4068_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set_tag(v___x_4139_, 7);
lean_ctor_set(v___x_4139_, 1, v___x_4147_);
lean_ctor_set(v___x_4139_, 0, v___x_4146_);
v___x_4149_ = v___x_4139_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4146_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v___x_4147_);
v___x_4149_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4150_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6);
v___x_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
lean_inc(v_fst_4136_);
v___x_4152_ = l_Lean_MessageData_ofName(v_fst_4136_);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4151_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4075_, v___x_4155_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref(v___x_4156_);
lean_inc_ref(v_expectedType_4029_);
lean_inc(v_val_4028_);
v___x_4158_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(v_val_4028_, v_fst_4136_, v_expectedType_4029_, v___f_4076_, v___f_4130_, v___x_4074_, v_cls_4075_, v_snd_4137_, v___x_4065_, v_a_4157_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4158_;
goto v___jp_4042_;
}
else
{
lean_dec(v_snd_4137_);
lean_dec(v_fst_4136_);
lean_dec_ref(v___f_4130_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
return v___x_4156_;
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_del_object(v___x_4139_);
lean_dec(v_snd_4137_);
lean_dec(v_fst_4136_);
lean_dec_ref(v___f_4130_);
lean_dec(v_userName_4068_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4160_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4142_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4142_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
else
{
lean_object* v___x_4168_; 
lean_del_object(v___x_4139_);
lean_dec(v_snd_4137_);
lean_dec(v_fst_4136_);
lean_dec_ref(v___f_4130_);
lean_dec(v_userName_4068_);
lean_inc(v___x_4077_);
v___x_4168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4065_, v___x_4077_, v___x_4074_, v_a_4071_, v___x_4026_, v___x_4023_, v_compile_4024_, v_logCompileErrors_4025_, v_isMeta_4027_, v___x_4074_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4168_;
goto v___jp_4042_;
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v___f_4130_);
lean_dec(v_a_4071_);
lean_dec(v_userName_4068_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4170_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4134_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4134_);
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
else
{
lean_dec(v_userName_4068_);
goto v___jp_4102_;
}
}
else
{
lean_dec_ref(v_a_4080_);
lean_dec(v_userName_4068_);
goto v___jp_4102_;
}
v___jp_4084_:
{
lean_object* v___x_4086_; 
lean_inc(v___x_4077_);
v___x_4086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_4077_, v_a_4071_, v_compile_4024_, v_logCompileErrors_4025_, v_isMeta_4027_, v___x_4065_, v___x_4074_, v_a_4085_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4086_;
goto v___jp_4042_;
}
v___jp_4087_:
{
if (v___y_4089_ == 0)
{
lean_dec_ref(v___y_4088_);
lean_del_object(v___x_4082_);
v_a_4085_ = v___x_4074_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4091_; 
lean_dec(v_a_4071_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set_tag(v___x_4082_, 1);
lean_ctor_set(v___x_4082_, 0, v___y_4088_);
v___x_4091_ = v___x_4082_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___y_4088_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
v___jp_4093_:
{
uint8_t v___x_4095_; 
v___x_4095_ = l_Lean_Exception_isInterrupt(v_a_4094_);
if (v___x_4095_ == 0)
{
uint8_t v___x_4096_; 
lean_inc_ref(v_a_4094_);
v___x_4096_ = l_Lean_Exception_isRuntime(v_a_4094_);
v___y_4088_ = v_a_4094_;
v___y_4089_ = v___x_4096_;
goto v___jp_4087_;
}
else
{
v___y_4088_ = v_a_4094_;
v___y_4089_ = v___x_4095_;
goto v___jp_4087_;
}
}
v___jp_4097_:
{
if (lean_obj_tag(v___y_4098_) == 0)
{
lean_object* v_a_4099_; 
lean_del_object(v___x_4082_);
v_a_4099_ = lean_ctor_get(v___y_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref(v___y_4098_);
if (lean_obj_tag(v_a_4099_) == 0)
{
lean_dec(v_a_4071_);
lean_dec(v___x_4065_);
v_a_4038_ = v___x_4074_;
goto v___jp_4037_;
}
else
{
lean_object* v_a_4100_; 
v_a_4100_ = lean_ctor_get(v_a_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v_a_4099_);
v_a_4085_ = v_a_4100_;
goto v___jp_4084_;
}
}
else
{
lean_object* v_a_4101_; 
v_a_4101_ = lean_ctor_get(v___y_4098_, 0);
lean_inc(v_a_4101_);
lean_dec_ref(v___y_4098_);
v_a_4094_ = v_a_4101_;
goto v___jp_4093_;
}
}
v___jp_4102_:
{
lean_object* v_options_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_options_4103_ = lean_ctor_get(v___y_4034_, 2);
v___x_4104_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4105_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4103_, v___x_4104_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4106_; 
lean_del_object(v___x_4082_);
lean_inc(v___x_4077_);
v___x_4106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_4077_, v_a_4071_, v_compile_4024_, v_logCompileErrors_4025_, v_isMeta_4027_, v___x_4065_, v___x_4074_, v___x_4074_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4106_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = lean_box(0);
lean_inc(v_a_4071_);
v___x_4108_ = l_Lean_Meta_trySynthInstance(v_a_4071_, v___x_4107_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref(v___x_4108_);
if (lean_obj_tag(v_a_4109_) == 1)
{
lean_object* v_a_4110_; lean_object* v___x_4111_; 
v_a_4110_ = lean_ctor_get(v_a_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref(v_a_4109_);
v___x_4111_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_4075_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; uint8_t v___x_4113_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref(v___x_4111_);
v___x_4113_ = lean_unbox(v_a_4112_);
lean_dec(v_a_4112_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; 
lean_inc(v___x_4065_);
v___x_4114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_4065_, v_a_4110_, v___x_4074_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4098_ = v___x_4114_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4115_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2);
lean_inc(v_a_4110_);
v___x_4116_ = l_Lean_MessageData_ofExpr(v_a_4110_);
v___x_4117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4075_, v___x_4117_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4120_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref(v___x_4118_);
lean_inc(v___x_4065_);
v___x_4120_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_4065_, v_a_4110_, v_a_4119_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4098_ = v___x_4120_;
goto v___jp_4097_;
}
else
{
lean_object* v_a_4121_; 
lean_dec(v_a_4110_);
v_a_4121_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4121_);
lean_dec_ref(v___x_4118_);
v_a_4094_ = v_a_4121_;
goto v___jp_4093_;
}
}
}
else
{
lean_object* v_a_4122_; 
lean_dec(v_a_4110_);
v_a_4122_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4122_);
lean_dec_ref(v___x_4111_);
v_a_4094_ = v_a_4122_;
goto v___jp_4093_;
}
}
else
{
lean_dec(v_a_4109_);
lean_del_object(v___x_4082_);
v_a_4085_ = v___x_4074_;
goto v___jp_4084_;
}
}
else
{
lean_object* v_a_4123_; 
v_a_4123_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4123_);
lean_dec_ref(v___x_4108_);
v_a_4094_ = v_a_4123_;
goto v___jp_4093_;
}
}
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec(v_a_4071_);
lean_dec(v_userName_4068_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4179_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4079_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4079_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
else
{
lean_object* v___x_4187_; 
lean_dec(v_userName_4068_);
lean_inc(v___y_4035_);
lean_inc_ref(v___y_4034_);
lean_inc(v___y_4033_);
lean_inc_ref(v___y_4032_);
lean_inc(v___x_4077_);
v___x_4187_ = lean_infer_type(v___x_4077_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4189_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc_n(v_a_4188_, 2);
lean_dec_ref(v___x_4187_);
lean_inc(v_a_4071_);
v___x_4189_ = l_Lean_Meta_isExprDefEq(v_a_4071_, v_a_4188_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___f_4191_; uint8_t v___x_4192_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref(v___x_4189_);
v___f_4191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__7));
v___x_4192_ = lean_unbox(v_a_4190_);
lean_dec(v_a_4190_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; 
v___x_4193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_4075_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; uint8_t v___x_4195_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref(v___x_4193_);
v___x_4195_ = lean_unbox(v_a_4194_);
lean_dec(v_a_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
lean_dec(v_a_4188_);
lean_inc(v___x_4077_);
v___x_4196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_4071_, v___x_4077_, v___x_4023_, v___x_4065_, v___f_4191_, v___x_4074_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4196_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4197_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9);
lean_inc(v_a_4030_);
v___x_4198_ = l_Nat_reprFast(v_a_4030_);
v___x_4199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
v___x_4200_ = l_Lean_MessageData_ofFormat(v___x_4199_);
v___x_4201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4197_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11);
v___x_4203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
lean_inc(v_a_4071_);
v___x_4204_ = l_Lean_MessageData_ofExpr(v_a_4071_);
v___x_4205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4203_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v___x_4206_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13);
v___x_4207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = l_Lean_MessageData_ofExpr(v_a_4188_);
v___x_4209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4207_);
lean_ctor_set(v___x_4209_, 1, v___x_4208_);
v___x_4210_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15);
v___x_4211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
lean_inc(v___x_4077_);
v___x_4212_ = l_Lean_MessageData_ofExpr(v___x_4077_);
v___x_4213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4075_, v___x_4213_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4216_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref(v___x_4214_);
lean_inc(v___x_4077_);
v___x_4216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_4071_, v___x_4077_, v___x_4023_, v___x_4065_, v___f_4191_, v_a_4215_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4216_;
goto v___jp_4042_;
}
else
{
lean_dec(v_a_4071_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
return v___x_4214_;
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v_a_4188_);
lean_dec(v_a_4071_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4217_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4193_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4193_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v___x_4225_; 
lean_dec(v_a_4188_);
lean_dec(v_a_4071_);
lean_inc(v___x_4077_);
v___x_4225_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4065_, v___x_4077_, v___y_4033_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref(v___x_4225_);
v___x_4227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6(v___x_4074_, v_a_4226_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4227_;
goto v___jp_4042_;
}
else
{
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
return v___x_4225_;
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec(v_a_4188_);
lean_dec(v_a_4071_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4228_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4189_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4189_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_a_4071_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4236_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4187_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4187_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec(v_a_4071_);
lean_dec(v_userName_4068_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4244_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4072_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4072_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_userName_4068_);
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4252_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4070_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4070_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec(v___x_4065_);
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4260_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4066_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4066_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
v___jp_4037_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4039_ = lean_unsigned_to_nat(1u);
v___x_4040_ = lean_nat_add(v_a_4030_, v___x_4039_);
lean_dec(v_a_4030_);
v___x_4041_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___redArg(v_upperBound_4020_, v_fst_4021_, v_args_4022_, v___x_4023_, v_compile_4024_, v_logCompileErrors_4025_, v___x_4026_, v_isMeta_4027_, v_val_4028_, v_expectedType_4029_, v___x_4040_, v_a_4038_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
return v___x_4041_;
}
v___jp_4042_:
{
if (lean_obj_tag(v___y_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4053_; 
v_a_4044_ = lean_ctor_get(v___y_4043_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___y_4043_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4046_ = v___y_4043_;
v_isShared_4047_ = v_isSharedCheck_4053_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___y_4043_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4053_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
if (lean_obj_tag(v_a_4044_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; 
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4048_ = lean_ctor_get(v_a_4044_, 0);
lean_inc(v_a_4048_);
lean_dec_ref(v_a_4044_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v_a_4048_);
v___x_4050_ = v___x_4046_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
else
{
lean_object* v_a_4052_; 
lean_del_object(v___x_4046_);
v_a_4052_ = lean_ctor_get(v_a_4044_, 0);
lean_inc(v_a_4052_);
lean_dec_ref(v_a_4044_);
v_a_4038_ = v_a_4052_;
goto v___jp_4037_;
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec(v_a_4030_);
lean_dec_ref(v_expectedType_4029_);
lean_dec(v_val_4028_);
v_a_4054_ = lean_ctor_get(v___y_4043_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___y_4043_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___y_4043_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___y_4043_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19(lean_object* v_inst_4268_, lean_object* v_expectedType_4269_, uint8_t v___x_4270_, uint8_t v___x_4271_, uint8_t v_compile_4272_, uint8_t v_logCompileErrors_4273_, uint8_t v_isMeta_4274_, lean_object* v_val_4275_, lean_object* v_x_4276_, lean_object* v_x_4277_, lean_object* v_x_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v_options_4327_; lean_object* v___y_4328_; 
if (lean_obj_tag(v_x_4276_) == 5)
{
lean_object* v_fn_4394_; lean_object* v_arg_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_fn_4394_ = lean_ctor_get(v_x_4276_, 0);
lean_inc_ref(v_fn_4394_);
v_arg_4395_ = lean_ctor_get(v_x_4276_, 1);
lean_inc_ref(v_arg_4395_);
lean_dec_ref(v_x_4276_);
v___x_4396_ = lean_array_set(v_x_4277_, v_x_4278_, v_arg_4395_);
v___x_4397_ = lean_unsigned_to_nat(1u);
v___x_4398_ = lean_nat_sub(v_x_4278_, v___x_4397_);
lean_dec(v_x_4278_);
v_x_4276_ = v_fn_4394_;
v_x_4277_ = v___x_4396_;
v_x_4278_ = v___x_4398_;
goto _start;
}
else
{
lean_object* v_cls_4400_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___x_4423_; 
lean_dec(v_x_4278_);
v_cls_4400_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4423_ = l_Lean_Expr_constName_x3f(v_x_4276_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_dec_ref(v_x_4277_);
lean_dec_ref(v_x_4276_);
lean_dec(v_val_4275_);
v___y_4402_ = v___y_4279_;
v___y_4403_ = v___y_4280_;
v___y_4404_ = v___y_4281_;
v___y_4405_ = v___y_4282_;
goto v___jp_4401_;
}
else
{
lean_object* v_val_4424_; lean_object* v___x_4425_; 
v_val_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_val_4424_);
lean_dec_ref(v___x_4423_);
v___x_4425_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4424_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref(v___x_4425_);
if (lean_obj_tag(v_a_4426_) == 6)
{
lean_object* v_val_4427_; lean_object* v___x_4428_; 
lean_dec_ref(v_inst_4268_);
v_val_4427_ = lean_ctor_get(v_a_4426_, 0);
lean_inc_ref(v_val_4427_);
lean_dec_ref(v_a_4426_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
lean_inc(v___y_4280_);
lean_inc_ref(v___y_4279_);
lean_inc_ref(v_x_4276_);
v___x_4428_ = lean_infer_type(v_x_4276_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; uint8_t v___x_4430_; lean_object* v___x_4431_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_a_4429_);
lean_dec_ref(v___x_4428_);
v___x_4430_ = 0;
v___x_4431_ = l_Lean_Meta_forallMetaTelescope(v_a_4429_, v___x_4430_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v_snd_4433_; lean_object* v_fst_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4533_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref(v___x_4431_);
v_snd_4433_ = lean_ctor_get(v_a_4432_, 1);
v_fst_4434_ = lean_ctor_get(v_a_4432_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_a_4432_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4436_ = v_a_4432_;
v_isShared_4437_ = v_isSharedCheck_4533_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_snd_4433_);
lean_inc(v_fst_4434_);
lean_dec(v_a_4432_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4533_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v_snd_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4531_; 
v_snd_4438_ = lean_ctor_get(v_snd_4433_, 1);
v_isSharedCheck_4531_ = !lean_is_exclusive(v_snd_4433_);
if (v_isSharedCheck_4531_ == 0)
{
lean_object* v_unused_4532_; 
v_unused_4532_ = lean_ctor_get(v_snd_4433_, 0);
lean_dec(v_unused_4532_);
v___x_4440_ = v_snd_4433_;
v_isShared_4441_ = v_isSharedCheck_4531_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_snd_4438_);
lean_dec(v_snd_4433_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4531_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4442_ = lean_array_get_size(v_x_4277_);
v___x_4479_ = lean_array_get_size(v_fst_4434_);
v___x_4480_ = lean_nat_dec_eq(v___x_4442_, v___x_4479_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
lean_dec(v_snd_4438_);
lean_dec(v_fst_4434_);
lean_dec_ref(v_val_4427_);
lean_dec(v_val_4275_);
lean_dec_ref(v_expectedType_4269_);
v___x_4481_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3);
v___x_4482_ = l_Lean_MessageData_ofExpr(v_x_4276_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set_tag(v___x_4440_, 7);
lean_ctor_set(v___x_4440_, 1, v___x_4482_);
lean_ctor_set(v___x_4440_, 0, v___x_4481_);
v___x_4484_ = v___x_4440_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4485_; lean_object* v___x_4487_; 
v___x_4485_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
if (v_isShared_4437_ == 0)
{
lean_ctor_set_tag(v___x_4436_, 7);
lean_ctor_set(v___x_4436_, 1, v___x_4485_);
lean_ctor_set(v___x_4436_, 0, v___x_4484_);
v___x_4487_ = v___x_4436_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4488_ = lean_array_to_list(v_x_4277_);
v___x_4489_ = lean_box(0);
v___x_4490_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(v___x_4488_, v___x_4489_);
v___x_4491_ = l_Lean_MessageData_ofList(v___x_4490_);
v___x_4492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4487_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
v___x_4493_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4492_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4493_;
}
}
}
else
{
lean_object* v___x_4496_; 
lean_inc_ref(v_expectedType_4269_);
v___x_4496_ = l_Lean_Meta_isExprDefEq(v_expectedType_4269_, v_snd_4438_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; uint8_t v___x_4498_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref(v___x_4496_);
v___x_4498_ = lean_unbox(v_a_4497_);
lean_dec(v_a_4497_);
if (v___x_4498_ == 0)
{
lean_object* v_toConstantVal_4499_; lean_object* v_name_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
lean_dec(v_fst_4434_);
lean_dec_ref(v_x_4277_);
lean_dec_ref(v_x_4276_);
lean_dec(v_val_4275_);
v_toConstantVal_4499_ = lean_ctor_get(v_val_4427_, 0);
lean_inc_ref(v_toConstantVal_4499_);
lean_dec_ref(v_val_4427_);
v_name_4500_ = lean_ctor_get(v_toConstantVal_4499_, 0);
lean_inc(v_name_4500_);
lean_dec_ref(v_toConstantVal_4499_);
v___x_4501_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5);
v___x_4502_ = l_Lean_MessageData_ofExpr(v_expectedType_4269_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set_tag(v___x_4440_, 7);
lean_ctor_set(v___x_4440_, 1, v___x_4502_);
lean_ctor_set(v___x_4440_, 0, v___x_4501_);
v___x_4504_ = v___x_4440_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4522_, 1, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4505_; lean_object* v___x_4507_; 
v___x_4505_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7);
if (v_isShared_4437_ == 0)
{
lean_ctor_set_tag(v___x_4436_, 7);
lean_ctor_set(v___x_4436_, 1, v___x_4505_);
lean_ctor_set(v___x_4436_, 0, v___x_4504_);
v___x_4507_ = v___x_4436_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4504_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
v___x_4508_ = l_Lean_MessageData_ofConstName(v_name_4500_, v___x_4270_);
v___x_4509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4507_);
lean_ctor_set(v___x_4509_, 1, v___x_4508_);
v___x_4510_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_4511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4509_);
lean_ctor_set(v___x_4511_, 1, v___x_4510_);
v___x_4512_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4511_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4512_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4512_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
else
{
lean_del_object(v___x_4440_);
lean_del_object(v___x_4436_);
v___y_4444_ = v___y_4279_;
v___y_4445_ = v___y_4280_;
v___y_4446_ = v___y_4281_;
v___y_4447_ = v___y_4282_;
goto v___jp_4443_;
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_del_object(v___x_4440_);
lean_del_object(v___x_4436_);
lean_dec(v_fst_4434_);
lean_dec_ref(v_val_4427_);
lean_dec_ref(v_x_4277_);
lean_dec_ref(v_x_4276_);
lean_dec(v_val_4275_);
lean_dec_ref(v_expectedType_4269_);
v_a_4523_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4496_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4496_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
v___jp_4443_:
{
lean_object* v_numParams_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v_numParams_4448_ = lean_ctor_get(v_val_4427_, 3);
lean_inc(v_numParams_4448_);
lean_dec_ref(v_val_4427_);
v___x_4449_ = lean_box(0);
v___x_4450_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___x_4442_, v_fst_4434_, v_x_4277_, v___x_4271_, v_compile_4272_, v_logCompileErrors_4273_, v___x_4270_, v_isMeta_4274_, v_val_4275_, v_expectedType_4269_, v_numParams_4448_, v___x_4449_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
lean_dec_ref(v_x_4277_);
if (lean_obj_tag(v___x_4450_) == 0)
{
size_t v_sz_4451_; size_t v___x_4452_; lean_object* v___x_4453_; 
lean_dec_ref(v___x_4450_);
v_sz_4451_ = lean_array_size(v_fst_4434_);
v___x_4452_ = ((size_t)0ULL);
v___x_4453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_4451_, v___x_4452_, v_fst_4434_, v___y_4445_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4462_; 
v_a_4454_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4456_ = v___x_4453_;
v_isShared_4457_ = v_isSharedCheck_4462_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4453_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4462_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4458_; lean_object* v___x_4460_; 
v___x_4458_ = l_Lean_mkAppN(v_x_4276_, v_a_4454_);
lean_dec(v_a_4454_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 0, v___x_4458_);
v___x_4460_ = v___x_4456_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4458_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec_ref(v_x_4276_);
v_a_4463_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4453_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4453_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec(v_fst_4434_);
lean_dec_ref(v_x_4276_);
v_a_4471_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4450_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4450_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v_val_4427_);
lean_dec_ref(v_x_4277_);
lean_dec_ref(v_x_4276_);
lean_dec(v_val_4275_);
lean_dec_ref(v_expectedType_4269_);
v_a_4534_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4431_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4431_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
else
{
lean_dec_ref(v_val_4427_);
lean_dec_ref(v_x_4277_);
lean_dec_ref(v_x_4276_);
lean_dec(v_val_4275_);
lean_dec_ref(v_expectedType_4269_);
return v___x_4428_;
}
}
else
{
lean_dec(v_a_4426_);
lean_dec_ref(v_x_4277_);
lean_dec_ref(v_x_4276_);
lean_dec(v_val_4275_);
v___y_4402_ = v___y_4279_;
v___y_4403_ = v___y_4280_;
v___y_4404_ = v___y_4281_;
v___y_4405_ = v___y_4282_;
goto v___jp_4401_;
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_dec_ref(v_x_4277_);
lean_dec_ref(v_x_4276_);
lean_dec(v_val_4275_);
lean_dec_ref(v_expectedType_4269_);
lean_dec_ref(v_inst_4268_);
v_a_4542_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4425_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4425_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
v___jp_4401_:
{
lean_object* v_options_4406_; uint8_t v_hasTrace_4407_; 
v_options_4406_ = lean_ctor_get(v___y_4404_, 2);
v_hasTrace_4407_ = lean_ctor_get_uint8(v_options_4406_, sizeof(void*)*1);
if (v_hasTrace_4407_ == 0)
{
v___y_4324_ = v___y_4402_;
v___y_4325_ = v___y_4403_;
v___y_4326_ = v___y_4404_;
v_options_4327_ = v_options_4406_;
v___y_4328_ = v___y_4405_;
goto v___jp_4323_;
}
else
{
lean_object* v_inheritedTraceOptions_4408_; lean_object* v___x_4409_; uint8_t v___x_4410_; 
v_inheritedTraceOptions_4408_ = lean_ctor_get(v___y_4404_, 13);
v___x_4409_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_4410_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4408_, v_options_4406_, v___x_4409_);
if (v___x_4410_ == 0)
{
v___y_4324_ = v___y_4402_;
v___y_4325_ = v___y_4403_;
v___y_4326_ = v___y_4404_;
v_options_4327_ = v_options_4406_;
v___y_4328_ = v___y_4405_;
goto v___jp_4323_;
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4411_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1);
lean_inc_ref(v_inst_4268_);
v___x_4412_ = l_Lean_MessageData_ofExpr(v_inst_4268_);
v___x_4413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4411_);
lean_ctor_set(v___x_4413_, 1, v___x_4412_);
v___x_4414_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4400_, v___x_4413_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_dec_ref(v___x_4414_);
v___y_4324_ = v___y_4402_;
v___y_4325_ = v___y_4403_;
v___y_4326_ = v___y_4404_;
v_options_4327_ = v_options_4406_;
v___y_4328_ = v___y_4405_;
goto v___jp_4323_;
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec_ref(v_expectedType_4269_);
lean_dec_ref(v_inst_4268_);
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
}
}
v___jp_4284_:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Lean_enableRealizationsForConst(v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; 
v_unused_4297_ = lean_ctor_get(v___x_4289_, 0);
lean_dec(v_unused_4297_);
v___x_4291_ = v___x_4289_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_dec(v___x_4289_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v___y_4285_);
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___y_4285_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec_ref(v___y_4285_);
v_a_4298_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4289_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4289_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
v___jp_4306_:
{
if (v_compile_4272_ == 0)
{
v___y_4285_ = v___y_4307_;
v___y_4286_ = v___y_4308_;
v___y_4287_ = v___y_4309_;
v___y_4288_ = v___y_4310_;
goto v___jp_4284_;
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4311_ = lean_unsigned_to_nat(1u);
v___x_4312_ = lean_mk_empty_array_with_capacity(v___x_4311_);
lean_inc(v___y_4308_);
v___x_4313_ = lean_array_push(v___x_4312_, v___y_4308_);
v___x_4314_ = l_Lean_compileDecls(v___x_4313_, v_logCompileErrors_4273_, v___y_4309_, v___y_4310_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_dec_ref(v___x_4314_);
v___y_4285_ = v___y_4307_;
v___y_4286_ = v___y_4308_;
v___y_4287_ = v___y_4309_;
v___y_4288_ = v___y_4310_;
goto v___jp_4284_;
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
}
v___jp_4323_:
{
lean_object* v___x_4329_; uint8_t v___x_4330_; 
v___x_4329_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4330_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4327_, v___x_4329_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4331_; 
lean_dec_ref(v_expectedType_4269_);
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v_inst_4268_);
return v___x_4331_;
}
else
{
lean_object* v___x_4332_; 
lean_inc(v___y_4328_);
lean_inc_ref(v___y_4326_);
lean_inc(v___y_4325_);
lean_inc_ref(v___y_4324_);
lean_inc_ref(v_inst_4268_);
v___x_4332_ = lean_infer_type(v_inst_4268_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4328_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4334_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref(v___x_4332_);
lean_inc_ref(v_expectedType_4269_);
v___x_4334_ = l_Lean_Meta_isExprDefEq(v_expectedType_4269_, v_a_4333_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4328_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4385_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4337_ = v___x_4334_;
v_isShared_4338_ = v_isSharedCheck_4385_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4334_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4385_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
uint8_t v___x_4339_; 
v___x_4339_ = lean_unbox(v_a_4335_);
lean_dec(v_a_4335_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v_a_4342_; lean_object* v___x_4343_; 
lean_del_object(v___x_4337_);
v___x_4340_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_4341_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4340_, v___y_4328_);
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
lean_inc_n(v_a_4342_, 2);
lean_dec_ref(v___x_4341_);
v___x_4343_ = l_Lean_Meta_mkAuxDefinition(v_a_4342_, v_expectedType_4269_, v_inst_4268_, v___x_4270_, v___x_4270_, v___x_4271_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4328_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; uint8_t v___x_4345_; lean_object* v___x_4346_; 
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4344_);
lean_dec_ref(v___x_4343_);
v___x_4345_ = 3;
lean_inc(v_a_4342_);
v___x_4346_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4342_, v___x_4345_, v___y_4325_, v___y_4328_);
lean_dec_ref(v___x_4346_);
if (v_isMeta_4274_ == 0)
{
v___y_4307_ = v_a_4344_;
v___y_4308_ = v_a_4342_;
v___y_4309_ = v___y_4326_;
v___y_4310_ = v___y_4328_;
goto v___jp_4306_;
}
else
{
lean_object* v___x_4347_; lean_object* v_env_4348_; lean_object* v_nextMacroScope_4349_; lean_object* v_ngen_4350_; lean_object* v_auxDeclNGen_4351_; lean_object* v_traceState_4352_; lean_object* v_messages_4353_; lean_object* v_infoState_4354_; lean_object* v_snapshotTasks_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4380_; 
v___x_4347_ = lean_st_ref_take(v___y_4328_);
v_env_4348_ = lean_ctor_get(v___x_4347_, 0);
v_nextMacroScope_4349_ = lean_ctor_get(v___x_4347_, 1);
v_ngen_4350_ = lean_ctor_get(v___x_4347_, 2);
v_auxDeclNGen_4351_ = lean_ctor_get(v___x_4347_, 3);
v_traceState_4352_ = lean_ctor_get(v___x_4347_, 4);
v_messages_4353_ = lean_ctor_get(v___x_4347_, 6);
v_infoState_4354_ = lean_ctor_get(v___x_4347_, 7);
v_snapshotTasks_4355_ = lean_ctor_get(v___x_4347_, 8);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4380_ == 0)
{
lean_object* v_unused_4381_; 
v_unused_4381_ = lean_ctor_get(v___x_4347_, 5);
lean_dec(v_unused_4381_);
v___x_4357_ = v___x_4347_;
v_isShared_4358_ = v_isSharedCheck_4380_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_snapshotTasks_4355_);
lean_inc(v_infoState_4354_);
lean_inc(v_messages_4353_);
lean_inc(v_traceState_4352_);
lean_inc(v_auxDeclNGen_4351_);
lean_inc(v_ngen_4350_);
lean_inc(v_nextMacroScope_4349_);
lean_inc(v_env_4348_);
lean_dec(v___x_4347_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4380_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
lean_inc(v_a_4342_);
v___x_4359_ = l_Lean_markMeta(v_env_4348_, v_a_4342_);
v___x_4360_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 5, v___x_4360_);
lean_ctor_set(v___x_4357_, 0, v___x_4359_);
v___x_4362_ = v___x_4357_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_nextMacroScope_4349_);
lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_ngen_4350_);
lean_ctor_set(v_reuseFailAlloc_4379_, 3, v_auxDeclNGen_4351_);
lean_ctor_set(v_reuseFailAlloc_4379_, 4, v_traceState_4352_);
lean_ctor_set(v_reuseFailAlloc_4379_, 5, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4379_, 6, v_messages_4353_);
lean_ctor_set(v_reuseFailAlloc_4379_, 7, v_infoState_4354_);
lean_ctor_set(v_reuseFailAlloc_4379_, 8, v_snapshotTasks_4355_);
v___x_4362_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v_mctx_4365_; lean_object* v_zetaDeltaFVarIds_4366_; lean_object* v_postponed_4367_; lean_object* v_diag_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4377_; 
v___x_4363_ = lean_st_ref_set(v___y_4328_, v___x_4362_);
v___x_4364_ = lean_st_ref_take(v___y_4325_);
v_mctx_4365_ = lean_ctor_get(v___x_4364_, 0);
v_zetaDeltaFVarIds_4366_ = lean_ctor_get(v___x_4364_, 2);
v_postponed_4367_ = lean_ctor_get(v___x_4364_, 3);
v_diag_4368_ = lean_ctor_get(v___x_4364_, 4);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4377_ == 0)
{
lean_object* v_unused_4378_; 
v_unused_4378_ = lean_ctor_get(v___x_4364_, 1);
lean_dec(v_unused_4378_);
v___x_4370_ = v___x_4364_;
v_isShared_4371_ = v_isSharedCheck_4377_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_diag_4368_);
lean_inc(v_postponed_4367_);
lean_inc(v_zetaDeltaFVarIds_4366_);
lean_inc(v_mctx_4365_);
lean_dec(v___x_4364_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4377_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4372_; lean_object* v___x_4374_; 
v___x_4372_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 1, v___x_4372_);
v___x_4374_ = v___x_4370_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_mctx_4365_);
lean_ctor_set(v_reuseFailAlloc_4376_, 1, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4376_, 2, v_zetaDeltaFVarIds_4366_);
lean_ctor_set(v_reuseFailAlloc_4376_, 3, v_postponed_4367_);
lean_ctor_set(v_reuseFailAlloc_4376_, 4, v_diag_4368_);
v___x_4374_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; 
v___x_4375_ = lean_st_ref_set(v___y_4325_, v___x_4374_);
v___y_4307_ = v_a_4344_;
v___y_4308_ = v_a_4342_;
v___y_4309_ = v___y_4326_;
v___y_4310_ = v___y_4328_;
goto v___jp_4306_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4342_);
return v___x_4343_;
}
}
else
{
lean_object* v___x_4383_; 
lean_dec_ref(v_expectedType_4269_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v_inst_4268_);
v___x_4383_ = v___x_4337_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_inst_4268_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_dec_ref(v_expectedType_4269_);
lean_dec_ref(v_inst_4268_);
v_a_4386_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4334_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4334_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4269_);
lean_dec_ref(v_inst_4268_);
return v___x_4332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(lean_object* v_inst_4550_, lean_object* v_expectedType_4551_, uint8_t v___x_4552_, uint8_t v___x_4553_, uint8_t v_compile_4554_, uint8_t v_logCompileErrors_4555_, uint8_t v_isMeta_4556_, lean_object* v_val_4557_, lean_object* v_x_4558_, lean_object* v_x_4559_, lean_object* v_x_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; lean_object* v_options_4609_; lean_object* v___y_4610_; 
if (lean_obj_tag(v_x_4558_) == 5)
{
lean_object* v_fn_4676_; lean_object* v_arg_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v_fn_4676_ = lean_ctor_get(v_x_4558_, 0);
lean_inc_ref(v_fn_4676_);
v_arg_4677_ = lean_ctor_get(v_x_4558_, 1);
lean_inc_ref(v_arg_4677_);
lean_dec_ref(v_x_4558_);
v___x_4678_ = lean_array_set(v_x_4559_, v_x_4560_, v_arg_4677_);
v___x_4679_ = lean_unsigned_to_nat(1u);
v___x_4680_ = lean_nat_sub(v_x_4560_, v___x_4679_);
v___x_4681_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19(v_inst_4550_, v_expectedType_4551_, v___x_4552_, v___x_4553_, v_compile_4554_, v_logCompileErrors_4555_, v_isMeta_4556_, v_val_4557_, v_fn_4676_, v___x_4678_, v___x_4680_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
return v___x_4681_;
}
else
{
lean_object* v_cls_4682_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___x_4705_; 
v_cls_4682_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4705_ = l_Lean_Expr_constName_x3f(v_x_4558_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4558_);
lean_dec(v_val_4557_);
v___y_4684_ = v___y_4561_;
v___y_4685_ = v___y_4562_;
v___y_4686_ = v___y_4563_;
v___y_4687_ = v___y_4564_;
goto v___jp_4683_;
}
else
{
lean_object* v_val_4706_; lean_object* v___x_4707_; 
v_val_4706_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_val_4706_);
lean_dec_ref(v___x_4705_);
v___x_4707_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4706_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref(v___x_4707_);
if (lean_obj_tag(v_a_4708_) == 6)
{
lean_object* v_val_4709_; lean_object* v___x_4710_; 
lean_dec_ref(v_inst_4550_);
v_val_4709_ = lean_ctor_get(v_a_4708_, 0);
lean_inc_ref(v_val_4709_);
lean_dec_ref(v_a_4708_);
lean_inc(v___y_4564_);
lean_inc_ref(v___y_4563_);
lean_inc(v___y_4562_);
lean_inc_ref(v___y_4561_);
lean_inc_ref(v_x_4558_);
v___x_4710_ = lean_infer_type(v_x_4558_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; uint8_t v___x_4712_; lean_object* v___x_4713_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref(v___x_4710_);
v___x_4712_ = 0;
v___x_4713_ = l_Lean_Meta_forallMetaTelescope(v_a_4711_, v___x_4712_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v_snd_4715_; lean_object* v_fst_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4815_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
lean_inc(v_a_4714_);
lean_dec_ref(v___x_4713_);
v_snd_4715_ = lean_ctor_get(v_a_4714_, 1);
v_fst_4716_ = lean_ctor_get(v_a_4714_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v_a_4714_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4718_ = v_a_4714_;
v_isShared_4719_ = v_isSharedCheck_4815_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_snd_4715_);
lean_inc(v_fst_4716_);
lean_dec(v_a_4714_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4815_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v_snd_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4813_; 
v_snd_4720_ = lean_ctor_get(v_snd_4715_, 1);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_snd_4715_);
if (v_isSharedCheck_4813_ == 0)
{
lean_object* v_unused_4814_; 
v_unused_4814_ = lean_ctor_get(v_snd_4715_, 0);
lean_dec(v_unused_4814_);
v___x_4722_ = v_snd_4715_;
v_isShared_4723_ = v_isSharedCheck_4813_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_snd_4720_);
lean_dec(v_snd_4715_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4813_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4724_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___y_4729_; lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4724_ = lean_array_get_size(v_x_4559_);
v___x_4761_ = lean_array_get_size(v_fst_4716_);
v___x_4762_ = lean_nat_dec_eq(v___x_4724_, v___x_4761_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4766_; 
lean_dec(v_snd_4720_);
lean_dec(v_fst_4716_);
lean_dec_ref(v_val_4709_);
lean_dec(v_val_4557_);
lean_dec_ref(v_expectedType_4551_);
v___x_4763_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3);
v___x_4764_ = l_Lean_MessageData_ofExpr(v_x_4558_);
if (v_isShared_4723_ == 0)
{
lean_ctor_set_tag(v___x_4722_, 7);
lean_ctor_set(v___x_4722_, 1, v___x_4764_);
lean_ctor_set(v___x_4722_, 0, v___x_4763_);
v___x_4766_ = v___x_4722_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4763_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4767_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
if (v_isShared_4719_ == 0)
{
lean_ctor_set_tag(v___x_4718_, 7);
lean_ctor_set(v___x_4718_, 1, v___x_4767_);
lean_ctor_set(v___x_4718_, 0, v___x_4766_);
v___x_4769_ = v___x_4718_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4770_ = lean_array_to_list(v_x_4559_);
v___x_4771_ = lean_box(0);
v___x_4772_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(v___x_4770_, v___x_4771_);
v___x_4773_ = l_Lean_MessageData_ofList(v___x_4772_);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4769_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4774_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
return v___x_4775_;
}
}
}
else
{
lean_object* v___x_4778_; 
lean_inc_ref(v_expectedType_4551_);
v___x_4778_ = l_Lean_Meta_isExprDefEq(v_expectedType_4551_, v_snd_4720_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
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
lean_object* v_toConstantVal_4781_; lean_object* v_name_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4786_; 
lean_dec(v_fst_4716_);
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4558_);
lean_dec(v_val_4557_);
v_toConstantVal_4781_ = lean_ctor_get(v_val_4709_, 0);
lean_inc_ref(v_toConstantVal_4781_);
lean_dec_ref(v_val_4709_);
v_name_4782_ = lean_ctor_get(v_toConstantVal_4781_, 0);
lean_inc(v_name_4782_);
lean_dec_ref(v_toConstantVal_4781_);
v___x_4783_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5);
v___x_4784_ = l_Lean_MessageData_ofExpr(v_expectedType_4551_);
if (v_isShared_4723_ == 0)
{
lean_ctor_set_tag(v___x_4722_, 7);
lean_ctor_set(v___x_4722_, 1, v___x_4784_);
lean_ctor_set(v___x_4722_, 0, v___x_4783_);
v___x_4786_ = v___x_4722_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
lean_object* v___x_4787_; lean_object* v___x_4789_; 
v___x_4787_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7);
if (v_isShared_4719_ == 0)
{
lean_ctor_set_tag(v___x_4718_, 7);
lean_ctor_set(v___x_4718_, 1, v___x_4787_);
lean_ctor_set(v___x_4718_, 0, v___x_4786_);
v___x_4789_ = v___x_4718_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4786_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v___x_4787_);
v___x_4789_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
v___x_4790_ = l_Lean_MessageData_ofConstName(v_name_4782_, v___x_4552_);
v___x_4791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4789_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
v___x_4792_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_4793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4791_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
v___x_4794_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4793_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4794_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4794_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
else
{
lean_del_object(v___x_4722_);
lean_del_object(v___x_4718_);
v___y_4726_ = v___y_4561_;
v___y_4727_ = v___y_4562_;
v___y_4728_ = v___y_4563_;
v___y_4729_ = v___y_4564_;
goto v___jp_4725_;
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_del_object(v___x_4722_);
lean_del_object(v___x_4718_);
lean_dec(v_fst_4716_);
lean_dec_ref(v_val_4709_);
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4558_);
lean_dec(v_val_4557_);
lean_dec_ref(v_expectedType_4551_);
v_a_4805_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4778_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4778_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
v___jp_4725_:
{
lean_object* v_numParams_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v_numParams_4730_ = lean_ctor_get(v_val_4709_, 3);
lean_inc(v_numParams_4730_);
lean_dec_ref(v_val_4709_);
v___x_4731_ = lean_box(0);
v___x_4732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___x_4724_, v_fst_4716_, v_x_4559_, v___x_4553_, v_compile_4554_, v_logCompileErrors_4555_, v___x_4552_, v_isMeta_4556_, v_val_4557_, v_expectedType_4551_, v_numParams_4730_, v___x_4731_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec_ref(v_x_4559_);
if (lean_obj_tag(v___x_4732_) == 0)
{
size_t v_sz_4733_; size_t v___x_4734_; lean_object* v___x_4735_; 
lean_dec_ref(v___x_4732_);
v_sz_4733_ = lean_array_size(v_fst_4716_);
v___x_4734_ = ((size_t)0ULL);
v___x_4735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_4733_, v___x_4734_, v_fst_4716_, v___y_4727_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4744_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4738_ = v___x_4735_;
v_isShared_4739_ = v_isSharedCheck_4744_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4744_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4740_; lean_object* v___x_4742_; 
v___x_4740_ = l_Lean_mkAppN(v_x_4558_, v_a_4736_);
lean_dec(v_a_4736_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v___x_4740_);
v___x_4742_ = v___x_4738_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_dec_ref(v_x_4558_);
v_a_4745_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4735_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4735_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec(v_fst_4716_);
lean_dec_ref(v_x_4558_);
v_a_4753_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4732_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4732_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec_ref(v_val_4709_);
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4558_);
lean_dec(v_val_4557_);
lean_dec_ref(v_expectedType_4551_);
v_a_4816_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4713_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4713_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
else
{
lean_dec_ref(v_val_4709_);
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4558_);
lean_dec(v_val_4557_);
lean_dec_ref(v_expectedType_4551_);
return v___x_4710_;
}
}
else
{
lean_dec(v_a_4708_);
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4558_);
lean_dec(v_val_4557_);
v___y_4684_ = v___y_4561_;
v___y_4685_ = v___y_4562_;
v___y_4686_ = v___y_4563_;
v___y_4687_ = v___y_4564_;
goto v___jp_4683_;
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4558_);
lean_dec(v_val_4557_);
lean_dec_ref(v_expectedType_4551_);
lean_dec_ref(v_inst_4550_);
v_a_4824_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4707_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4707_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
v___jp_4683_:
{
lean_object* v_options_4688_; uint8_t v_hasTrace_4689_; 
v_options_4688_ = lean_ctor_get(v___y_4686_, 2);
v_hasTrace_4689_ = lean_ctor_get_uint8(v_options_4688_, sizeof(void*)*1);
if (v_hasTrace_4689_ == 0)
{
v___y_4606_ = v___y_4684_;
v___y_4607_ = v___y_4685_;
v___y_4608_ = v___y_4686_;
v_options_4609_ = v_options_4688_;
v___y_4610_ = v___y_4687_;
goto v___jp_4605_;
}
else
{
lean_object* v_inheritedTraceOptions_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v_inheritedTraceOptions_4690_ = lean_ctor_get(v___y_4686_, 13);
v___x_4691_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_4692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4690_, v_options_4688_, v___x_4691_);
if (v___x_4692_ == 0)
{
v___y_4606_ = v___y_4684_;
v___y_4607_ = v___y_4685_;
v___y_4608_ = v___y_4686_;
v_options_4609_ = v_options_4688_;
v___y_4610_ = v___y_4687_;
goto v___jp_4605_;
}
else
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4693_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1);
lean_inc_ref(v_inst_4550_);
v___x_4694_ = l_Lean_MessageData_ofExpr(v_inst_4550_);
v___x_4695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4693_);
lean_ctor_set(v___x_4695_, 1, v___x_4694_);
v___x_4696_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4682_, v___x_4695_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_dec_ref(v___x_4696_);
v___y_4606_ = v___y_4684_;
v___y_4607_ = v___y_4685_;
v___y_4608_ = v___y_4686_;
v_options_4609_ = v_options_4688_;
v___y_4610_ = v___y_4687_;
goto v___jp_4605_;
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v_expectedType_4551_);
lean_dec_ref(v_inst_4550_);
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4696_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
}
}
v___jp_4566_:
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Lean_enableRealizationsForConst(v___y_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4578_ == 0)
{
lean_object* v_unused_4579_; 
v_unused_4579_ = lean_ctor_get(v___x_4571_, 0);
lean_dec(v_unused_4579_);
v___x_4573_ = v___x_4571_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_dec(v___x_4571_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v___y_4567_);
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___y_4567_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec_ref(v___y_4567_);
v_a_4580_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4571_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4571_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
v___jp_4588_:
{
if (v_compile_4554_ == 0)
{
v___y_4567_ = v___y_4589_;
v___y_4568_ = v___y_4590_;
v___y_4569_ = v___y_4591_;
v___y_4570_ = v___y_4592_;
goto v___jp_4566_;
}
else
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4593_ = lean_unsigned_to_nat(1u);
v___x_4594_ = lean_mk_empty_array_with_capacity(v___x_4593_);
lean_inc(v___y_4590_);
v___x_4595_ = lean_array_push(v___x_4594_, v___y_4590_);
v___x_4596_ = l_Lean_compileDecls(v___x_4595_, v_logCompileErrors_4555_, v___y_4591_, v___y_4592_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_dec_ref(v___x_4596_);
v___y_4567_ = v___y_4589_;
v___y_4568_ = v___y_4590_;
v___y_4569_ = v___y_4591_;
v___y_4570_ = v___y_4592_;
goto v___jp_4566_;
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4596_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4596_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
}
v___jp_4605_:
{
lean_object* v___x_4611_; uint8_t v___x_4612_; 
v___x_4611_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4612_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4609_, v___x_4611_);
if (v___x_4612_ == 0)
{
lean_object* v___x_4613_; 
lean_dec_ref(v_expectedType_4551_);
v___x_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4613_, 0, v_inst_4550_);
return v___x_4613_;
}
else
{
lean_object* v___x_4614_; 
lean_inc(v___y_4610_);
lean_inc_ref(v___y_4608_);
lean_inc(v___y_4607_);
lean_inc_ref(v___y_4606_);
lean_inc_ref(v_inst_4550_);
v___x_4614_ = lean_infer_type(v_inst_4550_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4610_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4616_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref(v___x_4614_);
lean_inc_ref(v_expectedType_4551_);
v___x_4616_ = l_Lean_Meta_isExprDefEq(v_expectedType_4551_, v_a_4615_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4610_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4667_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4619_ = v___x_4616_;
v_isShared_4620_ = v_isSharedCheck_4667_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4616_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4667_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
uint8_t v___x_4621_; 
v___x_4621_ = lean_unbox(v_a_4617_);
lean_dec(v_a_4617_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v_a_4624_; lean_object* v___x_4625_; 
lean_del_object(v___x_4619_);
v___x_4622_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_4623_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4622_, v___y_4610_);
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc_n(v_a_4624_, 2);
lean_dec_ref(v___x_4623_);
v___x_4625_ = l_Lean_Meta_mkAuxDefinition(v_a_4624_, v_expectedType_4551_, v_inst_4550_, v___x_4552_, v___x_4552_, v___x_4553_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4610_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; uint8_t v___x_4627_; lean_object* v___x_4628_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref(v___x_4625_);
v___x_4627_ = 3;
lean_inc(v_a_4624_);
v___x_4628_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4624_, v___x_4627_, v___y_4607_, v___y_4610_);
lean_dec_ref(v___x_4628_);
if (v_isMeta_4556_ == 0)
{
v___y_4589_ = v_a_4626_;
v___y_4590_ = v_a_4624_;
v___y_4591_ = v___y_4608_;
v___y_4592_ = v___y_4610_;
goto v___jp_4588_;
}
else
{
lean_object* v___x_4629_; lean_object* v_env_4630_; lean_object* v_nextMacroScope_4631_; lean_object* v_ngen_4632_; lean_object* v_auxDeclNGen_4633_; lean_object* v_traceState_4634_; lean_object* v_messages_4635_; lean_object* v_infoState_4636_; lean_object* v_snapshotTasks_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4662_; 
v___x_4629_ = lean_st_ref_take(v___y_4610_);
v_env_4630_ = lean_ctor_get(v___x_4629_, 0);
v_nextMacroScope_4631_ = lean_ctor_get(v___x_4629_, 1);
v_ngen_4632_ = lean_ctor_get(v___x_4629_, 2);
v_auxDeclNGen_4633_ = lean_ctor_get(v___x_4629_, 3);
v_traceState_4634_ = lean_ctor_get(v___x_4629_, 4);
v_messages_4635_ = lean_ctor_get(v___x_4629_, 6);
v_infoState_4636_ = lean_ctor_get(v___x_4629_, 7);
v_snapshotTasks_4637_ = lean_ctor_get(v___x_4629_, 8);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4662_ == 0)
{
lean_object* v_unused_4663_; 
v_unused_4663_ = lean_ctor_get(v___x_4629_, 5);
lean_dec(v_unused_4663_);
v___x_4639_ = v___x_4629_;
v_isShared_4640_ = v_isSharedCheck_4662_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_snapshotTasks_4637_);
lean_inc(v_infoState_4636_);
lean_inc(v_messages_4635_);
lean_inc(v_traceState_4634_);
lean_inc(v_auxDeclNGen_4633_);
lean_inc(v_ngen_4632_);
lean_inc(v_nextMacroScope_4631_);
lean_inc(v_env_4630_);
lean_dec(v___x_4629_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4662_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4644_; 
lean_inc(v_a_4624_);
v___x_4641_ = l_Lean_markMeta(v_env_4630_, v_a_4624_);
v___x_4642_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 5, v___x_4642_);
lean_ctor_set(v___x_4639_, 0, v___x_4641_);
v___x_4644_ = v___x_4639_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v_nextMacroScope_4631_);
lean_ctor_set(v_reuseFailAlloc_4661_, 2, v_ngen_4632_);
lean_ctor_set(v_reuseFailAlloc_4661_, 3, v_auxDeclNGen_4633_);
lean_ctor_set(v_reuseFailAlloc_4661_, 4, v_traceState_4634_);
lean_ctor_set(v_reuseFailAlloc_4661_, 5, v___x_4642_);
lean_ctor_set(v_reuseFailAlloc_4661_, 6, v_messages_4635_);
lean_ctor_set(v_reuseFailAlloc_4661_, 7, v_infoState_4636_);
lean_ctor_set(v_reuseFailAlloc_4661_, 8, v_snapshotTasks_4637_);
v___x_4644_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v_mctx_4647_; lean_object* v_zetaDeltaFVarIds_4648_; lean_object* v_postponed_4649_; lean_object* v_diag_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4659_; 
v___x_4645_ = lean_st_ref_set(v___y_4610_, v___x_4644_);
v___x_4646_ = lean_st_ref_take(v___y_4607_);
v_mctx_4647_ = lean_ctor_get(v___x_4646_, 0);
v_zetaDeltaFVarIds_4648_ = lean_ctor_get(v___x_4646_, 2);
v_postponed_4649_ = lean_ctor_get(v___x_4646_, 3);
v_diag_4650_ = lean_ctor_get(v___x_4646_, 4);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4659_ == 0)
{
lean_object* v_unused_4660_; 
v_unused_4660_ = lean_ctor_get(v___x_4646_, 1);
lean_dec(v_unused_4660_);
v___x_4652_ = v___x_4646_;
v_isShared_4653_ = v_isSharedCheck_4659_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_diag_4650_);
lean_inc(v_postponed_4649_);
lean_inc(v_zetaDeltaFVarIds_4648_);
lean_inc(v_mctx_4647_);
lean_dec(v___x_4646_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4659_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4654_; lean_object* v___x_4656_; 
v___x_4654_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 1, v___x_4654_);
v___x_4656_ = v___x_4652_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_mctx_4647_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4658_, 2, v_zetaDeltaFVarIds_4648_);
lean_ctor_set(v_reuseFailAlloc_4658_, 3, v_postponed_4649_);
lean_ctor_set(v_reuseFailAlloc_4658_, 4, v_diag_4650_);
v___x_4656_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_st_ref_set(v___y_4607_, v___x_4656_);
v___y_4589_ = v_a_4626_;
v___y_4590_ = v_a_4624_;
v___y_4591_ = v___y_4608_;
v___y_4592_ = v___y_4610_;
goto v___jp_4588_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4624_);
return v___x_4625_;
}
}
else
{
lean_object* v___x_4665_; 
lean_dec_ref(v_expectedType_4551_);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 0, v_inst_4550_);
v___x_4665_ = v___x_4619_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_inst_4550_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
lean_dec_ref(v_expectedType_4551_);
lean_dec_ref(v_inst_4550_);
v_a_4668_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4616_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4616_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4551_);
lean_dec_ref(v_inst_4550_);
return v___x_4614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object* v_expectedType_4832_, lean_object* v_inst_4833_, uint8_t v___x_4834_, uint8_t v_hasTrace_4835_, uint8_t v_compile_4836_, uint8_t v_logCompileErrors_4837_, uint8_t v_isMeta_4838_, lean_object* v_val_4839_, lean_object* v_____r_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v___x_4846_; 
lean_inc_ref(v_expectedType_4832_);
v___x_4846_ = l_Lean_Meta_isProp(v_expectedType_4832_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4868_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4868_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4868_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
uint8_t v___x_4851_; 
v___x_4851_ = lean_unbox(v_a_4847_);
lean_dec(v_a_4847_);
if (v___x_4851_ == 0)
{
lean_object* v___x_4852_; 
lean_del_object(v___x_4849_);
lean_inc(v___y_4844_);
lean_inc_ref(v___y_4843_);
lean_inc(v___y_4842_);
lean_inc_ref(v___y_4841_);
lean_inc_ref(v_inst_4833_);
v___x_4852_ = lean_whnf(v_inst_4833_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v_dummy_4854_; lean_object* v_nargs_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref(v___x_4852_);
v_dummy_4854_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_4855_ = l_Lean_Expr_getAppNumArgs(v_a_4853_);
lean_inc(v_nargs_4855_);
v___x_4856_ = lean_mk_array(v_nargs_4855_, v_dummy_4854_);
v___x_4857_ = lean_unsigned_to_nat(1u);
v___x_4858_ = lean_nat_sub(v_nargs_4855_, v___x_4857_);
lean_dec(v_nargs_4855_);
v___x_4859_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_inst_4833_, v_expectedType_4832_, v___x_4834_, v_hasTrace_4835_, v_compile_4836_, v_logCompileErrors_4837_, v_isMeta_4838_, v_val_4839_, v_a_4853_, v___x_4856_, v___x_4858_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
lean_dec(v___x_4858_);
return v___x_4859_;
}
else
{
lean_dec(v_val_4839_);
lean_dec_ref(v_inst_4833_);
lean_dec_ref(v_expectedType_4832_);
return v___x_4852_;
}
}
else
{
lean_object* v_options_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
lean_dec(v_val_4839_);
v_options_4860_ = lean_ctor_get(v___y_4843_, 2);
v___x_4861_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4862_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4860_, v___x_4861_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4864_; 
lean_dec_ref(v_expectedType_4832_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v_inst_4833_);
v___x_4864_ = v___x_4849_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_inst_4833_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; 
lean_del_object(v___x_4849_);
v___x_4866_ = lean_box(0);
v___x_4867_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_4832_, v_inst_4833_, v_hasTrace_4835_, v___x_4866_, v_hasTrace_4835_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
return v___x_4867_;
}
}
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v_val_4839_);
lean_dec_ref(v_inst_4833_);
lean_dec_ref(v_expectedType_4832_);
v_a_4869_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4846_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4846_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___closed__3(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = ((lean_object*)(l_Lean_Meta_wrapInstance___closed__2));
v___x_4879_ = l_Lean_stringToMessageData(v___x_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object* v_upperBound_4880_, lean_object* v_fst_4881_, lean_object* v_args_4882_, uint8_t v___x_4883_, uint8_t v_compile_4884_, uint8_t v_logCompileErrors_4885_, uint8_t v_isMeta_4886_, lean_object* v_val_4887_, lean_object* v_expectedType_4888_, lean_object* v_a_4889_, lean_object* v_b_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_a_4897_; lean_object* v___y_4902_; uint8_t v___x_4921_; 
v___x_4921_ = lean_nat_dec_lt(v_a_4889_, v_upperBound_4880_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; 
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v___x_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4922_, 0, v_b_4890_);
return v___x_4922_;
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4923_ = lean_array_fget_borrowed(v_fst_4881_, v_a_4889_);
v___x_4924_ = l_Lean_Expr_mvarId_x21(v___x_4923_);
lean_inc(v___x_4924_);
v___x_4925_ = l_Lean_MVarId_getDecl(v___x_4924_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v_userName_4927_; lean_object* v_type_4928_; lean_object* v___x_4929_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_a_4926_);
lean_dec_ref(v___x_4925_);
v_userName_4927_ = lean_ctor_get(v_a_4926_, 0);
lean_inc(v_userName_4927_);
v_type_4928_ = lean_ctor_get(v_a_4926_, 2);
lean_inc_ref(v_type_4928_);
lean_dec(v_a_4926_);
v___x_4929_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_4928_, v___y_4892_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4931_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc_n(v_a_4930_, 2);
lean_dec_ref(v___x_4929_);
v___x_4931_ = l_Lean_Meta_isProp(v_a_4930_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v___x_4933_; lean_object* v_cls_4934_; lean_object* v___f_4935_; lean_object* v___x_4936_; uint8_t v___x_4937_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref(v___x_4931_);
v___x_4933_ = lean_box(0);
v_cls_4934_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_4935_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0));
v___x_4936_ = lean_array_fget_borrowed(v_args_4882_, v_a_4889_);
v___x_4937_ = lean_unbox(v_a_4932_);
lean_dec(v_a_4932_);
if (v___x_4937_ == 0)
{
lean_object* v___x_4938_; 
lean_inc(v_a_4930_);
v___x_4938_ = l_Lean_Meta_isClass_x3f(v_a_4930_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_5037_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_4941_ = v___x_4938_;
v_isShared_4942_ = v_isSharedCheck_5037_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4938_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_5037_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___f_4947_; 
v___x_4943_ = lean_box(v___x_4883_);
v___x_4944_ = lean_box(v_compile_4884_);
v___x_4945_ = lean_box(v_logCompileErrors_4885_);
v___x_4946_ = lean_box(v_isMeta_4886_);
lean_inc(v_a_4930_);
lean_inc(v___x_4936_);
lean_inc(v___x_4924_);
v___f_4947_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1___boxed), 14, 8);
lean_closure_set(v___f_4947_, 0, v___x_4924_);
lean_closure_set(v___f_4947_, 1, v___x_4936_);
lean_closure_set(v___f_4947_, 2, v___x_4933_);
lean_closure_set(v___f_4947_, 3, v_a_4930_);
lean_closure_set(v___f_4947_, 4, v___x_4943_);
lean_closure_set(v___f_4947_, 5, v___x_4944_);
lean_closure_set(v___f_4947_, 6, v___x_4945_);
lean_closure_set(v___f_4947_, 7, v___x_4946_);
if (lean_obj_tag(v_a_4939_) == 0)
{
lean_del_object(v___x_4941_);
goto v___jp_4950_;
}
else
{
lean_dec_ref(v_a_4939_);
if (v___x_4883_ == 0)
{
lean_del_object(v___x_4941_);
goto v___jp_4950_;
}
else
{
lean_object* v_options_4998_; lean_object* v_a_5000_; lean_object* v___y_5003_; uint8_t v___y_5004_; lean_object* v_a_5009_; lean_object* v___y_5013_; lean_object* v___x_5017_; uint8_t v___x_5018_; 
lean_dec_ref(v___f_4947_);
lean_dec(v_userName_4927_);
v_options_4998_ = lean_ctor_get(v___y_4893_, 2);
v___x_5017_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_5018_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4998_, v___x_5017_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; 
lean_del_object(v___x_4941_);
lean_inc(v___x_4936_);
v___x_5019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_4936_, v_a_4930_, v_compile_4884_, v_logCompileErrors_4885_, v_isMeta_4886_, v___x_4924_, v___x_4933_, v___x_4933_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_5019_;
goto v___jp_4901_;
}
else
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_box(0);
lean_inc(v_a_4930_);
v___x_5021_ = l_Lean_Meta_trySynthInstance(v_a_4930_, v___x_5020_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5022_);
lean_dec_ref(v___x_5021_);
if (lean_obj_tag(v_a_5022_) == 1)
{
lean_object* v_a_5023_; lean_object* v___x_5024_; 
v_a_5023_ = lean_ctor_get(v_a_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref(v_a_5022_);
v___x_5024_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_4934_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; uint8_t v___x_5026_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5025_);
lean_dec_ref(v___x_5024_);
v___x_5026_ = lean_unbox(v_a_5025_);
lean_dec(v_a_5025_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
lean_inc(v___x_4924_);
v___x_5027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_4924_, v_a_5023_, v___x_4933_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_5013_ = v___x_5027_;
goto v___jp_5012_;
}
else
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5028_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__2);
lean_inc(v_a_5023_);
v___x_5029_ = l_Lean_MessageData_ofExpr(v_a_5023_);
v___x_5030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5028_);
lean_ctor_set(v___x_5030_, 1, v___x_5029_);
v___x_5031_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4934_, v___x_5030_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5033_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref(v___x_5031_);
lean_inc(v___x_4924_);
v___x_5033_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__5(v___x_4924_, v_a_5023_, v_a_5032_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_5013_ = v___x_5033_;
goto v___jp_5012_;
}
else
{
lean_object* v_a_5034_; 
lean_dec(v_a_5023_);
v_a_5034_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5034_);
lean_dec_ref(v___x_5031_);
v_a_5009_ = v_a_5034_;
goto v___jp_5008_;
}
}
}
else
{
lean_object* v_a_5035_; 
lean_dec(v_a_5023_);
v_a_5035_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5035_);
lean_dec_ref(v___x_5024_);
v_a_5009_ = v_a_5035_;
goto v___jp_5008_;
}
}
else
{
lean_dec(v_a_5022_);
lean_del_object(v___x_4941_);
v_a_5000_ = v___x_4933_;
goto v___jp_4999_;
}
}
else
{
lean_object* v_a_5036_; 
v_a_5036_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5036_);
lean_dec_ref(v___x_5021_);
v_a_5009_ = v_a_5036_;
goto v___jp_5008_;
}
}
v___jp_4999_:
{
lean_object* v___x_5001_; 
lean_inc(v___x_4936_);
v___x_5001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_4936_, v_a_4930_, v_compile_4884_, v_logCompileErrors_4885_, v_isMeta_4886_, v___x_4924_, v___x_4933_, v_a_5000_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_5001_;
goto v___jp_4901_;
}
v___jp_5002_:
{
if (v___y_5004_ == 0)
{
lean_dec_ref(v___y_5003_);
lean_del_object(v___x_4941_);
v_a_5000_ = v___x_4933_;
goto v___jp_4999_;
}
else
{
lean_object* v___x_5006_; 
lean_dec(v_a_4930_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set_tag(v___x_4941_, 1);
lean_ctor_set(v___x_4941_, 0, v___y_5003_);
v___x_5006_ = v___x_4941_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___y_5003_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
v___jp_5008_:
{
uint8_t v___x_5010_; 
v___x_5010_ = l_Lean_Exception_isInterrupt(v_a_5009_);
if (v___x_5010_ == 0)
{
uint8_t v___x_5011_; 
lean_inc_ref(v_a_5009_);
v___x_5011_ = l_Lean_Exception_isRuntime(v_a_5009_);
v___y_5003_ = v_a_5009_;
v___y_5004_ = v___x_5011_;
goto v___jp_5002_;
}
else
{
v___y_5003_ = v_a_5009_;
v___y_5004_ = v___x_5010_;
goto v___jp_5002_;
}
}
v___jp_5012_:
{
if (lean_obj_tag(v___y_5013_) == 0)
{
lean_object* v_a_5014_; 
lean_del_object(v___x_4941_);
v_a_5014_ = lean_ctor_get(v___y_5013_, 0);
lean_inc(v_a_5014_);
lean_dec_ref(v___y_5013_);
if (lean_obj_tag(v_a_5014_) == 0)
{
lean_dec(v_a_4930_);
lean_dec(v___x_4924_);
v_a_4897_ = v___x_4933_;
goto v___jp_4896_;
}
else
{
lean_object* v_a_5015_; 
v_a_5015_ = lean_ctor_get(v_a_5014_, 0);
lean_inc(v_a_5015_);
lean_dec_ref(v_a_5014_);
v_a_5000_ = v_a_5015_;
goto v___jp_4999_;
}
}
else
{
lean_object* v_a_5016_; 
v_a_5016_ = lean_ctor_get(v___y_5013_, 0);
lean_inc(v_a_5016_);
lean_dec_ref(v___y_5013_);
v_a_5009_ = v_a_5016_;
goto v___jp_5008_;
}
}
}
}
v___jp_4948_:
{
lean_object* v___x_4949_; 
lean_inc(v___x_4936_);
v___x_4949_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1(v___x_4924_, v___x_4936_, v___x_4933_, v_a_4930_, v___x_4883_, v_compile_4884_, v_logCompileErrors_4885_, v_isMeta_4886_, v___x_4933_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_4949_;
goto v___jp_4901_;
}
v___jp_4950_:
{
lean_object* v_options_4951_; lean_object* v___x_4952_; uint8_t v___x_4953_; 
v_options_4951_ = lean_ctor_get(v___y_4893_, 2);
v___x_4952_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4953_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4951_, v___x_4952_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; 
lean_dec_ref(v___f_4947_);
lean_dec(v_userName_4927_);
lean_inc(v___x_4936_);
v___x_4954_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__1(v___x_4924_, v___x_4936_, v___x_4933_, v_a_4930_, v___x_4883_, v_compile_4884_, v_logCompileErrors_4885_, v_isMeta_4886_, v___x_4933_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_4954_;
goto v___jp_4901_;
}
else
{
lean_object* v___x_4955_; 
lean_inc(v_userName_4927_);
lean_inc(v_val_4887_);
v___x_4955_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_4887_, v_userName_4927_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v_a_4956_; lean_object* v_fst_4957_; lean_object* v_snd_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4989_; 
v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_a_4956_);
lean_dec_ref(v___x_4955_);
v_fst_4957_ = lean_ctor_get(v_a_4956_, 0);
v_snd_4958_ = lean_ctor_get(v_a_4956_, 1);
v_isSharedCheck_4989_ = !lean_is_exclusive(v_a_4956_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4960_ = v_a_4956_;
v_isShared_4961_ = v_isSharedCheck_4989_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_snd_4958_);
lean_inc(v_fst_4957_);
lean_dec(v_a_4956_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4989_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
uint8_t v___x_4962_; 
v___x_4962_ = lean_name_eq(v_fst_4957_, v_val_4887_);
if (v___x_4962_ == 0)
{
if (v___x_4883_ == 0)
{
lean_del_object(v___x_4960_);
lean_dec(v_snd_4958_);
lean_dec(v_fst_4957_);
lean_dec_ref(v___f_4947_);
lean_dec(v_userName_4927_);
goto v___jp_4948_;
}
else
{
lean_object* v___x_4963_; 
lean_dec(v_a_4930_);
v___x_4963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_4934_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; uint8_t v___x_4965_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref(v___x_4963_);
v___x_4965_ = lean_unbox(v_a_4964_);
lean_dec(v_a_4964_);
if (v___x_4965_ == 0)
{
lean_object* v___x_4966_; 
lean_del_object(v___x_4960_);
lean_dec(v_userName_4927_);
lean_inc_ref(v_expectedType_4888_);
lean_inc(v_val_4887_);
v___x_4966_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(v_val_4887_, v_fst_4957_, v_expectedType_4888_, v___f_4935_, v___f_4947_, v___x_4933_, v_cls_4934_, v_snd_4958_, v___x_4924_, v___x_4933_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_4966_;
goto v___jp_4901_;
}
else
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4970_; 
v___x_4967_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__4);
v___x_4968_ = l_Lean_MessageData_ofName(v_userName_4927_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set_tag(v___x_4960_, 7);
lean_ctor_set(v___x_4960_, 1, v___x_4968_);
lean_ctor_set(v___x_4960_, 0, v___x_4967_);
v___x_4970_ = v___x_4960_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4971_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__6);
v___x_4972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4970_);
lean_ctor_set(v___x_4972_, 1, v___x_4971_);
lean_inc(v_fst_4957_);
v___x_4973_ = l_Lean_MessageData_ofName(v_fst_4957_);
v___x_4974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4972_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4974_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4934_, v___x_4976_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4979_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref(v___x_4977_);
lean_inc_ref(v_expectedType_4888_);
lean_inc(v_val_4887_);
v___x_4979_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5(v_val_4887_, v_fst_4957_, v_expectedType_4888_, v___f_4935_, v___f_4947_, v___x_4933_, v_cls_4934_, v_snd_4958_, v___x_4924_, v_a_4978_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_4979_;
goto v___jp_4901_;
}
else
{
lean_dec(v_snd_4958_);
lean_dec(v_fst_4957_);
lean_dec_ref(v___f_4947_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
return v___x_4977_;
}
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_del_object(v___x_4960_);
lean_dec(v_snd_4958_);
lean_dec(v_fst_4957_);
lean_dec_ref(v___f_4947_);
lean_dec(v_userName_4927_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_4981_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4963_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4963_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
}
else
{
lean_del_object(v___x_4960_);
lean_dec(v_snd_4958_);
lean_dec(v_fst_4957_);
lean_dec_ref(v___f_4947_);
lean_dec(v_userName_4927_);
goto v___jp_4948_;
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_dec_ref(v___f_4947_);
lean_dec(v_a_4930_);
lean_dec(v_userName_4927_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_4990_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4955_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4955_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
lean_dec(v_a_4930_);
lean_dec(v_userName_4927_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_5038_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5040_ = v___x_4938_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_4938_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
else
{
lean_object* v___x_5046_; 
lean_dec(v_userName_4927_);
lean_inc(v___y_4894_);
lean_inc_ref(v___y_4893_);
lean_inc(v___y_4892_);
lean_inc_ref(v___y_4891_);
lean_inc(v___x_4936_);
v___x_5046_ = lean_infer_type(v___x_4936_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_object* v_a_5047_; lean_object* v___x_5048_; 
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc_n(v_a_5047_, 2);
lean_dec_ref(v___x_5046_);
lean_inc(v_a_4930_);
v___x_5048_ = l_Lean_Meta_isExprDefEq(v_a_4930_, v_a_5047_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v_a_5049_; lean_object* v___f_5050_; uint8_t v___x_5051_; 
v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
lean_inc(v_a_5049_);
lean_dec_ref(v___x_5048_);
v___f_5050_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__7));
v___x_5051_ = lean_unbox(v_a_5049_);
lean_dec(v_a_5049_);
if (v___x_5051_ == 0)
{
lean_object* v___x_5052_; 
v___x_5052_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_cls_4934_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5052_) == 0)
{
lean_object* v_a_5053_; uint8_t v___x_5054_; 
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc(v_a_5053_);
lean_dec_ref(v___x_5052_);
v___x_5054_ = lean_unbox(v_a_5053_);
lean_dec(v_a_5053_);
if (v___x_5054_ == 0)
{
lean_object* v___x_5055_; 
lean_dec(v_a_5047_);
lean_inc(v___x_4936_);
v___x_5055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_4930_, v___x_4936_, v___x_4883_, v___x_4924_, v___f_5050_, v___x_4933_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_5055_;
goto v___jp_4901_;
}
else
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5056_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__9);
lean_inc(v_a_4889_);
v___x_5057_ = l_Nat_reprFast(v_a_4889_);
v___x_5058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
v___x_5059_ = l_Lean_MessageData_ofFormat(v___x_5058_);
v___x_5060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5056_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
v___x_5061_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__11);
v___x_5062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5060_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
lean_inc(v_a_4930_);
v___x_5063_ = l_Lean_MessageData_ofExpr(v_a_4930_);
v___x_5064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5062_);
lean_ctor_set(v___x_5064_, 1, v___x_5063_);
v___x_5065_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__13);
v___x_5066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5064_);
lean_ctor_set(v___x_5066_, 1, v___x_5065_);
v___x_5067_ = l_Lean_MessageData_ofExpr(v_a_5047_);
v___x_5068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5066_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
v___x_5069_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__15);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5068_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
lean_inc(v___x_4936_);
v___x_5071_ = l_Lean_MessageData_ofExpr(v___x_4936_);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5070_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4934_, v___x_5072_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v___x_5075_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5074_);
lean_dec_ref(v___x_5073_);
lean_inc(v___x_4936_);
v___x_5075_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__7(v_a_4930_, v___x_4936_, v___x_4883_, v___x_4924_, v___f_5050_, v_a_5074_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_5075_;
goto v___jp_4901_;
}
else
{
lean_dec(v_a_4930_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
return v___x_5073_;
}
}
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec(v_a_5047_);
lean_dec(v_a_4930_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_5076_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5052_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5052_);
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
lean_object* v___x_5084_; 
lean_dec(v_a_5047_);
lean_dec(v_a_4930_);
lean_inc(v___x_4936_);
v___x_5084_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4924_, v___x_4936_, v___y_4892_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5086_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref(v___x_5084_);
v___x_5086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__6(v___x_4933_, v_a_5085_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4902_ = v___x_5086_;
goto v___jp_4901_;
}
else
{
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
return v___x_5084_;
}
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v_a_5047_);
lean_dec(v_a_4930_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_5087_ = lean_ctor_get(v___x_5048_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5048_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5048_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_dec(v_a_4930_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_5095_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5046_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5046_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec(v_a_4930_);
lean_dec(v_userName_4927_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_5103_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_4931_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_4931_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec(v_userName_4927_);
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_5111_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_4929_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_4929_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec(v___x_4924_);
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_5119_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_4925_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_4925_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
v___jp_4896_:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
v___x_4898_ = lean_unsigned_to_nat(1u);
v___x_4899_ = lean_nat_add(v_a_4889_, v___x_4898_);
lean_dec(v_a_4889_);
v_a_4889_ = v___x_4899_;
v_b_4890_ = v_a_4897_;
goto _start;
}
v___jp_4901_:
{
if (lean_obj_tag(v___y_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4912_; 
v_a_4903_ = lean_ctor_get(v___y_4902_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___y_4902_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4905_ = v___y_4902_;
v_isShared_4906_ = v_isSharedCheck_4912_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___y_4902_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4912_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
if (lean_obj_tag(v_a_4903_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; 
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_4907_ = lean_ctor_get(v_a_4903_, 0);
lean_inc(v_a_4907_);
lean_dec_ref(v_a_4903_);
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 0, v_a_4907_);
v___x_4909_ = v___x_4905_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4907_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
else
{
lean_object* v_a_4911_; 
lean_del_object(v___x_4905_);
v_a_4911_ = lean_ctor_get(v_a_4903_, 0);
lean_inc(v_a_4911_);
lean_dec_ref(v_a_4903_);
v_a_4897_ = v_a_4911_;
goto v___jp_4896_;
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec(v_a_4889_);
lean_dec_ref(v_expectedType_4888_);
lean_dec(v_val_4887_);
v_a_4913_ = lean_ctor_get(v___y_4902_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___y_4902_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___y_4902_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___y_4902_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(lean_object* v_inst_5127_, lean_object* v_expectedType_5128_, uint8_t v___x_5129_, uint8_t v_compile_5130_, uint8_t v_logCompileErrors_5131_, uint8_t v_isMeta_5132_, lean_object* v_val_5133_, lean_object* v_x_5134_, lean_object* v_x_5135_, lean_object* v_x_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
lean_object* v___y_5143_; lean_object* v___y_5144_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5165_; lean_object* v___y_5166_; lean_object* v___y_5167_; lean_object* v___y_5168_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5184_; lean_object* v_options_5185_; lean_object* v___y_5186_; 
if (lean_obj_tag(v_x_5134_) == 5)
{
lean_object* v_fn_5254_; lean_object* v_arg_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; 
v_fn_5254_ = lean_ctor_get(v_x_5134_, 0);
lean_inc_ref(v_fn_5254_);
v_arg_5255_ = lean_ctor_get(v_x_5134_, 1);
lean_inc_ref(v_arg_5255_);
lean_dec_ref(v_x_5134_);
v___x_5256_ = lean_array_set(v_x_5135_, v_x_5136_, v_arg_5255_);
v___x_5257_ = lean_unsigned_to_nat(1u);
v___x_5258_ = lean_nat_sub(v_x_5136_, v___x_5257_);
lean_dec(v_x_5136_);
v_x_5134_ = v_fn_5254_;
v_x_5135_ = v___x_5256_;
v_x_5136_ = v___x_5258_;
goto _start;
}
else
{
lean_object* v_cls_5260_; lean_object* v___y_5262_; lean_object* v___y_5263_; lean_object* v___y_5264_; lean_object* v___y_5265_; lean_object* v___x_5283_; 
lean_dec(v_x_5136_);
v_cls_5260_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5283_ = l_Lean_Expr_constName_x3f(v_x_5134_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_dec_ref(v_x_5135_);
lean_dec_ref(v_x_5134_);
lean_dec(v_val_5133_);
v___y_5262_ = v___y_5137_;
v___y_5263_ = v___y_5138_;
v___y_5264_ = v___y_5139_;
v___y_5265_ = v___y_5140_;
goto v___jp_5261_;
}
else
{
lean_object* v_val_5284_; lean_object* v___x_5285_; 
v_val_5284_ = lean_ctor_get(v___x_5283_, 0);
lean_inc(v_val_5284_);
lean_dec_ref(v___x_5283_);
v___x_5285_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_5284_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref(v___x_5285_);
if (lean_obj_tag(v_a_5286_) == 6)
{
lean_object* v_val_5287_; lean_object* v___x_5288_; 
lean_dec_ref(v_inst_5127_);
v_val_5287_ = lean_ctor_get(v_a_5286_, 0);
lean_inc_ref(v_val_5287_);
lean_dec_ref(v_a_5286_);
lean_inc(v___y_5140_);
lean_inc_ref(v___y_5139_);
lean_inc(v___y_5138_);
lean_inc_ref(v___y_5137_);
lean_inc_ref(v_x_5134_);
v___x_5288_ = lean_infer_type(v_x_5134_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; uint8_t v___x_5290_; lean_object* v___x_5291_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
lean_inc(v_a_5289_);
lean_dec_ref(v___x_5288_);
v___x_5290_ = 0;
v___x_5291_ = l_Lean_Meta_forallMetaTelescope(v_a_5289_, v___x_5290_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5291_) == 0)
{
lean_object* v_a_5292_; lean_object* v_snd_5293_; lean_object* v_fst_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5394_; 
v_a_5292_ = lean_ctor_get(v___x_5291_, 0);
lean_inc(v_a_5292_);
lean_dec_ref(v___x_5291_);
v_snd_5293_ = lean_ctor_get(v_a_5292_, 1);
v_fst_5294_ = lean_ctor_get(v_a_5292_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v_a_5292_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5296_ = v_a_5292_;
v_isShared_5297_ = v_isSharedCheck_5394_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_snd_5293_);
lean_inc(v_fst_5294_);
lean_dec(v_a_5292_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5394_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v_snd_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5392_; 
v_snd_5298_ = lean_ctor_get(v_snd_5293_, 1);
v_isSharedCheck_5392_ = !lean_is_exclusive(v_snd_5293_);
if (v_isSharedCheck_5392_ == 0)
{
lean_object* v_unused_5393_; 
v_unused_5393_ = lean_ctor_get(v_snd_5293_, 0);
lean_dec(v_unused_5393_);
v___x_5300_ = v_snd_5293_;
v_isShared_5301_ = v_isSharedCheck_5392_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_snd_5298_);
lean_dec(v_snd_5293_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5392_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5302_; lean_object* v___y_5304_; lean_object* v___y_5305_; lean_object* v___y_5306_; lean_object* v___y_5307_; lean_object* v___x_5339_; uint8_t v___x_5340_; 
v___x_5302_ = lean_array_get_size(v_x_5135_);
v___x_5339_ = lean_array_get_size(v_fst_5294_);
v___x_5340_ = lean_nat_dec_eq(v___x_5302_, v___x_5339_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5344_; 
lean_dec(v_snd_5298_);
lean_dec(v_fst_5294_);
lean_dec_ref(v_val_5287_);
lean_dec(v_val_5133_);
lean_dec_ref(v_expectedType_5128_);
v___x_5341_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3);
v___x_5342_ = l_Lean_MessageData_ofExpr(v_x_5134_);
if (v_isShared_5301_ == 0)
{
lean_ctor_set_tag(v___x_5300_, 7);
lean_ctor_set(v___x_5300_, 1, v___x_5342_);
lean_ctor_set(v___x_5300_, 0, v___x_5341_);
v___x_5344_ = v___x_5300_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5355_, 1, v___x_5342_);
v___x_5344_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
lean_object* v___x_5345_; lean_object* v___x_5347_; 
v___x_5345_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
if (v_isShared_5297_ == 0)
{
lean_ctor_set_tag(v___x_5296_, 7);
lean_ctor_set(v___x_5296_, 1, v___x_5345_);
lean_ctor_set(v___x_5296_, 0, v___x_5344_);
v___x_5347_ = v___x_5296_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5344_);
lean_ctor_set(v_reuseFailAlloc_5354_, 1, v___x_5345_);
v___x_5347_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5348_ = lean_array_to_list(v_x_5135_);
v___x_5349_ = lean_box(0);
v___x_5350_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(v___x_5348_, v___x_5349_);
v___x_5351_ = l_Lean_MessageData_ofList(v___x_5350_);
v___x_5352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5352_, 0, v___x_5347_);
lean_ctor_set(v___x_5352_, 1, v___x_5351_);
v___x_5353_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5352_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
return v___x_5353_;
}
}
}
else
{
lean_object* v___x_5356_; 
lean_inc_ref(v_expectedType_5128_);
v___x_5356_ = l_Lean_Meta_isExprDefEq(v_expectedType_5128_, v_snd_5298_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; uint8_t v___x_5358_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref(v___x_5356_);
v___x_5358_ = lean_unbox(v_a_5357_);
if (v___x_5358_ == 0)
{
lean_object* v_toConstantVal_5359_; lean_object* v_name_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5364_; 
lean_dec(v_fst_5294_);
lean_dec_ref(v_x_5135_);
lean_dec_ref(v_x_5134_);
lean_dec(v_val_5133_);
v_toConstantVal_5359_ = lean_ctor_get(v_val_5287_, 0);
lean_inc_ref(v_toConstantVal_5359_);
lean_dec_ref(v_val_5287_);
v_name_5360_ = lean_ctor_get(v_toConstantVal_5359_, 0);
lean_inc(v_name_5360_);
lean_dec_ref(v_toConstantVal_5359_);
v___x_5361_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5);
v___x_5362_ = l_Lean_MessageData_ofExpr(v_expectedType_5128_);
if (v_isShared_5301_ == 0)
{
lean_ctor_set_tag(v___x_5300_, 7);
lean_ctor_set(v___x_5300_, 1, v___x_5362_);
lean_ctor_set(v___x_5300_, 0, v___x_5361_);
v___x_5364_ = v___x_5300_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v___x_5362_);
v___x_5364_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5365_; lean_object* v___x_5367_; 
v___x_5365_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7);
if (v_isShared_5297_ == 0)
{
lean_ctor_set_tag(v___x_5296_, 7);
lean_ctor_set(v___x_5296_, 1, v___x_5365_);
lean_ctor_set(v___x_5296_, 0, v___x_5364_);
v___x_5367_ = v___x_5296_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5364_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v___x_5365_);
v___x_5367_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
uint8_t v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
v___x_5368_ = lean_unbox(v_a_5357_);
lean_dec(v_a_5357_);
v___x_5369_ = l_Lean_MessageData_ofConstName(v_name_5360_, v___x_5368_);
v___x_5370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5370_, 0, v___x_5367_);
lean_ctor_set(v___x_5370_, 1, v___x_5369_);
v___x_5371_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_5372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5372_, 0, v___x_5370_);
lean_ctor_set(v___x_5372_, 1, v___x_5371_);
v___x_5373_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5372_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5373_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5373_);
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
}
else
{
lean_dec(v_a_5357_);
lean_del_object(v___x_5300_);
lean_del_object(v___x_5296_);
v___y_5304_ = v___y_5137_;
v___y_5305_ = v___y_5138_;
v___y_5306_ = v___y_5139_;
v___y_5307_ = v___y_5140_;
goto v___jp_5303_;
}
}
else
{
lean_object* v_a_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5391_; 
lean_del_object(v___x_5300_);
lean_del_object(v___x_5296_);
lean_dec(v_fst_5294_);
lean_dec_ref(v_val_5287_);
lean_dec_ref(v_x_5135_);
lean_dec_ref(v_x_5134_);
lean_dec(v_val_5133_);
lean_dec_ref(v_expectedType_5128_);
v_a_5384_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5391_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5391_ == 0)
{
v___x_5386_ = v___x_5356_;
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_a_5384_);
lean_dec(v___x_5356_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5389_; 
if (v_isShared_5387_ == 0)
{
v___x_5389_ = v___x_5386_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
}
}
v___jp_5303_:
{
lean_object* v_numParams_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
v_numParams_5308_ = lean_ctor_get(v_val_5287_, 3);
lean_inc(v_numParams_5308_);
lean_dec_ref(v_val_5287_);
v___x_5309_ = lean_box(0);
v___x_5310_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_5302_, v_fst_5294_, v_x_5135_, v___x_5129_, v_compile_5130_, v_logCompileErrors_5131_, v_isMeta_5132_, v_val_5133_, v_expectedType_5128_, v_numParams_5308_, v___x_5309_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec_ref(v_x_5135_);
if (lean_obj_tag(v___x_5310_) == 0)
{
size_t v_sz_5311_; size_t v___x_5312_; lean_object* v___x_5313_; 
lean_dec_ref(v___x_5310_);
v_sz_5311_ = lean_array_size(v_fst_5294_);
v___x_5312_ = ((size_t)0ULL);
v___x_5313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_5311_, v___x_5312_, v_fst_5294_, v___y_5305_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5322_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5316_ = v___x_5313_;
v_isShared_5317_ = v_isSharedCheck_5322_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5313_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5322_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5318_; lean_object* v___x_5320_; 
v___x_5318_ = l_Lean_mkAppN(v_x_5134_, v_a_5314_);
lean_dec(v_a_5314_);
if (v_isShared_5317_ == 0)
{
lean_ctor_set(v___x_5316_, 0, v___x_5318_);
v___x_5320_ = v___x_5316_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5318_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5330_; 
lean_dec_ref(v_x_5134_);
v_a_5323_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5325_ = v___x_5313_;
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5313_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___x_5328_; 
if (v_isShared_5326_ == 0)
{
v___x_5328_ = v___x_5325_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5323_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
}
}
else
{
lean_object* v_a_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5338_; 
lean_dec(v_fst_5294_);
lean_dec_ref(v_x_5134_);
v_a_5331_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5333_ = v___x_5310_;
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_a_5331_);
lean_dec(v___x_5310_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5336_; 
if (v_isShared_5334_ == 0)
{
v___x_5336_ = v___x_5333_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_a_5331_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5402_; 
lean_dec_ref(v_val_5287_);
lean_dec_ref(v_x_5135_);
lean_dec_ref(v_x_5134_);
lean_dec(v_val_5133_);
lean_dec_ref(v_expectedType_5128_);
v_a_5395_ = lean_ctor_get(v___x_5291_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5291_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5397_ = v___x_5291_;
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v___x_5291_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
if (v_isShared_5398_ == 0)
{
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_a_5395_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
}
else
{
lean_dec_ref(v_val_5287_);
lean_dec_ref(v_x_5135_);
lean_dec_ref(v_x_5134_);
lean_dec(v_val_5133_);
lean_dec_ref(v_expectedType_5128_);
return v___x_5288_;
}
}
else
{
lean_dec(v_a_5286_);
lean_dec_ref(v_x_5135_);
lean_dec_ref(v_x_5134_);
lean_dec(v_val_5133_);
v___y_5262_ = v___y_5137_;
v___y_5263_ = v___y_5138_;
v___y_5264_ = v___y_5139_;
v___y_5265_ = v___y_5140_;
goto v___jp_5261_;
}
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_dec_ref(v_x_5135_);
lean_dec_ref(v_x_5134_);
lean_dec(v_val_5133_);
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5403_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5285_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5285_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
v___jp_5261_:
{
lean_object* v_options_5266_; uint8_t v_hasTrace_5267_; 
v_options_5266_ = lean_ctor_get(v___y_5264_, 2);
v_hasTrace_5267_ = lean_ctor_get_uint8(v_options_5266_, sizeof(void*)*1);
if (v_hasTrace_5267_ == 0)
{
v___y_5182_ = v___y_5262_;
v___y_5183_ = v___y_5263_;
v___y_5184_ = v___y_5264_;
v_options_5185_ = v_options_5266_;
v___y_5186_ = v___y_5265_;
goto v___jp_5181_;
}
else
{
lean_object* v_inheritedTraceOptions_5268_; lean_object* v___x_5269_; uint8_t v___x_5270_; 
v_inheritedTraceOptions_5268_ = lean_ctor_get(v___y_5264_, 13);
v___x_5269_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_5270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5268_, v_options_5266_, v___x_5269_);
if (v___x_5270_ == 0)
{
v___y_5182_ = v___y_5262_;
v___y_5183_ = v___y_5263_;
v___y_5184_ = v___y_5264_;
v_options_5185_ = v_options_5266_;
v___y_5186_ = v___y_5265_;
goto v___jp_5181_;
}
else
{
lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; 
v___x_5271_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1);
lean_inc_ref(v_inst_5127_);
v___x_5272_ = l_Lean_MessageData_ofExpr(v_inst_5127_);
v___x_5273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5271_);
lean_ctor_set(v___x_5273_, 1, v___x_5272_);
v___x_5274_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5260_, v___x_5273_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_);
if (lean_obj_tag(v___x_5274_) == 0)
{
lean_dec_ref(v___x_5274_);
v___y_5182_ = v___y_5262_;
v___y_5183_ = v___y_5263_;
v___y_5184_ = v___y_5264_;
v_options_5185_ = v_options_5266_;
v___y_5186_ = v___y_5265_;
goto v___jp_5181_;
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5275_ = lean_ctor_get(v___x_5274_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5274_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5274_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5274_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
}
}
}
v___jp_5142_:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_Lean_enableRealizationsForConst(v___y_5143_, v___y_5145_, v___y_5146_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5154_ == 0)
{
lean_object* v_unused_5155_; 
v_unused_5155_ = lean_ctor_get(v___x_5147_, 0);
lean_dec(v_unused_5155_);
v___x_5149_ = v___x_5147_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_dec(v___x_5147_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v___y_5144_);
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___y_5144_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec_ref(v___y_5144_);
v_a_5156_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5147_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5147_);
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
v___jp_5164_:
{
if (v_compile_5130_ == 0)
{
v___y_5143_ = v___y_5165_;
v___y_5144_ = v___y_5166_;
v___y_5145_ = v___y_5167_;
v___y_5146_ = v___y_5168_;
goto v___jp_5142_;
}
else
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5169_ = lean_unsigned_to_nat(1u);
v___x_5170_ = lean_mk_empty_array_with_capacity(v___x_5169_);
lean_inc(v___y_5165_);
v___x_5171_ = lean_array_push(v___x_5170_, v___y_5165_);
v___x_5172_ = l_Lean_compileDecls(v___x_5171_, v_logCompileErrors_5131_, v___y_5167_, v___y_5168_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_dec_ref(v___x_5172_);
v___y_5143_ = v___y_5165_;
v___y_5144_ = v___y_5166_;
v___y_5145_ = v___y_5167_;
v___y_5146_ = v___y_5168_;
goto v___jp_5142_;
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec_ref(v___y_5166_);
lean_dec(v___y_5165_);
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5172_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5172_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
}
v___jp_5181_:
{
lean_object* v___x_5187_; uint8_t v___x_5188_; 
v___x_5187_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5188_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5185_, v___x_5187_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; 
lean_dec_ref(v_expectedType_5128_);
v___x_5189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5189_, 0, v_inst_5127_);
return v___x_5189_;
}
else
{
lean_object* v___x_5190_; 
lean_inc(v___y_5186_);
lean_inc_ref(v___y_5184_);
lean_inc(v___y_5183_);
lean_inc_ref(v___y_5182_);
lean_inc_ref(v_inst_5127_);
v___x_5190_ = lean_infer_type(v_inst_5127_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5186_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v___x_5192_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref(v___x_5190_);
lean_inc_ref(v_expectedType_5128_);
v___x_5192_ = l_Lean_Meta_isExprDefEq(v_expectedType_5128_, v_a_5191_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5186_);
if (lean_obj_tag(v___x_5192_) == 0)
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5245_; 
v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5192_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5195_ = v___x_5192_;
v_isShared_5196_ = v_isSharedCheck_5245_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5192_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5245_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
uint8_t v___x_5197_; 
v___x_5197_ = lean_unbox(v_a_5193_);
if (v___x_5197_ == 0)
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v_a_5200_; uint8_t v___x_5201_; uint8_t v___x_5202_; lean_object* v___x_5203_; 
lean_del_object(v___x_5195_);
v___x_5198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_5199_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_5198_, v___y_5186_);
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc_n(v_a_5200_, 2);
lean_dec_ref(v___x_5199_);
v___x_5201_ = lean_unbox(v_a_5193_);
v___x_5202_ = lean_unbox(v_a_5193_);
lean_dec(v_a_5193_);
v___x_5203_ = l_Lean_Meta_mkAuxDefinition(v_a_5200_, v_expectedType_5128_, v_inst_5127_, v___x_5201_, v___x_5202_, v___x_5129_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5186_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v_a_5204_; uint8_t v___x_5205_; lean_object* v___x_5206_; 
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc(v_a_5204_);
lean_dec_ref(v___x_5203_);
v___x_5205_ = 3;
lean_inc(v_a_5200_);
v___x_5206_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_5200_, v___x_5205_, v___y_5183_, v___y_5186_);
lean_dec_ref(v___x_5206_);
if (v_isMeta_5132_ == 0)
{
v___y_5165_ = v_a_5200_;
v___y_5166_ = v_a_5204_;
v___y_5167_ = v___y_5184_;
v___y_5168_ = v___y_5186_;
goto v___jp_5164_;
}
else
{
lean_object* v___x_5207_; lean_object* v_env_5208_; lean_object* v_nextMacroScope_5209_; lean_object* v_ngen_5210_; lean_object* v_auxDeclNGen_5211_; lean_object* v_traceState_5212_; lean_object* v_messages_5213_; lean_object* v_infoState_5214_; lean_object* v_snapshotTasks_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5240_; 
v___x_5207_ = lean_st_ref_take(v___y_5186_);
v_env_5208_ = lean_ctor_get(v___x_5207_, 0);
v_nextMacroScope_5209_ = lean_ctor_get(v___x_5207_, 1);
v_ngen_5210_ = lean_ctor_get(v___x_5207_, 2);
v_auxDeclNGen_5211_ = lean_ctor_get(v___x_5207_, 3);
v_traceState_5212_ = lean_ctor_get(v___x_5207_, 4);
v_messages_5213_ = lean_ctor_get(v___x_5207_, 6);
v_infoState_5214_ = lean_ctor_get(v___x_5207_, 7);
v_snapshotTasks_5215_ = lean_ctor_get(v___x_5207_, 8);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5240_ == 0)
{
lean_object* v_unused_5241_; 
v_unused_5241_ = lean_ctor_get(v___x_5207_, 5);
lean_dec(v_unused_5241_);
v___x_5217_ = v___x_5207_;
v_isShared_5218_ = v_isSharedCheck_5240_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_snapshotTasks_5215_);
lean_inc(v_infoState_5214_);
lean_inc(v_messages_5213_);
lean_inc(v_traceState_5212_);
lean_inc(v_auxDeclNGen_5211_);
lean_inc(v_ngen_5210_);
lean_inc(v_nextMacroScope_5209_);
lean_inc(v_env_5208_);
lean_dec(v___x_5207_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5240_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5222_; 
lean_inc(v_a_5200_);
v___x_5219_ = l_Lean_markMeta(v_env_5208_, v_a_5200_);
v___x_5220_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_5218_ == 0)
{
lean_ctor_set(v___x_5217_, 5, v___x_5220_);
lean_ctor_set(v___x_5217_, 0, v___x_5219_);
v___x_5222_ = v___x_5217_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5219_);
lean_ctor_set(v_reuseFailAlloc_5239_, 1, v_nextMacroScope_5209_);
lean_ctor_set(v_reuseFailAlloc_5239_, 2, v_ngen_5210_);
lean_ctor_set(v_reuseFailAlloc_5239_, 3, v_auxDeclNGen_5211_);
lean_ctor_set(v_reuseFailAlloc_5239_, 4, v_traceState_5212_);
lean_ctor_set(v_reuseFailAlloc_5239_, 5, v___x_5220_);
lean_ctor_set(v_reuseFailAlloc_5239_, 6, v_messages_5213_);
lean_ctor_set(v_reuseFailAlloc_5239_, 7, v_infoState_5214_);
lean_ctor_set(v_reuseFailAlloc_5239_, 8, v_snapshotTasks_5215_);
v___x_5222_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v_mctx_5225_; lean_object* v_zetaDeltaFVarIds_5226_; lean_object* v_postponed_5227_; lean_object* v_diag_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5237_; 
v___x_5223_ = lean_st_ref_set(v___y_5186_, v___x_5222_);
v___x_5224_ = lean_st_ref_take(v___y_5183_);
v_mctx_5225_ = lean_ctor_get(v___x_5224_, 0);
v_zetaDeltaFVarIds_5226_ = lean_ctor_get(v___x_5224_, 2);
v_postponed_5227_ = lean_ctor_get(v___x_5224_, 3);
v_diag_5228_ = lean_ctor_get(v___x_5224_, 4);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5237_ == 0)
{
lean_object* v_unused_5238_; 
v_unused_5238_ = lean_ctor_get(v___x_5224_, 1);
lean_dec(v_unused_5238_);
v___x_5230_ = v___x_5224_;
v_isShared_5231_ = v_isSharedCheck_5237_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_diag_5228_);
lean_inc(v_postponed_5227_);
lean_inc(v_zetaDeltaFVarIds_5226_);
lean_inc(v_mctx_5225_);
lean_dec(v___x_5224_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5237_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5232_; lean_object* v___x_5234_; 
v___x_5232_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 1, v___x_5232_);
v___x_5234_ = v___x_5230_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_mctx_5225_);
lean_ctor_set(v_reuseFailAlloc_5236_, 1, v___x_5232_);
lean_ctor_set(v_reuseFailAlloc_5236_, 2, v_zetaDeltaFVarIds_5226_);
lean_ctor_set(v_reuseFailAlloc_5236_, 3, v_postponed_5227_);
lean_ctor_set(v_reuseFailAlloc_5236_, 4, v_diag_5228_);
v___x_5234_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
lean_object* v___x_5235_; 
v___x_5235_ = lean_st_ref_set(v___y_5183_, v___x_5234_);
v___y_5165_ = v_a_5200_;
v___y_5166_ = v_a_5204_;
v___y_5167_ = v___y_5184_;
v___y_5168_ = v___y_5186_;
goto v___jp_5164_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5200_);
return v___x_5203_;
}
}
else
{
lean_object* v___x_5243_; 
lean_dec(v_a_5193_);
lean_dec_ref(v_expectedType_5128_);
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 0, v_inst_5127_);
v___x_5243_ = v___x_5195_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_inst_5127_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
else
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5246_ = lean_ctor_get(v___x_5192_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5192_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5192_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5192_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5249_ == 0)
{
v___x_5251_ = v___x_5248_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
return v___x_5190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object* v_inst_5411_, lean_object* v_expectedType_5412_, uint8_t v___x_5413_, uint8_t v_compile_5414_, uint8_t v_logCompileErrors_5415_, uint8_t v_isMeta_5416_, lean_object* v_val_5417_, lean_object* v_x_5418_, lean_object* v_x_5419_, lean_object* v_x_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_){
_start:
{
lean_object* v___y_5427_; lean_object* v___y_5428_; lean_object* v___y_5429_; lean_object* v___y_5430_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5466_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v_options_5469_; lean_object* v___y_5470_; 
if (lean_obj_tag(v_x_5418_) == 5)
{
lean_object* v_fn_5538_; lean_object* v_arg_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; 
v_fn_5538_ = lean_ctor_get(v_x_5418_, 0);
lean_inc_ref(v_fn_5538_);
v_arg_5539_ = lean_ctor_get(v_x_5418_, 1);
lean_inc_ref(v_arg_5539_);
lean_dec_ref(v_x_5418_);
v___x_5540_ = lean_array_set(v_x_5419_, v_x_5420_, v_arg_5539_);
v___x_5541_ = lean_unsigned_to_nat(1u);
v___x_5542_ = lean_nat_sub(v_x_5420_, v___x_5541_);
v___x_5543_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(v_inst_5411_, v_expectedType_5412_, v___x_5413_, v_compile_5414_, v_logCompileErrors_5415_, v_isMeta_5416_, v_val_5417_, v_fn_5538_, v___x_5540_, v___x_5542_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
return v___x_5543_;
}
else
{
lean_object* v_cls_5544_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v___x_5567_; 
v_cls_5544_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5567_ = l_Lean_Expr_constName_x3f(v_x_5418_);
if (lean_obj_tag(v___x_5567_) == 0)
{
lean_dec_ref(v_x_5419_);
lean_dec_ref(v_x_5418_);
lean_dec(v_val_5417_);
v___y_5546_ = v___y_5421_;
v___y_5547_ = v___y_5422_;
v___y_5548_ = v___y_5423_;
v___y_5549_ = v___y_5424_;
goto v___jp_5545_;
}
else
{
lean_object* v_val_5568_; lean_object* v___x_5569_; 
v_val_5568_ = lean_ctor_get(v___x_5567_, 0);
lean_inc(v_val_5568_);
lean_dec_ref(v___x_5567_);
v___x_5569_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_5568_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
if (lean_obj_tag(v___x_5569_) == 0)
{
lean_object* v_a_5570_; 
v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
lean_inc(v_a_5570_);
lean_dec_ref(v___x_5569_);
if (lean_obj_tag(v_a_5570_) == 6)
{
lean_object* v_val_5571_; lean_object* v___x_5572_; 
lean_dec_ref(v_inst_5411_);
v_val_5571_ = lean_ctor_get(v_a_5570_, 0);
lean_inc_ref(v_val_5571_);
lean_dec_ref(v_a_5570_);
lean_inc(v___y_5424_);
lean_inc_ref(v___y_5423_);
lean_inc(v___y_5422_);
lean_inc_ref(v___y_5421_);
lean_inc_ref(v_x_5418_);
v___x_5572_ = lean_infer_type(v_x_5418_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v_a_5573_; uint8_t v___x_5574_; lean_object* v___x_5575_; 
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
lean_inc(v_a_5573_);
lean_dec_ref(v___x_5572_);
v___x_5574_ = 0;
v___x_5575_ = l_Lean_Meta_forallMetaTelescope(v_a_5573_, v___x_5574_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v_a_5576_; lean_object* v_snd_5577_; lean_object* v_fst_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5678_; 
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
lean_inc(v_a_5576_);
lean_dec_ref(v___x_5575_);
v_snd_5577_ = lean_ctor_get(v_a_5576_, 1);
v_fst_5578_ = lean_ctor_get(v_a_5576_, 0);
v_isSharedCheck_5678_ = !lean_is_exclusive(v_a_5576_);
if (v_isSharedCheck_5678_ == 0)
{
v___x_5580_ = v_a_5576_;
v_isShared_5581_ = v_isSharedCheck_5678_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_snd_5577_);
lean_inc(v_fst_5578_);
lean_dec(v_a_5576_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5678_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v_snd_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5676_; 
v_snd_5582_ = lean_ctor_get(v_snd_5577_, 1);
v_isSharedCheck_5676_ = !lean_is_exclusive(v_snd_5577_);
if (v_isSharedCheck_5676_ == 0)
{
lean_object* v_unused_5677_; 
v_unused_5677_ = lean_ctor_get(v_snd_5577_, 0);
lean_dec(v_unused_5677_);
v___x_5584_ = v_snd_5577_;
v_isShared_5585_ = v_isSharedCheck_5676_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_snd_5582_);
lean_dec(v_snd_5577_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5676_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5586_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___x_5623_; uint8_t v___x_5624_; 
v___x_5586_ = lean_array_get_size(v_x_5419_);
v___x_5623_ = lean_array_get_size(v_fst_5578_);
v___x_5624_ = lean_nat_dec_eq(v___x_5586_, v___x_5623_);
if (v___x_5624_ == 0)
{
lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5628_; 
lean_dec(v_snd_5582_);
lean_dec(v_fst_5578_);
lean_dec_ref(v_val_5571_);
lean_dec(v_val_5417_);
lean_dec_ref(v_expectedType_5412_);
v___x_5625_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__3);
v___x_5626_ = l_Lean_MessageData_ofExpr(v_x_5418_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set_tag(v___x_5584_, 7);
lean_ctor_set(v___x_5584_, 1, v___x_5626_);
lean_ctor_set(v___x_5584_, 0, v___x_5625_);
v___x_5628_ = v___x_5584_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5625_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v___x_5626_);
v___x_5628_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5629_; lean_object* v___x_5631_; 
v___x_5629_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___lam__5___closed__3);
if (v_isShared_5581_ == 0)
{
lean_ctor_set_tag(v___x_5580_, 7);
lean_ctor_set(v___x_5580_, 1, v___x_5629_);
lean_ctor_set(v___x_5580_, 0, v___x_5628_);
v___x_5631_ = v___x_5580_;
goto v_reusejp_5630_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___x_5628_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v___x_5629_);
v___x_5631_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5630_;
}
v_reusejp_5630_:
{
lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v___x_5632_ = lean_array_to_list(v_x_5419_);
v___x_5633_ = lean_box(0);
v___x_5634_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__7(v___x_5632_, v___x_5633_);
v___x_5635_ = l_Lean_MessageData_ofList(v___x_5634_);
v___x_5636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5631_);
lean_ctor_set(v___x_5636_, 1, v___x_5635_);
v___x_5637_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5636_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
return v___x_5637_;
}
}
}
else
{
lean_object* v___x_5640_; 
lean_inc_ref(v_expectedType_5412_);
v___x_5640_ = l_Lean_Meta_isExprDefEq(v_expectedType_5412_, v_snd_5582_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
if (lean_obj_tag(v___x_5640_) == 0)
{
lean_object* v_a_5641_; uint8_t v___x_5642_; 
v_a_5641_ = lean_ctor_get(v___x_5640_, 0);
lean_inc(v_a_5641_);
lean_dec_ref(v___x_5640_);
v___x_5642_ = lean_unbox(v_a_5641_);
if (v___x_5642_ == 0)
{
lean_object* v_toConstantVal_5643_; lean_object* v_name_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5648_; 
lean_dec(v_fst_5578_);
lean_dec_ref(v_x_5419_);
lean_dec_ref(v_x_5418_);
lean_dec(v_val_5417_);
v_toConstantVal_5643_ = lean_ctor_get(v_val_5571_, 0);
lean_inc_ref(v_toConstantVal_5643_);
lean_dec_ref(v_val_5571_);
v_name_5644_ = lean_ctor_get(v_toConstantVal_5643_, 0);
lean_inc(v_name_5644_);
lean_dec_ref(v_toConstantVal_5643_);
v___x_5645_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__5);
v___x_5646_ = l_Lean_MessageData_ofExpr(v_expectedType_5412_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set_tag(v___x_5584_, 7);
lean_ctor_set(v___x_5584_, 1, v___x_5646_);
lean_ctor_set(v___x_5584_, 0, v___x_5645_);
v___x_5648_ = v___x_5584_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v___x_5645_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v___x_5646_);
v___x_5648_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
lean_object* v___x_5649_; lean_object* v___x_5651_; 
v___x_5649_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__7);
if (v_isShared_5581_ == 0)
{
lean_ctor_set_tag(v___x_5580_, 7);
lean_ctor_set(v___x_5580_, 1, v___x_5649_);
lean_ctor_set(v___x_5580_, 0, v___x_5648_);
v___x_5651_ = v___x_5580_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v___x_5648_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v___x_5649_);
v___x_5651_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
uint8_t v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
v___x_5652_ = lean_unbox(v_a_5641_);
lean_dec(v_a_5641_);
v___x_5653_ = l_Lean_MessageData_ofConstName(v_name_5644_, v___x_5652_);
v___x_5654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5651_);
lean_ctor_set(v___x_5654_, 1, v___x_5653_);
v___x_5655_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6);
v___x_5656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5654_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5656_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
v_a_5658_ = lean_ctor_get(v___x_5657_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5657_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5657_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5657_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
}
else
{
lean_dec(v_a_5641_);
lean_del_object(v___x_5584_);
lean_del_object(v___x_5580_);
v___y_5588_ = v___y_5421_;
v___y_5589_ = v___y_5422_;
v___y_5590_ = v___y_5423_;
v___y_5591_ = v___y_5424_;
goto v___jp_5587_;
}
}
else
{
lean_object* v_a_5668_; lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5675_; 
lean_del_object(v___x_5584_);
lean_del_object(v___x_5580_);
lean_dec(v_fst_5578_);
lean_dec_ref(v_val_5571_);
lean_dec_ref(v_x_5419_);
lean_dec_ref(v_x_5418_);
lean_dec(v_val_5417_);
lean_dec_ref(v_expectedType_5412_);
v_a_5668_ = lean_ctor_get(v___x_5640_, 0);
v_isSharedCheck_5675_ = !lean_is_exclusive(v___x_5640_);
if (v_isSharedCheck_5675_ == 0)
{
v___x_5670_ = v___x_5640_;
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
else
{
lean_inc(v_a_5668_);
lean_dec(v___x_5640_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v___x_5673_; 
if (v_isShared_5671_ == 0)
{
v___x_5673_ = v___x_5670_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
v___x_5673_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
return v___x_5673_;
}
}
}
}
v___jp_5587_:
{
lean_object* v_numParams_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v_numParams_5592_ = lean_ctor_get(v_val_5571_, 3);
lean_inc(v_numParams_5592_);
lean_dec_ref(v_val_5571_);
v___x_5593_ = lean_box(0);
v___x_5594_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_5586_, v_fst_5578_, v_x_5419_, v___x_5413_, v_compile_5414_, v_logCompileErrors_5415_, v_isMeta_5416_, v_val_5417_, v_expectedType_5412_, v_numParams_5592_, v___x_5593_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_);
lean_dec_ref(v_x_5419_);
if (lean_obj_tag(v___x_5594_) == 0)
{
size_t v_sz_5595_; size_t v___x_5596_; lean_object* v___x_5597_; 
lean_dec_ref(v___x_5594_);
v_sz_5595_ = lean_array_size(v_fst_5578_);
v___x_5596_ = ((size_t)0ULL);
v___x_5597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_5595_, v___x_5596_, v_fst_5578_, v___y_5589_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5606_; 
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5600_ = v___x_5597_;
v_isShared_5601_ = v_isSharedCheck_5606_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_a_5598_);
lean_dec(v___x_5597_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5606_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5602_ = l_Lean_mkAppN(v_x_5418_, v_a_5598_);
lean_dec(v_a_5598_);
if (v_isShared_5601_ == 0)
{
lean_ctor_set(v___x_5600_, 0, v___x_5602_);
v___x_5604_ = v___x_5600_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
else
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5614_; 
lean_dec_ref(v_x_5418_);
v_a_5607_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5609_ = v___x_5597_;
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v___x_5597_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5610_ == 0)
{
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_dec(v_fst_5578_);
lean_dec_ref(v_x_5418_);
v_a_5615_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5594_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5594_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5686_; 
lean_dec_ref(v_val_5571_);
lean_dec_ref(v_x_5419_);
lean_dec_ref(v_x_5418_);
lean_dec(v_val_5417_);
lean_dec_ref(v_expectedType_5412_);
v_a_5679_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5686_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5686_ == 0)
{
v___x_5681_ = v___x_5575_;
v_isShared_5682_ = v_isSharedCheck_5686_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_a_5679_);
lean_dec(v___x_5575_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5686_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v___x_5684_; 
if (v_isShared_5682_ == 0)
{
v___x_5684_ = v___x_5681_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5685_; 
v_reuseFailAlloc_5685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_a_5679_);
v___x_5684_ = v_reuseFailAlloc_5685_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
return v___x_5684_;
}
}
}
}
else
{
lean_dec_ref(v_val_5571_);
lean_dec_ref(v_x_5419_);
lean_dec_ref(v_x_5418_);
lean_dec(v_val_5417_);
lean_dec_ref(v_expectedType_5412_);
return v___x_5572_;
}
}
else
{
lean_dec(v_a_5570_);
lean_dec_ref(v_x_5419_);
lean_dec_ref(v_x_5418_);
lean_dec(v_val_5417_);
v___y_5546_ = v___y_5421_;
v___y_5547_ = v___y_5422_;
v___y_5548_ = v___y_5423_;
v___y_5549_ = v___y_5424_;
goto v___jp_5545_;
}
}
else
{
lean_object* v_a_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5694_; 
lean_dec_ref(v_x_5419_);
lean_dec_ref(v_x_5418_);
lean_dec(v_val_5417_);
lean_dec_ref(v_expectedType_5412_);
lean_dec_ref(v_inst_5411_);
v_a_5687_ = lean_ctor_get(v___x_5569_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5569_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5689_ = v___x_5569_;
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_a_5687_);
lean_dec(v___x_5569_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5692_; 
if (v_isShared_5690_ == 0)
{
v___x_5692_ = v___x_5689_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_a_5687_);
v___x_5692_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
return v___x_5692_;
}
}
}
}
v___jp_5545_:
{
lean_object* v_options_5550_; uint8_t v_hasTrace_5551_; 
v_options_5550_ = lean_ctor_get(v___y_5548_, 2);
v_hasTrace_5551_ = lean_ctor_get_uint8(v_options_5550_, sizeof(void*)*1);
if (v_hasTrace_5551_ == 0)
{
v___y_5466_ = v___y_5546_;
v___y_5467_ = v___y_5547_;
v___y_5468_ = v___y_5548_;
v_options_5469_ = v_options_5550_;
v___y_5470_ = v___y_5549_;
goto v___jp_5465_;
}
else
{
lean_object* v_inheritedTraceOptions_5552_; lean_object* v___x_5553_; uint8_t v___x_5554_; 
v_inheritedTraceOptions_5552_ = lean_ctor_get(v___y_5548_, 13);
v___x_5553_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_5554_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5552_, v_options_5550_, v___x_5553_);
if (v___x_5554_ == 0)
{
v___y_5466_ = v___y_5546_;
v___y_5467_ = v___y_5547_;
v___y_5468_ = v___y_5548_;
v_options_5469_ = v_options_5550_;
v___y_5470_ = v___y_5549_;
goto v___jp_5465_;
}
else
{
lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5555_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___closed__1);
lean_inc_ref(v_inst_5411_);
v___x_5556_ = l_Lean_MessageData_ofExpr(v_inst_5411_);
v___x_5557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5555_);
lean_ctor_set(v___x_5557_, 1, v___x_5556_);
v___x_5558_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5544_, v___x_5557_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
if (lean_obj_tag(v___x_5558_) == 0)
{
lean_dec_ref(v___x_5558_);
v___y_5466_ = v___y_5546_;
v___y_5467_ = v___y_5547_;
v___y_5468_ = v___y_5548_;
v_options_5469_ = v_options_5550_;
v___y_5470_ = v___y_5549_;
goto v___jp_5465_;
}
else
{
lean_object* v_a_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5566_; 
lean_dec_ref(v_expectedType_5412_);
lean_dec_ref(v_inst_5411_);
v_a_5559_ = lean_ctor_get(v___x_5558_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5558_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5561_ = v___x_5558_;
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5558_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5564_; 
if (v_isShared_5562_ == 0)
{
v___x_5564_ = v___x_5561_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
}
}
}
}
v___jp_5426_:
{
lean_object* v___x_5431_; 
v___x_5431_ = l_Lean_enableRealizationsForConst(v___y_5427_, v___y_5429_, v___y_5430_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5438_; 
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5438_ == 0)
{
lean_object* v_unused_5439_; 
v_unused_5439_ = lean_ctor_get(v___x_5431_, 0);
lean_dec(v_unused_5439_);
v___x_5433_ = v___x_5431_;
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
else
{
lean_dec(v___x_5431_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5436_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 0, v___y_5428_);
v___x_5436_ = v___x_5433_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___y_5428_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
else
{
lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
lean_dec_ref(v___y_5428_);
v_a_5440_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5442_ = v___x_5431_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_dec(v___x_5431_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5445_; 
if (v_isShared_5443_ == 0)
{
v___x_5445_ = v___x_5442_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5440_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
}
v___jp_5448_:
{
if (v_compile_5414_ == 0)
{
v___y_5427_ = v___y_5449_;
v___y_5428_ = v___y_5450_;
v___y_5429_ = v___y_5451_;
v___y_5430_ = v___y_5452_;
goto v___jp_5426_;
}
else
{
lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___x_5453_ = lean_unsigned_to_nat(1u);
v___x_5454_ = lean_mk_empty_array_with_capacity(v___x_5453_);
lean_inc(v___y_5449_);
v___x_5455_ = lean_array_push(v___x_5454_, v___y_5449_);
v___x_5456_ = l_Lean_compileDecls(v___x_5455_, v_logCompileErrors_5415_, v___y_5451_, v___y_5452_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_dec_ref(v___x_5456_);
v___y_5427_ = v___y_5449_;
v___y_5428_ = v___y_5450_;
v___y_5429_ = v___y_5451_;
v___y_5430_ = v___y_5452_;
goto v___jp_5426_;
}
else
{
lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5464_; 
lean_dec_ref(v___y_5450_);
lean_dec(v___y_5449_);
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5464_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5464_ == 0)
{
v___x_5459_ = v___x_5456_;
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_dec(v___x_5456_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5462_; 
if (v_isShared_5460_ == 0)
{
v___x_5462_ = v___x_5459_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5457_);
v___x_5462_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
return v___x_5462_;
}
}
}
}
}
v___jp_5465_:
{
lean_object* v___x_5471_; uint8_t v___x_5472_; 
v___x_5471_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5472_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5469_, v___x_5471_);
if (v___x_5472_ == 0)
{
lean_object* v___x_5473_; 
lean_dec_ref(v_expectedType_5412_);
v___x_5473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5473_, 0, v_inst_5411_);
return v___x_5473_;
}
else
{
lean_object* v___x_5474_; 
lean_inc(v___y_5470_);
lean_inc_ref(v___y_5468_);
lean_inc(v___y_5467_);
lean_inc_ref(v___y_5466_);
lean_inc_ref(v_inst_5411_);
v___x_5474_ = lean_infer_type(v_inst_5411_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5470_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v_a_5475_; lean_object* v___x_5476_; 
v_a_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_a_5475_);
lean_dec_ref(v___x_5474_);
lean_inc_ref(v_expectedType_5412_);
v___x_5476_ = l_Lean_Meta_isExprDefEq(v_expectedType_5412_, v_a_5475_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5470_);
if (lean_obj_tag(v___x_5476_) == 0)
{
lean_object* v_a_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5529_; 
v_a_5477_ = lean_ctor_get(v___x_5476_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5476_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5479_ = v___x_5476_;
v_isShared_5480_ = v_isSharedCheck_5529_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_a_5477_);
lean_dec(v___x_5476_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5529_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
uint8_t v___x_5481_; 
v___x_5481_ = lean_unbox(v_a_5477_);
if (v___x_5481_ == 0)
{
lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v_a_5484_; uint8_t v___x_5485_; uint8_t v___x_5486_; lean_object* v___x_5487_; 
lean_del_object(v___x_5479_);
v___x_5482_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___closed__1));
v___x_5483_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_5482_, v___y_5470_);
v_a_5484_ = lean_ctor_get(v___x_5483_, 0);
lean_inc_n(v_a_5484_, 2);
lean_dec_ref(v___x_5483_);
v___x_5485_ = lean_unbox(v_a_5477_);
v___x_5486_ = lean_unbox(v_a_5477_);
lean_dec(v_a_5477_);
v___x_5487_ = l_Lean_Meta_mkAuxDefinition(v_a_5484_, v_expectedType_5412_, v_inst_5411_, v___x_5485_, v___x_5486_, v___x_5413_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5470_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; uint8_t v___x_5489_; lean_object* v___x_5490_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
lean_dec_ref(v___x_5487_);
v___x_5489_ = 3;
lean_inc(v_a_5484_);
v___x_5490_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_5484_, v___x_5489_, v___y_5467_, v___y_5470_);
lean_dec_ref(v___x_5490_);
if (v_isMeta_5416_ == 0)
{
v___y_5449_ = v_a_5484_;
v___y_5450_ = v_a_5488_;
v___y_5451_ = v___y_5468_;
v___y_5452_ = v___y_5470_;
goto v___jp_5448_;
}
else
{
lean_object* v___x_5491_; lean_object* v_env_5492_; lean_object* v_nextMacroScope_5493_; lean_object* v_ngen_5494_; lean_object* v_auxDeclNGen_5495_; lean_object* v_traceState_5496_; lean_object* v_messages_5497_; lean_object* v_infoState_5498_; lean_object* v_snapshotTasks_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5524_; 
v___x_5491_ = lean_st_ref_take(v___y_5470_);
v_env_5492_ = lean_ctor_get(v___x_5491_, 0);
v_nextMacroScope_5493_ = lean_ctor_get(v___x_5491_, 1);
v_ngen_5494_ = lean_ctor_get(v___x_5491_, 2);
v_auxDeclNGen_5495_ = lean_ctor_get(v___x_5491_, 3);
v_traceState_5496_ = lean_ctor_get(v___x_5491_, 4);
v_messages_5497_ = lean_ctor_get(v___x_5491_, 6);
v_infoState_5498_ = lean_ctor_get(v___x_5491_, 7);
v_snapshotTasks_5499_ = lean_ctor_get(v___x_5491_, 8);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5491_);
if (v_isSharedCheck_5524_ == 0)
{
lean_object* v_unused_5525_; 
v_unused_5525_ = lean_ctor_get(v___x_5491_, 5);
lean_dec(v_unused_5525_);
v___x_5501_ = v___x_5491_;
v_isShared_5502_ = v_isSharedCheck_5524_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_snapshotTasks_5499_);
lean_inc(v_infoState_5498_);
lean_inc(v_messages_5497_);
lean_inc(v_traceState_5496_);
lean_inc(v_auxDeclNGen_5495_);
lean_inc(v_ngen_5494_);
lean_inc(v_nextMacroScope_5493_);
lean_inc(v_env_5492_);
lean_dec(v___x_5491_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5524_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5506_; 
lean_inc(v_a_5484_);
v___x_5503_ = l_Lean_markMeta(v_env_5492_, v_a_5484_);
v___x_5504_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 5, v___x_5504_);
lean_ctor_set(v___x_5501_, 0, v___x_5503_);
v___x_5506_ = v___x_5501_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5503_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_nextMacroScope_5493_);
lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_ngen_5494_);
lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_auxDeclNGen_5495_);
lean_ctor_set(v_reuseFailAlloc_5523_, 4, v_traceState_5496_);
lean_ctor_set(v_reuseFailAlloc_5523_, 5, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5523_, 6, v_messages_5497_);
lean_ctor_set(v_reuseFailAlloc_5523_, 7, v_infoState_5498_);
lean_ctor_set(v_reuseFailAlloc_5523_, 8, v_snapshotTasks_5499_);
v___x_5506_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v_mctx_5509_; lean_object* v_zetaDeltaFVarIds_5510_; lean_object* v_postponed_5511_; lean_object* v_diag_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5521_; 
v___x_5507_ = lean_st_ref_set(v___y_5470_, v___x_5506_);
v___x_5508_ = lean_st_ref_take(v___y_5467_);
v_mctx_5509_ = lean_ctor_get(v___x_5508_, 0);
v_zetaDeltaFVarIds_5510_ = lean_ctor_get(v___x_5508_, 2);
v_postponed_5511_ = lean_ctor_get(v___x_5508_, 3);
v_diag_5512_ = lean_ctor_get(v___x_5508_, 4);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5508_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; 
v_unused_5522_ = lean_ctor_get(v___x_5508_, 1);
lean_dec(v_unused_5522_);
v___x_5514_ = v___x_5508_;
v_isShared_5515_ = v_isSharedCheck_5521_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_diag_5512_);
lean_inc(v_postponed_5511_);
lean_inc(v_zetaDeltaFVarIds_5510_);
lean_inc(v_mctx_5509_);
lean_dec(v___x_5508_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5521_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5516_; lean_object* v___x_5518_; 
v___x_5516_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5516_);
v___x_5518_ = v___x_5514_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_mctx_5509_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v___x_5516_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_zetaDeltaFVarIds_5510_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v_postponed_5511_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v_diag_5512_);
v___x_5518_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
lean_object* v___x_5519_; 
v___x_5519_ = lean_st_ref_set(v___y_5467_, v___x_5518_);
v___y_5449_ = v_a_5484_;
v___y_5450_ = v_a_5488_;
v___y_5451_ = v___y_5468_;
v___y_5452_ = v___y_5470_;
goto v___jp_5448_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5484_);
return v___x_5487_;
}
}
else
{
lean_object* v___x_5527_; 
lean_dec(v_a_5477_);
lean_dec_ref(v_expectedType_5412_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 0, v_inst_5411_);
v___x_5527_ = v___x_5479_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_inst_5411_);
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
lean_dec_ref(v_expectedType_5412_);
lean_dec_ref(v_inst_5411_);
v_a_5530_ = lean_ctor_get(v___x_5476_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5476_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5476_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5476_);
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
lean_dec_ref(v_expectedType_5412_);
lean_dec_ref(v_inst_5411_);
return v___x_5474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object* v_expectedType_5695_, lean_object* v_inst_5696_, uint8_t v___x_5697_, uint8_t v_compile_5698_, uint8_t v_logCompileErrors_5699_, uint8_t v_isMeta_5700_, lean_object* v_val_5701_, lean_object* v_____r_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
lean_object* v___x_5708_; 
lean_inc_ref(v_expectedType_5695_);
v___x_5708_ = l_Lean_Meta_isProp(v_expectedType_5695_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
if (lean_obj_tag(v___x_5708_) == 0)
{
lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5730_; 
v_a_5709_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5711_ = v___x_5708_;
v_isShared_5712_ = v_isSharedCheck_5730_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_dec(v___x_5708_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5730_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
uint8_t v___x_5713_; 
v___x_5713_ = lean_unbox(v_a_5709_);
lean_dec(v_a_5709_);
if (v___x_5713_ == 0)
{
lean_object* v___x_5714_; 
lean_del_object(v___x_5711_);
lean_inc(v___y_5706_);
lean_inc_ref(v___y_5705_);
lean_inc(v___y_5704_);
lean_inc_ref(v___y_5703_);
lean_inc_ref(v_inst_5696_);
v___x_5714_ = lean_whnf(v_inst_5696_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
if (lean_obj_tag(v___x_5714_) == 0)
{
lean_object* v_a_5715_; lean_object* v_dummy_5716_; lean_object* v_nargs_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v_a_5715_ = lean_ctor_get(v___x_5714_, 0);
lean_inc(v_a_5715_);
lean_dec_ref(v___x_5714_);
v_dummy_5716_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5717_ = l_Lean_Expr_getAppNumArgs(v_a_5715_);
lean_inc(v_nargs_5717_);
v___x_5718_ = lean_mk_array(v_nargs_5717_, v_dummy_5716_);
v___x_5719_ = lean_unsigned_to_nat(1u);
v___x_5720_ = lean_nat_sub(v_nargs_5717_, v___x_5719_);
lean_dec(v_nargs_5717_);
v___x_5721_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_5696_, v_expectedType_5695_, v___x_5697_, v_compile_5698_, v_logCompileErrors_5699_, v_isMeta_5700_, v_val_5701_, v_a_5715_, v___x_5718_, v___x_5720_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
lean_dec(v___x_5720_);
return v___x_5721_;
}
else
{
lean_dec(v_val_5701_);
lean_dec_ref(v_inst_5696_);
lean_dec_ref(v_expectedType_5695_);
return v___x_5714_;
}
}
else
{
lean_object* v_options_5722_; lean_object* v___x_5723_; uint8_t v___x_5724_; 
lean_dec(v_val_5701_);
v_options_5722_ = lean_ctor_get(v___y_5705_, 2);
v___x_5723_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5724_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5722_, v___x_5723_);
if (v___x_5724_ == 0)
{
lean_object* v___x_5726_; 
lean_dec_ref(v_expectedType_5695_);
if (v_isShared_5712_ == 0)
{
lean_ctor_set(v___x_5711_, 0, v_inst_5696_);
v___x_5726_ = v___x_5711_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_inst_5696_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
else
{
lean_object* v___x_5728_; lean_object* v___x_5729_; 
lean_del_object(v___x_5711_);
v___x_5728_ = lean_box(0);
v___x_5729_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5695_, v_inst_5696_, v___x_5697_, v___x_5728_, v___x_5697_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
return v___x_5729_;
}
}
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5738_; 
lean_dec(v_val_5701_);
lean_dec_ref(v_inst_5696_);
lean_dec_ref(v_expectedType_5695_);
v_a_5731_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5733_ = v___x_5708_;
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5708_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5736_; 
if (v_isShared_5734_ == 0)
{
v___x_5736_ = v___x_5733_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object* v_inst_5739_, lean_object* v_expectedType_5740_, uint8_t v_compile_5741_, uint8_t v_logCompileErrors_5742_, uint8_t v_isMeta_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_){
_start:
{
lean_object* v___x_5749_; lean_object* v_options_5750_; uint8_t v_foApprox_5751_; uint8_t v_ctxApprox_5752_; uint8_t v_quasiPatternApprox_5753_; uint8_t v_constApprox_5754_; uint8_t v_isDefEqStuckEx_5755_; uint8_t v_unificationHints_5756_; uint8_t v_proofIrrelevance_5757_; uint8_t v_assignSyntheticOpaque_5758_; uint8_t v_offsetCnstrs_5759_; uint8_t v_etaStruct_5760_; uint8_t v_univApprox_5761_; uint8_t v_iota_5762_; uint8_t v_beta_5763_; uint8_t v_proj_5764_; uint8_t v_zeta_5765_; uint8_t v_zetaDelta_5766_; uint8_t v_zetaUnused_5767_; uint8_t v_zetaHave_5768_; lean_object* v___x_5770_; uint8_t v_isShared_5771_; uint8_t v_isSharedCheck_6019_; 
v___x_5749_ = l_Lean_Meta_Context_config(v_a_5744_);
v_options_5750_ = lean_ctor_get(v_a_5746_, 2);
v_foApprox_5751_ = lean_ctor_get_uint8(v___x_5749_, 0);
v_ctxApprox_5752_ = lean_ctor_get_uint8(v___x_5749_, 1);
v_quasiPatternApprox_5753_ = lean_ctor_get_uint8(v___x_5749_, 2);
v_constApprox_5754_ = lean_ctor_get_uint8(v___x_5749_, 3);
v_isDefEqStuckEx_5755_ = lean_ctor_get_uint8(v___x_5749_, 4);
v_unificationHints_5756_ = lean_ctor_get_uint8(v___x_5749_, 5);
v_proofIrrelevance_5757_ = lean_ctor_get_uint8(v___x_5749_, 6);
v_assignSyntheticOpaque_5758_ = lean_ctor_get_uint8(v___x_5749_, 7);
v_offsetCnstrs_5759_ = lean_ctor_get_uint8(v___x_5749_, 8);
v_etaStruct_5760_ = lean_ctor_get_uint8(v___x_5749_, 10);
v_univApprox_5761_ = lean_ctor_get_uint8(v___x_5749_, 11);
v_iota_5762_ = lean_ctor_get_uint8(v___x_5749_, 12);
v_beta_5763_ = lean_ctor_get_uint8(v___x_5749_, 13);
v_proj_5764_ = lean_ctor_get_uint8(v___x_5749_, 14);
v_zeta_5765_ = lean_ctor_get_uint8(v___x_5749_, 15);
v_zetaDelta_5766_ = lean_ctor_get_uint8(v___x_5749_, 16);
v_zetaUnused_5767_ = lean_ctor_get_uint8(v___x_5749_, 17);
v_zetaHave_5768_ = lean_ctor_get_uint8(v___x_5749_, 18);
v_isSharedCheck_6019_ = !lean_is_exclusive(v___x_5749_);
if (v_isSharedCheck_6019_ == 0)
{
v___x_5770_ = v___x_5749_;
v_isShared_5771_ = v_isSharedCheck_6019_;
goto v_resetjp_5769_;
}
else
{
lean_dec(v___x_5749_);
v___x_5770_ = lean_box(0);
v_isShared_5771_ = v_isSharedCheck_6019_;
goto v_resetjp_5769_;
}
v_resetjp_5769_:
{
uint8_t v_trackZetaDelta_5772_; lean_object* v_zetaDeltaSet_5773_; lean_object* v_lctx_5774_; lean_object* v_localInstances_5775_; lean_object* v_defEqCtx_x3f_5776_; lean_object* v_synthPendingDepth_5777_; lean_object* v_canUnfold_x3f_5778_; uint8_t v_univApprox_5779_; uint8_t v_inTypeClassResolution_5780_; uint8_t v_cacheInferType_5781_; lean_object* v_inheritedTraceOptions_5782_; uint8_t v_hasTrace_5783_; uint8_t v___x_5784_; lean_object* v_config_5786_; 
v_trackZetaDelta_5772_ = lean_ctor_get_uint8(v_a_5744_, sizeof(void*)*7);
v_zetaDeltaSet_5773_ = lean_ctor_get(v_a_5744_, 1);
v_lctx_5774_ = lean_ctor_get(v_a_5744_, 2);
v_localInstances_5775_ = lean_ctor_get(v_a_5744_, 3);
v_defEqCtx_x3f_5776_ = lean_ctor_get(v_a_5744_, 4);
v_synthPendingDepth_5777_ = lean_ctor_get(v_a_5744_, 5);
v_canUnfold_x3f_5778_ = lean_ctor_get(v_a_5744_, 6);
v_univApprox_5779_ = lean_ctor_get_uint8(v_a_5744_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5780_ = lean_ctor_get_uint8(v_a_5744_, sizeof(void*)*7 + 2);
v_cacheInferType_5781_ = lean_ctor_get_uint8(v_a_5744_, sizeof(void*)*7 + 3);
v_inheritedTraceOptions_5782_ = lean_ctor_get(v_a_5746_, 13);
v_hasTrace_5783_ = lean_ctor_get_uint8(v_options_5750_, sizeof(void*)*1);
v___x_5784_ = 3;
if (v_isShared_5771_ == 0)
{
v_config_5786_ = v___x_5770_;
goto v_reusejp_5785_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 0, v_foApprox_5751_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 1, v_ctxApprox_5752_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 2, v_quasiPatternApprox_5753_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 3, v_constApprox_5754_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 4, v_isDefEqStuckEx_5755_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 5, v_unificationHints_5756_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 6, v_proofIrrelevance_5757_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 7, v_assignSyntheticOpaque_5758_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 8, v_offsetCnstrs_5759_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 10, v_etaStruct_5760_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 11, v_univApprox_5761_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 12, v_iota_5762_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 13, v_beta_5763_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 14, v_proj_5764_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 15, v_zeta_5765_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 16, v_zetaDelta_5766_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 17, v_zetaUnused_5767_);
lean_ctor_set_uint8(v_reuseFailAlloc_6018_, 18, v_zetaHave_5768_);
v_config_5786_ = v_reuseFailAlloc_6018_;
goto v_reusejp_5785_;
}
v_reusejp_5785_:
{
uint64_t v___x_5787_; uint64_t v___x_5788_; uint64_t v___x_5789_; uint64_t v___x_5790_; uint64_t v___x_5791_; uint64_t v_key_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; 
lean_ctor_set_uint8(v_config_5786_, 9, v___x_5784_);
v___x_5787_ = l_Lean_Meta_Context_configKey(v_a_5744_);
v___x_5788_ = 2ULL;
v___x_5789_ = lean_uint64_shift_right(v___x_5787_, v___x_5788_);
v___x_5790_ = lean_uint64_shift_left(v___x_5789_, v___x_5788_);
v___x_5791_ = lean_uint64_once(&l_Lean_Meta_wrapInstance___closed__0, &l_Lean_Meta_wrapInstance___closed__0_once, _init_l_Lean_Meta_wrapInstance___closed__0);
v_key_5792_ = lean_uint64_lor(v___x_5790_, v___x_5791_);
v___x_5793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5793_, 0, v_config_5786_);
lean_ctor_set_uint64(v___x_5793_, sizeof(void*)*1, v_key_5792_);
lean_inc(v_canUnfold_x3f_5778_);
lean_inc(v_synthPendingDepth_5777_);
lean_inc(v_defEqCtx_x3f_5776_);
lean_inc_ref(v_localInstances_5775_);
lean_inc_ref(v_lctx_5774_);
lean_inc(v_zetaDeltaSet_5773_);
v___x_5794_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5794_, 0, v___x_5793_);
lean_ctor_set(v___x_5794_, 1, v_zetaDeltaSet_5773_);
lean_ctor_set(v___x_5794_, 2, v_lctx_5774_);
lean_ctor_set(v___x_5794_, 3, v_localInstances_5775_);
lean_ctor_set(v___x_5794_, 4, v_defEqCtx_x3f_5776_);
lean_ctor_set(v___x_5794_, 5, v_synthPendingDepth_5777_);
lean_ctor_set(v___x_5794_, 6, v_canUnfold_x3f_5778_);
lean_ctor_set_uint8(v___x_5794_, sizeof(void*)*7, v_trackZetaDelta_5772_);
lean_ctor_set_uint8(v___x_5794_, sizeof(void*)*7 + 1, v_univApprox_5779_);
lean_ctor_set_uint8(v___x_5794_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5780_);
lean_ctor_set_uint8(v___x_5794_, sizeof(void*)*7 + 3, v_cacheInferType_5781_);
if (v_hasTrace_5783_ == 0)
{
lean_object* v___x_5795_; 
lean_inc_ref(v_expectedType_5740_);
v___x_5795_ = l_Lean_Meta_isClass_x3f(v_expectedType_5740_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5834_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5834_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5834_ == 0)
{
v___x_5798_ = v___x_5795_;
v_isShared_5799_ = v_isSharedCheck_5834_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5795_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5834_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
if (lean_obj_tag(v_a_5796_) == 1)
{
lean_object* v_val_5800_; lean_object* v___x_5801_; 
lean_del_object(v___x_5798_);
v_val_5800_ = lean_ctor_get(v_a_5796_, 0);
lean_inc(v_val_5800_);
lean_dec_ref(v_a_5796_);
lean_inc_ref(v_expectedType_5740_);
v___x_5801_ = l_Lean_Meta_isProp(v_expectedType_5740_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_object* v_a_5802_; lean_object* v___x_5804_; uint8_t v_isShared_5805_; uint8_t v_isSharedCheck_5822_; 
v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5822_ == 0)
{
v___x_5804_ = v___x_5801_;
v_isShared_5805_ = v_isSharedCheck_5822_;
goto v_resetjp_5803_;
}
else
{
lean_inc(v_a_5802_);
lean_dec(v___x_5801_);
v___x_5804_ = lean_box(0);
v_isShared_5805_ = v_isSharedCheck_5822_;
goto v_resetjp_5803_;
}
v_resetjp_5803_:
{
uint8_t v___x_5806_; 
v___x_5806_ = lean_unbox(v_a_5802_);
lean_dec(v_a_5802_);
if (v___x_5806_ == 0)
{
lean_object* v___x_5807_; 
lean_del_object(v___x_5804_);
lean_inc(v_a_5747_);
lean_inc_ref(v_a_5746_);
lean_inc(v_a_5745_);
lean_inc_ref(v___x_5794_);
lean_inc_ref(v_inst_5739_);
v___x_5807_ = lean_whnf(v_inst_5739_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5807_) == 0)
{
lean_object* v_a_5808_; lean_object* v_dummy_5809_; lean_object* v_nargs_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; 
v_a_5808_ = lean_ctor_get(v___x_5807_, 0);
lean_inc(v_a_5808_);
lean_dec_ref(v___x_5807_);
v_dummy_5809_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5810_ = l_Lean_Expr_getAppNumArgs(v_a_5808_);
lean_inc(v_nargs_5810_);
v___x_5811_ = lean_mk_array(v_nargs_5810_, v_dummy_5809_);
v___x_5812_ = lean_unsigned_to_nat(1u);
v___x_5813_ = lean_nat_sub(v_nargs_5810_, v___x_5812_);
lean_dec(v_nargs_5810_);
v___x_5814_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8(v_inst_5739_, v_expectedType_5740_, v_hasTrace_5783_, v_compile_5741_, v_logCompileErrors_5742_, v_isMeta_5743_, v_val_5800_, v_a_5808_, v___x_5811_, v___x_5813_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec_ref(v___x_5794_);
lean_dec(v___x_5813_);
return v___x_5814_;
}
else
{
lean_dec(v_val_5800_);
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
return v___x_5807_;
}
}
else
{
lean_object* v___x_5815_; uint8_t v___x_5816_; 
lean_dec(v_val_5800_);
v___x_5815_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5816_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5750_, v___x_5815_);
if (v___x_5816_ == 0)
{
lean_object* v___x_5818_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
if (v_isShared_5805_ == 0)
{
lean_ctor_set(v___x_5804_, 0, v_inst_5739_);
v___x_5818_ = v___x_5804_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_inst_5739_);
v___x_5818_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
return v___x_5818_;
}
}
else
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
lean_del_object(v___x_5804_);
v___x_5820_ = lean_box(0);
v___x_5821_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5740_, v_inst_5739_, v___x_5816_, v___x_5820_, v___x_5816_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec_ref(v___x_5794_);
return v___x_5821_;
}
}
}
}
else
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5830_; 
lean_dec(v_val_5800_);
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5823_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5825_ = v___x_5801_;
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5801_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v___x_5828_; 
if (v_isShared_5826_ == 0)
{
v___x_5828_ = v___x_5825_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_a_5823_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
return v___x_5828_;
}
}
}
}
else
{
lean_object* v___x_5832_; 
lean_dec(v_a_5796_);
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v_inst_5739_);
v___x_5832_ = v___x_5798_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v_inst_5739_);
v___x_5832_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
return v___x_5832_;
}
}
}
}
else
{
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5842_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5835_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5837_ = v___x_5795_;
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5795_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5840_; 
if (v_isShared_5838_ == 0)
{
v___x_5840_ = v___x_5837_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_a_5835_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
}
else
{
lean_object* v___f_5843_; lean_object* v_cls_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; uint8_t v___x_5847_; lean_object* v___y_5849_; lean_object* v___y_5850_; lean_object* v_a_5851_; lean_object* v___y_5861_; lean_object* v___y_5862_; lean_object* v_a_5863_; lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v_a_5868_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v_a_5879_; lean_object* v___y_5892_; lean_object* v___y_5893_; lean_object* v_a_5894_; lean_object* v___y_5897_; lean_object* v___y_5898_; lean_object* v_a_5899_; lean_object* v___y_5902_; lean_object* v___y_5903_; lean_object* v___y_5904_; 
lean_inc_ref(v_expectedType_5740_);
v___f_5843_ = lean_alloc_closure((void*)(l_Lean_Meta_wrapInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5843_, 0, v_expectedType_5740_);
v_cls_5844_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5845_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_5846_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2);
v___x_5847_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5782_, v_options_5750_, v___x_5846_);
if (v___x_5847_ == 0)
{
lean_object* v___x_5950_; uint8_t v___x_5951_; 
v___x_5950_ = l_Lean_trace_profiler;
v___x_5951_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5750_, v___x_5950_);
if (v___x_5951_ == 0)
{
lean_object* v___x_5952_; 
lean_dec_ref(v___f_5843_);
lean_inc_ref(v_expectedType_5740_);
v___x_5952_ = l_Lean_Meta_isClass_x3f(v_expectedType_5740_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5952_) == 0)
{
lean_object* v_a_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_6009_; 
v_a_5953_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_6009_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_6009_ == 0)
{
v___x_5955_ = v___x_5952_;
v_isShared_5956_ = v_isSharedCheck_6009_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_a_5953_);
lean_dec(v___x_5952_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_6009_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
if (lean_obj_tag(v_a_5953_) == 1)
{
lean_object* v_val_5957_; lean_object* v___y_5959_; lean_object* v___y_5960_; lean_object* v___y_5961_; lean_object* v___y_5962_; 
lean_del_object(v___x_5955_);
v_val_5957_ = lean_ctor_get(v_a_5953_, 0);
lean_inc(v_val_5957_);
lean_dec_ref(v_a_5953_);
if (v___x_5847_ == 0)
{
v___y_5959_ = v___x_5794_;
v___y_5960_ = v_a_5745_;
v___y_5961_ = v_a_5746_;
v___y_5962_ = v_a_5747_;
goto v___jp_5958_;
}
else
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5994_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
lean_inc(v_val_5957_);
v___x_5995_ = l_Lean_MessageData_ofName(v_val_5957_);
v___x_5996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5994_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5844_, v___x_5996_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5997_) == 0)
{
lean_dec_ref(v___x_5997_);
v___y_5959_ = v___x_5794_;
v___y_5960_ = v_a_5745_;
v___y_5961_ = v_a_5746_;
v___y_5962_ = v_a_5747_;
goto v___jp_5958_;
}
else
{
lean_object* v_a_5998_; lean_object* v___x_6000_; uint8_t v_isShared_6001_; uint8_t v_isSharedCheck_6005_; 
lean_dec(v_val_5957_);
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5998_ = lean_ctor_get(v___x_5997_, 0);
v_isSharedCheck_6005_ = !lean_is_exclusive(v___x_5997_);
if (v_isSharedCheck_6005_ == 0)
{
v___x_6000_ = v___x_5997_;
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
else
{
lean_inc(v_a_5998_);
lean_dec(v___x_5997_);
v___x_6000_ = lean_box(0);
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
v_resetjp_5999_:
{
lean_object* v___x_6003_; 
if (v_isShared_6001_ == 0)
{
v___x_6003_ = v___x_6000_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_a_5998_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
return v___x_6003_;
}
}
}
}
v___jp_5958_:
{
lean_object* v___x_5963_; 
lean_inc_ref(v_expectedType_5740_);
v___x_5963_ = l_Lean_Meta_isProp(v_expectedType_5740_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_);
if (lean_obj_tag(v___x_5963_) == 0)
{
lean_object* v_a_5964_; lean_object* v___x_5966_; uint8_t v_isShared_5967_; uint8_t v_isSharedCheck_5985_; 
v_a_5964_ = lean_ctor_get(v___x_5963_, 0);
v_isSharedCheck_5985_ = !lean_is_exclusive(v___x_5963_);
if (v_isSharedCheck_5985_ == 0)
{
v___x_5966_ = v___x_5963_;
v_isShared_5967_ = v_isSharedCheck_5985_;
goto v_resetjp_5965_;
}
else
{
lean_inc(v_a_5964_);
lean_dec(v___x_5963_);
v___x_5966_ = lean_box(0);
v_isShared_5967_ = v_isSharedCheck_5985_;
goto v_resetjp_5965_;
}
v_resetjp_5965_:
{
uint8_t v___x_5968_; 
v___x_5968_ = lean_unbox(v_a_5964_);
lean_dec(v_a_5964_);
if (v___x_5968_ == 0)
{
lean_object* v___x_5969_; 
lean_del_object(v___x_5966_);
lean_inc(v___y_5962_);
lean_inc_ref(v___y_5961_);
lean_inc(v___y_5960_);
lean_inc_ref(v___y_5959_);
lean_inc_ref(v_inst_5739_);
v___x_5969_ = lean_whnf(v_inst_5739_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_);
if (lean_obj_tag(v___x_5969_) == 0)
{
lean_object* v_a_5970_; lean_object* v_dummy_5971_; lean_object* v_nargs_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; 
v_a_5970_ = lean_ctor_get(v___x_5969_, 0);
lean_inc(v_a_5970_);
lean_dec_ref(v___x_5969_);
v_dummy_5971_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5972_ = l_Lean_Expr_getAppNumArgs(v_a_5970_);
lean_inc(v_nargs_5972_);
v___x_5973_ = lean_mk_array(v_nargs_5972_, v_dummy_5971_);
v___x_5974_ = lean_unsigned_to_nat(1u);
v___x_5975_ = lean_nat_sub(v_nargs_5972_, v___x_5974_);
lean_dec(v_nargs_5972_);
v___x_5976_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_inst_5739_, v_expectedType_5740_, v___x_5951_, v_hasTrace_5783_, v_compile_5741_, v_logCompileErrors_5742_, v_isMeta_5743_, v_val_5957_, v_a_5970_, v___x_5973_, v___x_5975_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_);
lean_dec_ref(v___y_5959_);
lean_dec(v___x_5975_);
return v___x_5976_;
}
else
{
lean_dec_ref(v___y_5959_);
lean_dec(v_val_5957_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
return v___x_5969_;
}
}
else
{
lean_object* v_options_5977_; lean_object* v___x_5978_; uint8_t v___x_5979_; 
lean_dec(v_val_5957_);
v_options_5977_ = lean_ctor_get(v___y_5961_, 2);
v___x_5978_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5979_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5977_, v___x_5978_);
if (v___x_5979_ == 0)
{
lean_object* v___x_5981_; 
lean_dec_ref(v___y_5959_);
lean_dec_ref(v_expectedType_5740_);
if (v_isShared_5967_ == 0)
{
lean_ctor_set(v___x_5966_, 0, v_inst_5739_);
v___x_5981_ = v___x_5966_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_inst_5739_);
v___x_5981_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
return v___x_5981_;
}
}
else
{
lean_object* v___x_5983_; lean_object* v___x_5984_; 
lean_del_object(v___x_5966_);
v___x_5983_ = lean_box(0);
v___x_5984_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5740_, v_inst_5739_, v_hasTrace_5783_, v___x_5983_, v_hasTrace_5783_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_);
lean_dec_ref(v___y_5959_);
return v___x_5984_;
}
}
}
}
else
{
lean_object* v_a_5986_; lean_object* v___x_5988_; uint8_t v_isShared_5989_; uint8_t v_isSharedCheck_5993_; 
lean_dec_ref(v___y_5959_);
lean_dec(v_val_5957_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5986_ = lean_ctor_get(v___x_5963_, 0);
v_isSharedCheck_5993_ = !lean_is_exclusive(v___x_5963_);
if (v_isSharedCheck_5993_ == 0)
{
v___x_5988_ = v___x_5963_;
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
else
{
lean_inc(v_a_5986_);
lean_dec(v___x_5963_);
v___x_5988_ = lean_box(0);
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
v_resetjp_5987_:
{
lean_object* v___x_5991_; 
if (v_isShared_5989_ == 0)
{
v___x_5991_ = v___x_5988_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5986_);
v___x_5991_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
return v___x_5991_;
}
}
}
}
}
else
{
lean_object* v___x_6007_; 
lean_dec(v_a_5953_);
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 0, v_inst_5739_);
v___x_6007_ = v___x_5955_;
goto v_reusejp_6006_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_inst_5739_);
v___x_6007_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6006_;
}
v_reusejp_6006_:
{
return v___x_6007_;
}
}
}
}
else
{
lean_object* v_a_6010_; lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6017_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_6010_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_6017_ == 0)
{
v___x_6012_ = v___x_5952_;
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
else
{
lean_inc(v_a_6010_);
lean_dec(v___x_5952_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6015_; 
if (v_isShared_6013_ == 0)
{
v___x_6015_ = v___x_6012_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
v___x_6015_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
return v___x_6015_;
}
}
}
}
else
{
goto v___jp_5907_;
}
}
else
{
goto v___jp_5907_;
}
v___jp_5848_:
{
lean_object* v___x_5852_; double v___x_5853_; double v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5852_ = lean_io_get_num_heartbeats();
v___x_5853_ = lean_float_of_nat(v___y_5849_);
v___x_5854_ = lean_float_of_nat(v___x_5852_);
v___x_5855_ = lean_box_float(v___x_5853_);
v___x_5856_ = lean_box_float(v___x_5854_);
v___x_5857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5857_, 0, v___x_5855_);
lean_ctor_set(v___x_5857_, 1, v___x_5856_);
v___x_5858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5858_, 0, v_a_5851_);
lean_ctor_set(v___x_5858_, 1, v___x_5857_);
v___x_5859_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10(v_cls_5844_, v_hasTrace_5783_, v___x_5845_, v_options_5750_, v___x_5847_, v___y_5850_, v___f_5843_, v___x_5858_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec_ref(v___x_5794_);
return v___x_5859_;
}
v___jp_5860_:
{
lean_object* v___x_5864_; 
v___x_5864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5864_, 0, v_a_5863_);
v___y_5849_ = v___y_5861_;
v___y_5850_ = v___y_5862_;
v_a_5851_ = v___x_5864_;
goto v___jp_5848_;
}
v___jp_5865_:
{
lean_object* v___x_5869_; 
v___x_5869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5869_, 0, v_a_5868_);
v___y_5849_ = v___y_5866_;
v___y_5850_ = v___y_5867_;
v_a_5851_ = v___x_5869_;
goto v___jp_5848_;
}
v___jp_5870_:
{
if (lean_obj_tag(v___y_5873_) == 0)
{
lean_object* v_a_5874_; 
v_a_5874_ = lean_ctor_get(v___y_5873_, 0);
lean_inc(v_a_5874_);
lean_dec_ref(v___y_5873_);
v___y_5861_ = v___y_5871_;
v___y_5862_ = v___y_5872_;
v_a_5863_ = v_a_5874_;
goto v___jp_5860_;
}
else
{
lean_object* v_a_5875_; 
v_a_5875_ = lean_ctor_get(v___y_5873_, 0);
lean_inc(v_a_5875_);
lean_dec_ref(v___y_5873_);
v___y_5866_ = v___y_5871_;
v___y_5867_ = v___y_5872_;
v_a_5868_ = v_a_5875_;
goto v___jp_5865_;
}
}
v___jp_5876_:
{
lean_object* v___x_5880_; double v___x_5881_; double v___x_5882_; double v___x_5883_; double v___x_5884_; double v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5880_ = lean_io_mono_nanos_now();
v___x_5881_ = lean_float_of_nat(v___y_5877_);
v___x_5882_ = lean_float_once(&l_Lean_Meta_wrapInstance___closed__1, &l_Lean_Meta_wrapInstance___closed__1_once, _init_l_Lean_Meta_wrapInstance___closed__1);
v___x_5883_ = lean_float_div(v___x_5881_, v___x_5882_);
v___x_5884_ = lean_float_of_nat(v___x_5880_);
v___x_5885_ = lean_float_div(v___x_5884_, v___x_5882_);
v___x_5886_ = lean_box_float(v___x_5883_);
v___x_5887_ = lean_box_float(v___x_5885_);
v___x_5888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5886_);
lean_ctor_set(v___x_5888_, 1, v___x_5887_);
v___x_5889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5889_, 0, v_a_5879_);
lean_ctor_set(v___x_5889_, 1, v___x_5888_);
v___x_5890_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10(v_cls_5844_, v_hasTrace_5783_, v___x_5845_, v_options_5750_, v___x_5847_, v___y_5878_, v___f_5843_, v___x_5889_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec_ref(v___x_5794_);
return v___x_5890_;
}
v___jp_5891_:
{
lean_object* v___x_5895_; 
v___x_5895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5895_, 0, v_a_5894_);
v___y_5877_ = v___y_5892_;
v___y_5878_ = v___y_5893_;
v_a_5879_ = v___x_5895_;
goto v___jp_5876_;
}
v___jp_5896_:
{
lean_object* v___x_5900_; 
v___x_5900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5900_, 0, v_a_5899_);
v___y_5877_ = v___y_5897_;
v___y_5878_ = v___y_5898_;
v_a_5879_ = v___x_5900_;
goto v___jp_5876_;
}
v___jp_5901_:
{
if (lean_obj_tag(v___y_5904_) == 0)
{
lean_object* v_a_5905_; 
v_a_5905_ = lean_ctor_get(v___y_5904_, 0);
lean_inc(v_a_5905_);
lean_dec_ref(v___y_5904_);
v___y_5897_ = v___y_5902_;
v___y_5898_ = v___y_5903_;
v_a_5899_ = v_a_5905_;
goto v___jp_5896_;
}
else
{
lean_object* v_a_5906_; 
v_a_5906_ = lean_ctor_get(v___y_5904_, 0);
lean_inc(v_a_5906_);
lean_dec_ref(v___y_5904_);
v___y_5892_ = v___y_5902_;
v___y_5893_ = v___y_5903_;
v_a_5894_ = v_a_5906_;
goto v___jp_5891_;
}
}
v___jp_5907_:
{
lean_object* v___x_5908_; 
v___x_5908_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__9___redArg(v_a_5747_);
if (lean_obj_tag(v___x_5908_) == 0)
{
lean_object* v_a_5909_; lean_object* v___x_5910_; uint8_t v___x_5911_; 
v_a_5909_ = lean_ctor_get(v___x_5908_, 0);
lean_inc(v_a_5909_);
lean_dec_ref(v___x_5908_);
v___x_5910_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5911_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5750_, v___x_5910_);
if (v___x_5911_ == 0)
{
lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5912_ = lean_io_mono_nanos_now();
lean_inc_ref(v_expectedType_5740_);
v___x_5913_ = l_Lean_Meta_isClass_x3f(v_expectedType_5740_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5913_) == 0)
{
lean_object* v_a_5914_; 
v_a_5914_ = lean_ctor_get(v___x_5913_, 0);
lean_inc(v_a_5914_);
lean_dec_ref(v___x_5913_);
if (lean_obj_tag(v_a_5914_) == 1)
{
if (v___x_5847_ == 0)
{
lean_object* v_val_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v_val_5915_ = lean_ctor_get(v_a_5914_, 0);
lean_inc(v_val_5915_);
lean_dec_ref(v_a_5914_);
v___x_5916_ = lean_box(0);
v___x_5917_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5740_, v_inst_5739_, v___x_5911_, v_hasTrace_5783_, v_compile_5741_, v_logCompileErrors_5742_, v_isMeta_5743_, v_val_5915_, v___x_5916_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
v___y_5902_ = v___x_5912_;
v___y_5903_ = v_a_5909_;
v___y_5904_ = v___x_5917_;
goto v___jp_5901_;
}
else
{
lean_object* v_val_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; 
v_val_5918_ = lean_ctor_get(v_a_5914_, 0);
lean_inc_n(v_val_5918_, 2);
lean_dec_ref(v_a_5914_);
v___x_5919_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5920_ = l_Lean_MessageData_ofName(v_val_5918_);
v___x_5921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5919_);
lean_ctor_set(v___x_5921_, 1, v___x_5920_);
v___x_5922_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5844_, v___x_5921_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5922_) == 0)
{
lean_object* v_a_5923_; lean_object* v___x_5924_; 
v_a_5923_ = lean_ctor_get(v___x_5922_, 0);
lean_inc(v_a_5923_);
lean_dec_ref(v___x_5922_);
v___x_5924_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5740_, v_inst_5739_, v___x_5911_, v_hasTrace_5783_, v_compile_5741_, v_logCompileErrors_5742_, v_isMeta_5743_, v_val_5918_, v_a_5923_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
v___y_5902_ = v___x_5912_;
v___y_5903_ = v_a_5909_;
v___y_5904_ = v___x_5924_;
goto v___jp_5901_;
}
else
{
lean_object* v_a_5925_; 
lean_dec(v_val_5918_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5925_ = lean_ctor_get(v___x_5922_, 0);
lean_inc(v_a_5925_);
lean_dec_ref(v___x_5922_);
v___y_5892_ = v___x_5912_;
v___y_5893_ = v_a_5909_;
v_a_5894_ = v_a_5925_;
goto v___jp_5891_;
}
}
}
else
{
lean_dec(v_a_5914_);
lean_dec_ref(v_expectedType_5740_);
v___y_5897_ = v___x_5912_;
v___y_5898_ = v_a_5909_;
v_a_5899_ = v_inst_5739_;
goto v___jp_5896_;
}
}
else
{
lean_object* v_a_5926_; 
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5926_ = lean_ctor_get(v___x_5913_, 0);
lean_inc(v_a_5926_);
lean_dec_ref(v___x_5913_);
v___y_5892_ = v___x_5912_;
v___y_5893_ = v_a_5909_;
v_a_5894_ = v_a_5926_;
goto v___jp_5891_;
}
}
else
{
lean_object* v___x_5927_; lean_object* v___x_5928_; 
v___x_5927_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_expectedType_5740_);
v___x_5928_ = l_Lean_Meta_isClass_x3f(v_expectedType_5740_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5928_) == 0)
{
lean_object* v_a_5929_; 
v_a_5929_ = lean_ctor_get(v___x_5928_, 0);
lean_inc(v_a_5929_);
lean_dec_ref(v___x_5928_);
if (lean_obj_tag(v_a_5929_) == 1)
{
if (v___x_5847_ == 0)
{
lean_object* v_val_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; 
v_val_5930_ = lean_ctor_get(v_a_5929_, 0);
lean_inc(v_val_5930_);
lean_dec_ref(v_a_5929_);
v___x_5931_ = lean_box(0);
v___x_5932_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5740_, v_inst_5739_, v___x_5911_, v_compile_5741_, v_logCompileErrors_5742_, v_isMeta_5743_, v_val_5930_, v___x_5931_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
v___y_5871_ = v___x_5927_;
v___y_5872_ = v_a_5909_;
v___y_5873_ = v___x_5932_;
goto v___jp_5870_;
}
else
{
lean_object* v_val_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; 
v_val_5933_ = lean_ctor_get(v_a_5929_, 0);
lean_inc_n(v_val_5933_, 2);
lean_dec_ref(v_a_5929_);
v___x_5934_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5935_ = l_Lean_MessageData_ofName(v_val_5933_);
v___x_5936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5844_, v___x_5936_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
if (lean_obj_tag(v___x_5937_) == 0)
{
lean_object* v_a_5938_; lean_object* v___x_5939_; 
v_a_5938_ = lean_ctor_get(v___x_5937_, 0);
lean_inc(v_a_5938_);
lean_dec_ref(v___x_5937_);
v___x_5939_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5740_, v_inst_5739_, v___x_5911_, v_compile_5741_, v_logCompileErrors_5742_, v_isMeta_5743_, v_val_5933_, v_a_5938_, v___x_5794_, v_a_5745_, v_a_5746_, v_a_5747_);
v___y_5871_ = v___x_5927_;
v___y_5872_ = v_a_5909_;
v___y_5873_ = v___x_5939_;
goto v___jp_5870_;
}
else
{
lean_object* v_a_5940_; 
lean_dec(v_val_5933_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5940_ = lean_ctor_get(v___x_5937_, 0);
lean_inc(v_a_5940_);
lean_dec_ref(v___x_5937_);
v___y_5866_ = v___x_5927_;
v___y_5867_ = v_a_5909_;
v_a_5868_ = v_a_5940_;
goto v___jp_5865_;
}
}
}
else
{
lean_dec(v_a_5929_);
lean_dec_ref(v_expectedType_5740_);
v___y_5861_ = v___x_5927_;
v___y_5862_ = v_a_5909_;
v_a_5863_ = v_inst_5739_;
goto v___jp_5860_;
}
}
else
{
lean_object* v_a_5941_; 
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5941_ = lean_ctor_get(v___x_5928_, 0);
lean_inc(v_a_5941_);
lean_dec_ref(v___x_5928_);
v___y_5866_ = v___x_5927_;
v___y_5867_ = v_a_5909_;
v_a_5868_ = v_a_5941_;
goto v___jp_5865_;
}
}
}
else
{
lean_object* v_a_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5949_; 
lean_dec_ref(v___f_5843_);
lean_dec_ref(v___x_5794_);
lean_dec_ref(v_expectedType_5740_);
lean_dec_ref(v_inst_5739_);
v_a_5942_ = lean_ctor_get(v___x_5908_, 0);
v_isSharedCheck_5949_ = !lean_is_exclusive(v___x_5908_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5944_ = v___x_5908_;
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_a_5942_);
lean_dec(v___x_5908_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
v_resetjp_5943_:
{
lean_object* v___x_5947_; 
if (v_isShared_5945_ == 0)
{
v___x_5947_ = v___x_5944_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_a_5942_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(lean_object* v___x_6020_, lean_object* v_a_6021_, uint8_t v_compile_6022_, uint8_t v_logCompileErrors_6023_, uint8_t v_isMeta_6024_, lean_object* v___x_6025_, lean_object* v___x_6026_, lean_object* v_____r_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_){
_start:
{
lean_object* v___x_6033_; 
v___x_6033_ = l_Lean_Meta_wrapInstance(v___x_6020_, v_a_6021_, v_compile_6022_, v_logCompileErrors_6023_, v_isMeta_6024_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_);
if (lean_obj_tag(v___x_6033_) == 0)
{
lean_object* v_a_6034_; lean_object* v___x_6035_; 
v_a_6034_ = lean_ctor_get(v___x_6033_, 0);
lean_inc(v_a_6034_);
lean_dec_ref(v___x_6033_);
v___x_6035_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_6025_, v_a_6034_, v___y_6029_);
if (lean_obj_tag(v___x_6035_) == 0)
{
lean_object* v___x_6037_; uint8_t v_isShared_6038_; uint8_t v_isSharedCheck_6043_; 
v_isSharedCheck_6043_ = !lean_is_exclusive(v___x_6035_);
if (v_isSharedCheck_6043_ == 0)
{
lean_object* v_unused_6044_; 
v_unused_6044_ = lean_ctor_get(v___x_6035_, 0);
lean_dec(v_unused_6044_);
v___x_6037_ = v___x_6035_;
v_isShared_6038_ = v_isSharedCheck_6043_;
goto v_resetjp_6036_;
}
else
{
lean_dec(v___x_6035_);
v___x_6037_ = lean_box(0);
v_isShared_6038_ = v_isSharedCheck_6043_;
goto v_resetjp_6036_;
}
v_resetjp_6036_:
{
lean_object* v___x_6039_; lean_object* v___x_6041_; 
v___x_6039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6026_);
if (v_isShared_6038_ == 0)
{
lean_ctor_set(v___x_6037_, 0, v___x_6039_);
v___x_6041_ = v___x_6037_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v___x_6039_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
}
else
{
lean_object* v_a_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6052_; 
v_a_6045_ = lean_ctor_get(v___x_6035_, 0);
v_isSharedCheck_6052_ = !lean_is_exclusive(v___x_6035_);
if (v_isSharedCheck_6052_ == 0)
{
v___x_6047_ = v___x_6035_;
v_isShared_6048_ = v_isSharedCheck_6052_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_a_6045_);
lean_dec(v___x_6035_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6052_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6050_; 
if (v_isShared_6048_ == 0)
{
v___x_6050_ = v___x_6047_;
goto v_reusejp_6049_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
v___x_6050_ = v_reuseFailAlloc_6051_;
goto v_reusejp_6049_;
}
v_reusejp_6049_:
{
return v___x_6050_;
}
}
}
}
else
{
lean_object* v_a_6053_; lean_object* v___x_6055_; uint8_t v_isShared_6056_; uint8_t v_isSharedCheck_6060_; 
lean_dec(v___x_6025_);
v_a_6053_ = lean_ctor_get(v___x_6033_, 0);
v_isSharedCheck_6060_ = !lean_is_exclusive(v___x_6033_);
if (v_isSharedCheck_6060_ == 0)
{
v___x_6055_ = v___x_6033_;
v_isShared_6056_ = v_isSharedCheck_6060_;
goto v_resetjp_6054_;
}
else
{
lean_inc(v_a_6053_);
lean_dec(v___x_6033_);
v___x_6055_ = lean_box(0);
v_isShared_6056_ = v_isSharedCheck_6060_;
goto v_resetjp_6054_;
}
v_resetjp_6054_:
{
lean_object* v___x_6058_; 
if (v_isShared_6056_ == 0)
{
v___x_6058_ = v___x_6055_;
goto v_reusejp_6057_;
}
else
{
lean_object* v_reuseFailAlloc_6059_; 
v_reuseFailAlloc_6059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_a_6053_);
v___x_6058_ = v_reuseFailAlloc_6059_;
goto v_reusejp_6057_;
}
v_reusejp_6057_:
{
return v___x_6058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4___boxed(lean_object* v___x_6061_, lean_object* v_a_6062_, lean_object* v_compile_6063_, lean_object* v_logCompileErrors_6064_, lean_object* v_isMeta_6065_, lean_object* v___x_6066_, lean_object* v___x_6067_, lean_object* v_____r_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_){
_start:
{
uint8_t v_compile_boxed_6074_; uint8_t v_logCompileErrors_boxed_6075_; uint8_t v_isMeta_boxed_6076_; lean_object* v_res_6077_; 
v_compile_boxed_6074_ = lean_unbox(v_compile_6063_);
v_logCompileErrors_boxed_6075_ = lean_unbox(v_logCompileErrors_6064_);
v_isMeta_boxed_6076_ = lean_unbox(v_isMeta_6065_);
v_res_6077_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__4(v___x_6061_, v_a_6062_, v_compile_boxed_6074_, v_logCompileErrors_boxed_6075_, v_isMeta_boxed_6076_, v___x_6066_, v___x_6067_, v_____r_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
lean_dec(v___y_6072_);
lean_dec_ref(v___y_6071_);
lean_dec(v___y_6070_);
lean_dec_ref(v___y_6069_);
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object* v_expectedType_6078_, lean_object* v_inst_6079_, lean_object* v___x_6080_, lean_object* v_hasTrace_6081_, lean_object* v_compile_6082_, lean_object* v_logCompileErrors_6083_, lean_object* v_isMeta_6084_, lean_object* v_val_6085_, lean_object* v_____r_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_){
_start:
{
uint8_t v___x_159495__boxed_6092_; uint8_t v_hasTrace_boxed_6093_; uint8_t v_compile_boxed_6094_; uint8_t v_logCompileErrors_boxed_6095_; uint8_t v_isMeta_boxed_6096_; lean_object* v_res_6097_; 
v___x_159495__boxed_6092_ = lean_unbox(v___x_6080_);
v_hasTrace_boxed_6093_ = lean_unbox(v_hasTrace_6081_);
v_compile_boxed_6094_ = lean_unbox(v_compile_6082_);
v_logCompileErrors_boxed_6095_ = lean_unbox(v_logCompileErrors_6083_);
v_isMeta_boxed_6096_ = lean_unbox(v_isMeta_6084_);
v_res_6097_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_6078_, v_inst_6079_, v___x_159495__boxed_6092_, v_hasTrace_boxed_6093_, v_compile_boxed_6094_, v_logCompileErrors_boxed_6095_, v_isMeta_boxed_6096_, v_val_6085_, v_____r_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
return v_res_6097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object* v_expectedType_6098_, lean_object* v_inst_6099_, lean_object* v___x_6100_, lean_object* v_compile_6101_, lean_object* v_logCompileErrors_6102_, lean_object* v_isMeta_6103_, lean_object* v_val_6104_, lean_object* v_____r_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_){
_start:
{
uint8_t v___x_159520__boxed_6111_; uint8_t v_compile_boxed_6112_; uint8_t v_logCompileErrors_boxed_6113_; uint8_t v_isMeta_boxed_6114_; lean_object* v_res_6115_; 
v___x_159520__boxed_6111_ = lean_unbox(v___x_6100_);
v_compile_boxed_6112_ = lean_unbox(v_compile_6101_);
v_logCompileErrors_boxed_6113_ = lean_unbox(v_logCompileErrors_6102_);
v_isMeta_boxed_6114_ = lean_unbox(v_isMeta_6103_);
v_res_6115_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_6098_, v_inst_6099_, v___x_159520__boxed_6111_, v_compile_boxed_6112_, v_logCompileErrors_boxed_6113_, v_isMeta_boxed_6114_, v_val_6104_, v_____r_6105_, v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_);
lean_dec(v___y_6109_);
lean_dec_ref(v___y_6108_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
return v_res_6115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19___boxed(lean_object* v_inst_6116_, lean_object* v_expectedType_6117_, lean_object* v___x_6118_, lean_object* v___x_6119_, lean_object* v_compile_6120_, lean_object* v_logCompileErrors_6121_, lean_object* v_isMeta_6122_, lean_object* v_val_6123_, lean_object* v_x_6124_, lean_object* v_x_6125_, lean_object* v_x_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_){
_start:
{
uint8_t v___x_159557__boxed_6132_; uint8_t v___x_159558__boxed_6133_; uint8_t v_compile_boxed_6134_; uint8_t v_logCompileErrors_boxed_6135_; uint8_t v_isMeta_boxed_6136_; lean_object* v_res_6137_; 
v___x_159557__boxed_6132_ = lean_unbox(v___x_6118_);
v___x_159558__boxed_6133_ = lean_unbox(v___x_6119_);
v_compile_boxed_6134_ = lean_unbox(v_compile_6120_);
v_logCompileErrors_boxed_6135_ = lean_unbox(v_logCompileErrors_6121_);
v_isMeta_boxed_6136_ = lean_unbox(v_isMeta_6122_);
v_res_6137_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__19(v_inst_6116_, v_expectedType_6117_, v___x_159557__boxed_6132_, v___x_159558__boxed_6133_, v_compile_boxed_6134_, v_logCompileErrors_boxed_6135_, v_isMeta_boxed_6136_, v_val_6123_, v_x_6124_, v_x_6125_, v_x_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
lean_dec(v___y_6128_);
lean_dec_ref(v___y_6127_);
return v_res_6137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___boxed(lean_object* v_inst_6138_, lean_object* v_expectedType_6139_, lean_object* v___x_6140_, lean_object* v_compile_6141_, lean_object* v_logCompileErrors_6142_, lean_object* v_isMeta_6143_, lean_object* v_val_6144_, lean_object* v_x_6145_, lean_object* v_x_6146_, lean_object* v_x_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_){
_start:
{
uint8_t v___x_159713__boxed_6153_; uint8_t v_compile_boxed_6154_; uint8_t v_logCompileErrors_boxed_6155_; uint8_t v_isMeta_boxed_6156_; lean_object* v_res_6157_; 
v___x_159713__boxed_6153_ = lean_unbox(v___x_6140_);
v_compile_boxed_6154_ = lean_unbox(v_compile_6141_);
v_logCompileErrors_boxed_6155_ = lean_unbox(v_logCompileErrors_6142_);
v_isMeta_boxed_6156_ = lean_unbox(v_isMeta_6143_);
v_res_6157_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(v_inst_6138_, v_expectedType_6139_, v___x_159713__boxed_6153_, v_compile_boxed_6154_, v_logCompileErrors_boxed_6155_, v_isMeta_boxed_6156_, v_val_6144_, v_x_6145_, v_x_6146_, v_x_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
lean_dec(v___y_6151_);
lean_dec_ref(v___y_6150_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
return v_res_6157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object* v_inst_6158_, lean_object* v_expectedType_6159_, lean_object* v___x_6160_, lean_object* v___x_6161_, lean_object* v_compile_6162_, lean_object* v_logCompileErrors_6163_, lean_object* v_isMeta_6164_, lean_object* v_val_6165_, lean_object* v_x_6166_, lean_object* v_x_6167_, lean_object* v_x_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_){
_start:
{
uint8_t v___x_159881__boxed_6174_; uint8_t v___x_159882__boxed_6175_; uint8_t v_compile_boxed_6176_; uint8_t v_logCompileErrors_boxed_6177_; uint8_t v_isMeta_boxed_6178_; lean_object* v_res_6179_; 
v___x_159881__boxed_6174_ = lean_unbox(v___x_6160_);
v___x_159882__boxed_6175_ = lean_unbox(v___x_6161_);
v_compile_boxed_6176_ = lean_unbox(v_compile_6162_);
v_logCompileErrors_boxed_6177_ = lean_unbox(v_logCompileErrors_6163_);
v_isMeta_boxed_6178_ = lean_unbox(v_isMeta_6164_);
v_res_6179_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_inst_6158_, v_expectedType_6159_, v___x_159881__boxed_6174_, v___x_159882__boxed_6175_, v_compile_boxed_6176_, v_logCompileErrors_boxed_6177_, v_isMeta_boxed_6178_, v_val_6165_, v_x_6166_, v_x_6167_, v_x_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_);
lean_dec(v___y_6172_);
lean_dec_ref(v___y_6171_);
lean_dec(v___y_6170_);
lean_dec_ref(v___y_6169_);
lean_dec(v_x_6168_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object* v_inst_6180_, lean_object* v_expectedType_6181_, lean_object* v___x_6182_, lean_object* v_compile_6183_, lean_object* v_logCompileErrors_6184_, lean_object* v_isMeta_6185_, lean_object* v_val_6186_, lean_object* v_x_6187_, lean_object* v_x_6188_, lean_object* v_x_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
uint8_t v___x_160050__boxed_6195_; uint8_t v_compile_boxed_6196_; uint8_t v_logCompileErrors_boxed_6197_; uint8_t v_isMeta_boxed_6198_; lean_object* v_res_6199_; 
v___x_160050__boxed_6195_ = lean_unbox(v___x_6182_);
v_compile_boxed_6196_ = lean_unbox(v_compile_6183_);
v_logCompileErrors_boxed_6197_ = lean_unbox(v_logCompileErrors_6184_);
v_isMeta_boxed_6198_ = lean_unbox(v_isMeta_6185_);
v_res_6199_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_6180_, v_expectedType_6181_, v___x_160050__boxed_6195_, v_compile_boxed_6196_, v_logCompileErrors_boxed_6197_, v_isMeta_boxed_6198_, v_val_6186_, v_x_6187_, v_x_6188_, v_x_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6191_);
lean_dec_ref(v___y_6190_);
lean_dec(v_x_6189_);
return v_res_6199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8_spec__9___boxed(lean_object* v_inst_6200_, lean_object* v_expectedType_6201_, lean_object* v___x_6202_, lean_object* v_compile_6203_, lean_object* v_logCompileErrors_6204_, lean_object* v_isMeta_6205_, lean_object* v_val_6206_, lean_object* v_x_6207_, lean_object* v_x_6208_, lean_object* v_x_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_){
_start:
{
uint8_t v___x_160218__boxed_6215_; uint8_t v_compile_boxed_6216_; uint8_t v_logCompileErrors_boxed_6217_; uint8_t v_isMeta_boxed_6218_; lean_object* v_res_6219_; 
v___x_160218__boxed_6215_ = lean_unbox(v___x_6202_);
v_compile_boxed_6216_ = lean_unbox(v_compile_6203_);
v_logCompileErrors_boxed_6217_ = lean_unbox(v_logCompileErrors_6204_);
v_isMeta_boxed_6218_ = lean_unbox(v_isMeta_6205_);
v_res_6219_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8_spec__9(v_inst_6200_, v_expectedType_6201_, v___x_160218__boxed_6215_, v_compile_boxed_6216_, v_logCompileErrors_boxed_6217_, v_isMeta_boxed_6218_, v_val_6206_, v_x_6207_, v_x_6208_, v_x_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
lean_dec(v___y_6213_);
lean_dec_ref(v___y_6212_);
lean_dec(v___y_6211_);
lean_dec_ref(v___y_6210_);
return v_res_6219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8___boxed(lean_object* v_inst_6220_, lean_object* v_expectedType_6221_, lean_object* v___x_6222_, lean_object* v_compile_6223_, lean_object* v_logCompileErrors_6224_, lean_object* v_isMeta_6225_, lean_object* v_val_6226_, lean_object* v_x_6227_, lean_object* v_x_6228_, lean_object* v_x_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
uint8_t v___x_160387__boxed_6235_; uint8_t v_compile_boxed_6236_; uint8_t v_logCompileErrors_boxed_6237_; uint8_t v_isMeta_boxed_6238_; lean_object* v_res_6239_; 
v___x_160387__boxed_6235_ = lean_unbox(v___x_6222_);
v_compile_boxed_6236_ = lean_unbox(v_compile_6223_);
v_logCompileErrors_boxed_6237_ = lean_unbox(v_logCompileErrors_6224_);
v_isMeta_boxed_6238_ = lean_unbox(v_isMeta_6225_);
v_res_6239_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__8(v_inst_6220_, v_expectedType_6221_, v___x_160387__boxed_6235_, v_compile_boxed_6236_, v_logCompileErrors_boxed_6237_, v_isMeta_boxed_6238_, v_val_6226_, v_x_6227_, v_x_6228_, v_x_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
lean_dec(v___y_6233_);
lean_dec_ref(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec_ref(v___y_6230_);
lean_dec(v_x_6229_);
return v_res_6239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_6240_ = _args[0];
lean_object* v_fst_6241_ = _args[1];
lean_object* v_args_6242_ = _args[2];
lean_object* v___x_6243_ = _args[3];
lean_object* v_compile_6244_ = _args[4];
lean_object* v_logCompileErrors_6245_ = _args[5];
lean_object* v___x_6246_ = _args[6];
lean_object* v_isMeta_6247_ = _args[7];
lean_object* v_val_6248_ = _args[8];
lean_object* v_expectedType_6249_ = _args[9];
lean_object* v_a_6250_ = _args[10];
lean_object* v_b_6251_ = _args[11];
lean_object* v___y_6252_ = _args[12];
lean_object* v___y_6253_ = _args[13];
lean_object* v___y_6254_ = _args[14];
lean_object* v___y_6255_ = _args[15];
lean_object* v___y_6256_ = _args[16];
_start:
{
uint8_t v___x_160583__boxed_6257_; uint8_t v_compile_boxed_6258_; uint8_t v_logCompileErrors_boxed_6259_; uint8_t v___x_160584__boxed_6260_; uint8_t v_isMeta_boxed_6261_; lean_object* v_res_6262_; 
v___x_160583__boxed_6257_ = lean_unbox(v___x_6243_);
v_compile_boxed_6258_ = lean_unbox(v_compile_6244_);
v_logCompileErrors_boxed_6259_ = lean_unbox(v_logCompileErrors_6245_);
v___x_160584__boxed_6260_ = lean_unbox(v___x_6246_);
v_isMeta_boxed_6261_ = lean_unbox(v_isMeta_6247_);
v_res_6262_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_upperBound_6240_, v_fst_6241_, v_args_6242_, v___x_160583__boxed_6257_, v_compile_boxed_6258_, v_logCompileErrors_boxed_6259_, v___x_160584__boxed_6260_, v_isMeta_boxed_6261_, v_val_6248_, v_expectedType_6249_, v_a_6250_, v_b_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec_ref(v_args_6242_);
lean_dec_ref(v_fst_6241_);
lean_dec(v_upperBound_6240_);
return v_res_6262_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___boxed(lean_object* v_upperBound_6263_, lean_object* v_fst_6264_, lean_object* v_args_6265_, lean_object* v_compile_6266_, lean_object* v_logCompileErrors_6267_, lean_object* v___x_6268_, lean_object* v_isMeta_6269_, lean_object* v_val_6270_, lean_object* v_expectedType_6271_, lean_object* v_a_6272_, lean_object* v_b_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_){
_start:
{
uint8_t v_compile_boxed_6279_; uint8_t v_logCompileErrors_boxed_6280_; uint8_t v___x_160734__boxed_6281_; uint8_t v_isMeta_boxed_6282_; lean_object* v_res_6283_; 
v_compile_boxed_6279_ = lean_unbox(v_compile_6266_);
v_logCompileErrors_boxed_6280_ = lean_unbox(v_logCompileErrors_6267_);
v___x_160734__boxed_6281_ = lean_unbox(v___x_6268_);
v_isMeta_boxed_6282_ = lean_unbox(v_isMeta_6269_);
v_res_6283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_upperBound_6263_, v_fst_6264_, v_args_6265_, v_compile_boxed_6279_, v_logCompileErrors_boxed_6280_, v___x_160734__boxed_6281_, v_isMeta_boxed_6282_, v_val_6270_, v_expectedType_6271_, v_a_6272_, v_b_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
lean_dec(v___y_6277_);
lean_dec_ref(v___y_6276_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec_ref(v_args_6265_);
lean_dec_ref(v_fst_6264_);
lean_dec(v_upperBound_6263_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_6284_ = _args[0];
lean_object* v_fst_6285_ = _args[1];
lean_object* v_args_6286_ = _args[2];
lean_object* v___x_6287_ = _args[3];
lean_object* v_compile_6288_ = _args[4];
lean_object* v_logCompileErrors_6289_ = _args[5];
lean_object* v___x_6290_ = _args[6];
lean_object* v_isMeta_6291_ = _args[7];
lean_object* v_val_6292_ = _args[8];
lean_object* v_expectedType_6293_ = _args[9];
lean_object* v_a_6294_ = _args[10];
lean_object* v_b_6295_ = _args[11];
lean_object* v___y_6296_ = _args[12];
lean_object* v___y_6297_ = _args[13];
lean_object* v___y_6298_ = _args[14];
lean_object* v___y_6299_ = _args[15];
lean_object* v___y_6300_ = _args[16];
_start:
{
uint8_t v___x_160893__boxed_6301_; uint8_t v_compile_boxed_6302_; uint8_t v_logCompileErrors_boxed_6303_; uint8_t v___x_160894__boxed_6304_; uint8_t v_isMeta_boxed_6305_; lean_object* v_res_6306_; 
v___x_160893__boxed_6301_ = lean_unbox(v___x_6287_);
v_compile_boxed_6302_ = lean_unbox(v_compile_6288_);
v_logCompileErrors_boxed_6303_ = lean_unbox(v_logCompileErrors_6289_);
v___x_160894__boxed_6304_ = lean_unbox(v___x_6290_);
v_isMeta_boxed_6305_ = lean_unbox(v_isMeta_6291_);
v_res_6306_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___redArg(v_upperBound_6284_, v_fst_6285_, v_args_6286_, v___x_160893__boxed_6301_, v_compile_boxed_6302_, v_logCompileErrors_boxed_6303_, v___x_160894__boxed_6304_, v_isMeta_boxed_6305_, v_val_6292_, v_expectedType_6293_, v_a_6294_, v_b_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_);
lean_dec(v___y_6299_);
lean_dec_ref(v___y_6298_);
lean_dec(v___y_6297_);
lean_dec_ref(v___y_6296_);
lean_dec_ref(v_args_6286_);
lean_dec_ref(v_fst_6285_);
lean_dec(v_upperBound_6284_);
return v_res_6306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object* v_upperBound_6307_, lean_object* v_fst_6308_, lean_object* v_args_6309_, lean_object* v___x_6310_, lean_object* v_compile_6311_, lean_object* v_logCompileErrors_6312_, lean_object* v_isMeta_6313_, lean_object* v_val_6314_, lean_object* v_expectedType_6315_, lean_object* v_a_6316_, lean_object* v_b_6317_, lean_object* v___y_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_){
_start:
{
uint8_t v___x_161054__boxed_6323_; uint8_t v_compile_boxed_6324_; uint8_t v_logCompileErrors_boxed_6325_; uint8_t v_isMeta_boxed_6326_; lean_object* v_res_6327_; 
v___x_161054__boxed_6323_ = lean_unbox(v___x_6310_);
v_compile_boxed_6324_ = lean_unbox(v_compile_6311_);
v_logCompileErrors_boxed_6325_ = lean_unbox(v_logCompileErrors_6312_);
v_isMeta_boxed_6326_ = lean_unbox(v_isMeta_6313_);
v_res_6327_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_6307_, v_fst_6308_, v_args_6309_, v___x_161054__boxed_6323_, v_compile_boxed_6324_, v_logCompileErrors_boxed_6325_, v_isMeta_boxed_6326_, v_val_6314_, v_expectedType_6315_, v_a_6316_, v_b_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_);
lean_dec(v___y_6321_);
lean_dec_ref(v___y_6320_);
lean_dec(v___y_6319_);
lean_dec_ref(v___y_6318_);
lean_dec_ref(v_args_6309_);
lean_dec_ref(v_fst_6308_);
lean_dec(v_upperBound_6307_);
return v_res_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object* v_inst_6328_, lean_object* v_expectedType_6329_, lean_object* v_compile_6330_, lean_object* v_logCompileErrors_6331_, lean_object* v_isMeta_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_){
_start:
{
uint8_t v_compile_boxed_6338_; uint8_t v_logCompileErrors_boxed_6339_; uint8_t v_isMeta_boxed_6340_; lean_object* v_res_6341_; 
v_compile_boxed_6338_ = lean_unbox(v_compile_6330_);
v_logCompileErrors_boxed_6339_ = lean_unbox(v_logCompileErrors_6331_);
v_isMeta_boxed_6340_ = lean_unbox(v_isMeta_6332_);
v_res_6341_ = l_Lean_Meta_wrapInstance(v_inst_6328_, v_expectedType_6329_, v_compile_boxed_6338_, v_logCompileErrors_boxed_6339_, v_isMeta_boxed_6340_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_);
lean_dec(v_a_6336_);
lean_dec_ref(v_a_6335_);
lean_dec(v_a_6334_);
lean_dec_ref(v_a_6333_);
return v_res_6341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(size_t v_sz_6342_, size_t v_i_6343_, lean_object* v_bs_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_){
_start:
{
lean_object* v___x_6350_; 
v___x_6350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_6342_, v_i_6343_, v_bs_6344_, v___y_6346_);
return v___x_6350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object* v_sz_6351_, lean_object* v_i_6352_, lean_object* v_bs_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_){
_start:
{
size_t v_sz_boxed_6359_; size_t v_i_boxed_6360_; lean_object* v_res_6361_; 
v_sz_boxed_6359_ = lean_unbox_usize(v_sz_6351_);
lean_dec(v_sz_6351_);
v_i_boxed_6360_ = lean_unbox_usize(v_i_6352_);
lean_dec(v_i_6352_);
v_res_6361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_boxed_6359_, v_i_boxed_6360_, v_bs_6353_, v___y_6354_, v___y_6355_, v___y_6356_, v___y_6357_);
lean_dec(v___y_6357_);
lean_dec_ref(v___y_6356_);
lean_dec(v___y_6355_);
lean_dec_ref(v___y_6354_);
return v_res_6361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(lean_object* v_upperBound_6362_, lean_object* v_fst_6363_, lean_object* v_args_6364_, uint8_t v_compile_6365_, uint8_t v_logCompileErrors_6366_, uint8_t v___x_6367_, uint8_t v_isMeta_6368_, lean_object* v_val_6369_, lean_object* v_expectedType_6370_, lean_object* v_inst_6371_, lean_object* v_R_6372_, lean_object* v_a_6373_, lean_object* v_b_6374_, lean_object* v_c_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_upperBound_6362_, v_fst_6363_, v_args_6364_, v_compile_6365_, v_logCompileErrors_6366_, v___x_6367_, v_isMeta_6368_, v_val_6369_, v_expectedType_6370_, v_a_6373_, v_b_6374_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_);
return v___x_6381_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_6382_ = _args[0];
lean_object* v_fst_6383_ = _args[1];
lean_object* v_args_6384_ = _args[2];
lean_object* v_compile_6385_ = _args[3];
lean_object* v_logCompileErrors_6386_ = _args[4];
lean_object* v___x_6387_ = _args[5];
lean_object* v_isMeta_6388_ = _args[6];
lean_object* v_val_6389_ = _args[7];
lean_object* v_expectedType_6390_ = _args[8];
lean_object* v_inst_6391_ = _args[9];
lean_object* v_R_6392_ = _args[10];
lean_object* v_a_6393_ = _args[11];
lean_object* v_b_6394_ = _args[12];
lean_object* v_c_6395_ = _args[13];
lean_object* v___y_6396_ = _args[14];
lean_object* v___y_6397_ = _args[15];
lean_object* v___y_6398_ = _args[16];
lean_object* v___y_6399_ = _args[17];
lean_object* v___y_6400_ = _args[18];
_start:
{
uint8_t v_compile_boxed_6401_; uint8_t v_logCompileErrors_boxed_6402_; uint8_t v___x_165548__boxed_6403_; uint8_t v_isMeta_boxed_6404_; lean_object* v_res_6405_; 
v_compile_boxed_6401_ = lean_unbox(v_compile_6385_);
v_logCompileErrors_boxed_6402_ = lean_unbox(v_logCompileErrors_6386_);
v___x_165548__boxed_6403_ = lean_unbox(v___x_6387_);
v_isMeta_boxed_6404_ = lean_unbox(v_isMeta_6388_);
v_res_6405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(v_upperBound_6382_, v_fst_6383_, v_args_6384_, v_compile_boxed_6401_, v_logCompileErrors_boxed_6402_, v___x_165548__boxed_6403_, v_isMeta_boxed_6404_, v_val_6389_, v_expectedType_6390_, v_inst_6391_, v_R_6392_, v_a_6393_, v_b_6394_, v_c_6395_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_);
lean_dec(v___y_6399_);
lean_dec_ref(v___y_6398_);
lean_dec(v___y_6397_);
lean_dec_ref(v___y_6396_);
lean_dec_ref(v_args_6384_);
lean_dec_ref(v_fst_6383_);
lean_dec(v_upperBound_6382_);
return v_res_6405_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14(lean_object* v_00_u03b1_6406_, lean_object* v_x_6407_, lean_object* v___y_6408_, lean_object* v___y_6409_, lean_object* v___y_6410_, lean_object* v___y_6411_){
_start:
{
lean_object* v___x_6413_; 
v___x_6413_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___redArg(v_x_6407_);
return v___x_6413_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14___boxed(lean_object* v_00_u03b1_6414_, lean_object* v_x_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_, lean_object* v___y_6420_){
_start:
{
lean_object* v_res_6421_; 
v_res_6421_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__10_spec__14(v_00_u03b1_6414_, v_x_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6418_);
lean_dec(v___y_6417_);
lean_dec_ref(v___y_6416_);
return v_res_6421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(lean_object* v_upperBound_6422_, lean_object* v_fst_6423_, lean_object* v_args_6424_, uint8_t v___x_6425_, uint8_t v_compile_6426_, uint8_t v_logCompileErrors_6427_, uint8_t v___x_6428_, uint8_t v_isMeta_6429_, lean_object* v_val_6430_, lean_object* v_expectedType_6431_, lean_object* v_inst_6432_, lean_object* v_R_6433_, lean_object* v_a_6434_, lean_object* v_b_6435_, lean_object* v_c_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_, lean_object* v___y_6440_){
_start:
{
lean_object* v___x_6442_; 
v___x_6442_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_upperBound_6422_, v_fst_6423_, v_args_6424_, v___x_6425_, v_compile_6426_, v_logCompileErrors_6427_, v___x_6428_, v_isMeta_6429_, v_val_6430_, v_expectedType_6431_, v_a_6434_, v_b_6435_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_);
return v___x_6442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_6443_ = _args[0];
lean_object* v_fst_6444_ = _args[1];
lean_object* v_args_6445_ = _args[2];
lean_object* v___x_6446_ = _args[3];
lean_object* v_compile_6447_ = _args[4];
lean_object* v_logCompileErrors_6448_ = _args[5];
lean_object* v___x_6449_ = _args[6];
lean_object* v_isMeta_6450_ = _args[7];
lean_object* v_val_6451_ = _args[8];
lean_object* v_expectedType_6452_ = _args[9];
lean_object* v_inst_6453_ = _args[10];
lean_object* v_R_6454_ = _args[11];
lean_object* v_a_6455_ = _args[12];
lean_object* v_b_6456_ = _args[13];
lean_object* v_c_6457_ = _args[14];
lean_object* v___y_6458_ = _args[15];
lean_object* v___y_6459_ = _args[16];
lean_object* v___y_6460_ = _args[17];
lean_object* v___y_6461_ = _args[18];
lean_object* v___y_6462_ = _args[19];
_start:
{
uint8_t v___x_165600__boxed_6463_; uint8_t v_compile_boxed_6464_; uint8_t v_logCompileErrors_boxed_6465_; uint8_t v___x_165601__boxed_6466_; uint8_t v_isMeta_boxed_6467_; lean_object* v_res_6468_; 
v___x_165600__boxed_6463_ = lean_unbox(v___x_6446_);
v_compile_boxed_6464_ = lean_unbox(v_compile_6447_);
v_logCompileErrors_boxed_6465_ = lean_unbox(v_logCompileErrors_6448_);
v___x_165601__boxed_6466_ = lean_unbox(v___x_6449_);
v_isMeta_boxed_6467_ = lean_unbox(v_isMeta_6450_);
v_res_6468_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(v_upperBound_6443_, v_fst_6444_, v_args_6445_, v___x_165600__boxed_6463_, v_compile_boxed_6464_, v_logCompileErrors_boxed_6465_, v___x_165601__boxed_6466_, v_isMeta_boxed_6467_, v_val_6451_, v_expectedType_6452_, v_inst_6453_, v_R_6454_, v_a_6455_, v_b_6456_, v_c_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_);
lean_dec(v___y_6461_);
lean_dec_ref(v___y_6460_);
lean_dec(v___y_6459_);
lean_dec_ref(v___y_6458_);
lean_dec_ref(v_args_6445_);
lean_dec_ref(v_fst_6444_);
lean_dec(v_upperBound_6443_);
return v_res_6468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object* v_upperBound_6469_, lean_object* v_fst_6470_, lean_object* v_args_6471_, uint8_t v___x_6472_, uint8_t v_compile_6473_, uint8_t v_logCompileErrors_6474_, uint8_t v_isMeta_6475_, lean_object* v_val_6476_, lean_object* v_expectedType_6477_, lean_object* v_inst_6478_, lean_object* v_R_6479_, lean_object* v_a_6480_, lean_object* v_b_6481_, lean_object* v_c_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_){
_start:
{
lean_object* v___x_6488_; 
v___x_6488_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_6469_, v_fst_6470_, v_args_6471_, v___x_6472_, v_compile_6473_, v_logCompileErrors_6474_, v_isMeta_6475_, v_val_6476_, v_expectedType_6477_, v_a_6480_, v_b_6481_, v___y_6483_, v___y_6484_, v___y_6485_, v___y_6486_);
return v___x_6488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object** _args){
lean_object* v_upperBound_6489_ = _args[0];
lean_object* v_fst_6490_ = _args[1];
lean_object* v_args_6491_ = _args[2];
lean_object* v___x_6492_ = _args[3];
lean_object* v_compile_6493_ = _args[4];
lean_object* v_logCompileErrors_6494_ = _args[5];
lean_object* v_isMeta_6495_ = _args[6];
lean_object* v_val_6496_ = _args[7];
lean_object* v_expectedType_6497_ = _args[8];
lean_object* v_inst_6498_ = _args[9];
lean_object* v_R_6499_ = _args[10];
lean_object* v_a_6500_ = _args[11];
lean_object* v_b_6501_ = _args[12];
lean_object* v_c_6502_ = _args[13];
lean_object* v___y_6503_ = _args[14];
lean_object* v___y_6504_ = _args[15];
lean_object* v___y_6505_ = _args[16];
lean_object* v___y_6506_ = _args[17];
lean_object* v___y_6507_ = _args[18];
_start:
{
uint8_t v___x_165635__boxed_6508_; uint8_t v_compile_boxed_6509_; uint8_t v_logCompileErrors_boxed_6510_; uint8_t v_isMeta_boxed_6511_; lean_object* v_res_6512_; 
v___x_165635__boxed_6508_ = lean_unbox(v___x_6492_);
v_compile_boxed_6509_ = lean_unbox(v_compile_6493_);
v_logCompileErrors_boxed_6510_ = lean_unbox(v_logCompileErrors_6494_);
v_isMeta_boxed_6511_ = lean_unbox(v_isMeta_6495_);
v_res_6512_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(v_upperBound_6489_, v_fst_6490_, v_args_6491_, v___x_165635__boxed_6508_, v_compile_boxed_6509_, v_logCompileErrors_boxed_6510_, v_isMeta_boxed_6511_, v_val_6496_, v_expectedType_6497_, v_inst_6498_, v_R_6499_, v_a_6500_, v_b_6501_, v_c_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_);
lean_dec(v___y_6506_);
lean_dec_ref(v___y_6505_);
lean_dec(v___y_6504_);
lean_dec_ref(v___y_6503_);
lean_dec_ref(v_args_6491_);
lean_dec_ref(v_fst_6490_);
lean_dec(v_upperBound_6489_);
return v_res_6512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(lean_object* v_00_u03b1_6513_, lean_object* v_constName_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_){
_start:
{
lean_object* v___x_6520_; 
v___x_6520_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
return v___x_6520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___boxed(lean_object* v_00_u03b1_6521_, lean_object* v_constName_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_){
_start:
{
lean_object* v_res_6528_; 
v_res_6528_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(v_00_u03b1_6521_, v_constName_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
lean_dec(v___y_6526_);
lean_dec_ref(v___y_6525_);
lean_dec(v___y_6524_);
lean_dec_ref(v___y_6523_);
return v_res_6528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17(lean_object* v_upperBound_6529_, lean_object* v_fst_6530_, lean_object* v_args_6531_, uint8_t v___x_6532_, uint8_t v_compile_6533_, uint8_t v_logCompileErrors_6534_, uint8_t v___x_6535_, uint8_t v_isMeta_6536_, lean_object* v_val_6537_, lean_object* v_expectedType_6538_, lean_object* v_inst_6539_, lean_object* v_R_6540_, lean_object* v_a_6541_, lean_object* v_b_6542_, lean_object* v_c_6543_, lean_object* v___y_6544_, lean_object* v___y_6545_, lean_object* v___y_6546_, lean_object* v___y_6547_){
_start:
{
lean_object* v___x_6549_; 
v___x_6549_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___redArg(v_upperBound_6529_, v_fst_6530_, v_args_6531_, v___x_6532_, v_compile_6533_, v_logCompileErrors_6534_, v___x_6535_, v_isMeta_6536_, v_val_6537_, v_expectedType_6538_, v_a_6541_, v_b_6542_, v___y_6544_, v___y_6545_, v___y_6546_, v___y_6547_);
return v___x_6549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17___boxed(lean_object** _args){
lean_object* v_upperBound_6550_ = _args[0];
lean_object* v_fst_6551_ = _args[1];
lean_object* v_args_6552_ = _args[2];
lean_object* v___x_6553_ = _args[3];
lean_object* v_compile_6554_ = _args[4];
lean_object* v_logCompileErrors_6555_ = _args[5];
lean_object* v___x_6556_ = _args[6];
lean_object* v_isMeta_6557_ = _args[7];
lean_object* v_val_6558_ = _args[8];
lean_object* v_expectedType_6559_ = _args[9];
lean_object* v_inst_6560_ = _args[10];
lean_object* v_R_6561_ = _args[11];
lean_object* v_a_6562_ = _args[12];
lean_object* v_b_6563_ = _args[13];
lean_object* v_c_6564_ = _args[14];
lean_object* v___y_6565_ = _args[15];
lean_object* v___y_6566_ = _args[16];
lean_object* v___y_6567_ = _args[17];
lean_object* v___y_6568_ = _args[18];
lean_object* v___y_6569_ = _args[19];
_start:
{
uint8_t v___x_165684__boxed_6570_; uint8_t v_compile_boxed_6571_; uint8_t v_logCompileErrors_boxed_6572_; uint8_t v___x_165685__boxed_6573_; uint8_t v_isMeta_boxed_6574_; lean_object* v_res_6575_; 
v___x_165684__boxed_6570_ = lean_unbox(v___x_6553_);
v_compile_boxed_6571_ = lean_unbox(v_compile_6554_);
v_logCompileErrors_boxed_6572_ = lean_unbox(v_logCompileErrors_6555_);
v___x_165685__boxed_6573_ = lean_unbox(v___x_6556_);
v_isMeta_boxed_6574_ = lean_unbox(v_isMeta_6557_);
v_res_6575_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__17(v_upperBound_6550_, v_fst_6551_, v_args_6552_, v___x_165684__boxed_6570_, v_compile_boxed_6571_, v_logCompileErrors_boxed_6572_, v___x_165685__boxed_6573_, v_isMeta_boxed_6574_, v_val_6558_, v_expectedType_6559_, v_inst_6560_, v_R_6561_, v_a_6562_, v_b_6563_, v_c_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
lean_dec(v___y_6568_);
lean_dec_ref(v___y_6567_);
lean_dec(v___y_6566_);
lean_dec_ref(v___y_6565_);
lean_dec_ref(v_args_6552_);
lean_dec_ref(v_fst_6551_);
lean_dec(v_upperBound_6550_);
return v_res_6575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6(lean_object* v_00_u03b1_6576_, lean_object* v_ref_6577_, lean_object* v_constName_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_){
_start:
{
lean_object* v___x_6584_; 
v___x_6584_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___redArg(v_ref_6577_, v_constName_6578_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_);
return v___x_6584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6___boxed(lean_object* v_00_u03b1_6585_, lean_object* v_ref_6586_, lean_object* v_constName_6587_, lean_object* v___y_6588_, lean_object* v___y_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_, lean_object* v___y_6592_){
_start:
{
lean_object* v_res_6593_; 
v_res_6593_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6(v_00_u03b1_6585_, v_ref_6586_, v_constName_6587_, v___y_6588_, v___y_6589_, v___y_6590_, v___y_6591_);
lean_dec(v___y_6591_);
lean_dec_ref(v___y_6590_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v_ref_6586_);
return v_res_6593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19(lean_object* v_00_u03b1_6594_, lean_object* v_ref_6595_, lean_object* v_msg_6596_, lean_object* v_declHint_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_){
_start:
{
lean_object* v___x_6603_; 
v___x_6603_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___redArg(v_ref_6595_, v_msg_6596_, v_declHint_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_);
return v___x_6603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19___boxed(lean_object* v_00_u03b1_6604_, lean_object* v_ref_6605_, lean_object* v_msg_6606_, lean_object* v_declHint_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_, lean_object* v___y_6611_, lean_object* v___y_6612_){
_start:
{
lean_object* v_res_6613_; 
v_res_6613_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19(v_00_u03b1_6604_, v_ref_6605_, v_msg_6606_, v_declHint_6607_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_);
lean_dec(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec(v___y_6609_);
lean_dec_ref(v___y_6608_);
lean_dec(v_ref_6605_);
return v_res_6613_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27(lean_object* v_msg_6614_, lean_object* v_declHint_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_){
_start:
{
lean_object* v___x_6621_; 
v___x_6621_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___redArg(v_msg_6614_, v_declHint_6615_, v___y_6619_);
return v___x_6621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27___boxed(lean_object* v_msg_6622_, lean_object* v_declHint_6623_, lean_object* v___y_6624_, lean_object* v___y_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_){
_start:
{
lean_object* v_res_6629_; 
v_res_6629_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__25_spec__27(v_msg_6622_, v_declHint_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_);
lean_dec(v___y_6627_);
lean_dec_ref(v___y_6626_);
lean_dec(v___y_6625_);
lean_dec_ref(v___y_6624_);
return v_res_6629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26(lean_object* v_00_u03b1_6630_, lean_object* v_ref_6631_, lean_object* v_msg_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_){
_start:
{
lean_object* v___x_6638_; 
v___x_6638_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___redArg(v_ref_6631_, v_msg_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_);
return v___x_6638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26___boxed(lean_object* v_00_u03b1_6639_, lean_object* v_ref_6640_, lean_object* v_msg_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_, lean_object* v___y_6646_){
_start:
{
lean_object* v_res_6647_; 
v_res_6647_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__6_spec__19_spec__26(v_00_u03b1_6639_, v_ref_6640_, v_msg_6641_, v___y_6642_, v___y_6643_, v___y_6644_, v___y_6645_);
lean_dec(v___y_6645_);
lean_dec_ref(v___y_6644_);
lean_dec(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec(v_ref_6640_);
return v_res_6647_;
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
