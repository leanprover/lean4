// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Eqns
// Imports: public import Lean.Elab.PreDefinition.FixedParams import Init.Internal.Order.Basic import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.Refl
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*);
static const lean_string_object l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2;
static const lean_array_object l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3 = (const lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PartialFixpoint"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 126, 228, 214, 96, 108, 195, 201)}};
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 154, 190, 235, 71, 53, 215, 0)}};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "deltaLHSUntilFix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 223, 150, 107, 82, 172, 43, 154)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value),LEAN_SCALAR_PTR_LITERAL(18, 104, 23, 57, 110, 104, 99, 16)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 115, 213, 20, 156, 86, 56, 31)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "rwFixUnder: unexpected expression "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lfp_monotone_fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value),LEAN_SCALAR_PTR_LITERAL(178, 113, 187, 250, 69, 106, 19, 81)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fix_eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value),LEAN_SCALAR_PTR_LITERAL(83, 197, 58, 21, 58, 52, 66, 18)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Elab.PreDefinition.PartialFixpoint.Eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "_private.Lean.Elab.PreDefinition.PartialFixpoint.Eqns.0.Lean.Elab.PartialFixpoint.rwFixEq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "mkUnfoldEq rfl succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mkUnfoldEq after rwFixEq:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mkUnfoldEq after deltaLHS:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to generate unfold theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mkUnfoldEq start:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
v___x_10_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3));
v___x_11_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2, &l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2);
v___x_12_ = lean_box(0);
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_11_);
lean_ctor_set(v___x_14_, 3, v___x_11_);
lean_ctor_set(v___x_14_, 4, v___x_10_);
lean_ctor_set(v___x_14_, 5, v___x_13_);
lean_ctor_set(v___x_14_, 6, v___x_9_);
lean_ctor_set(v___x_14_, 7, v___x_10_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4, &l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once, _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
return v___x_16_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_17_, lean_object* v_n_18_, lean_object* v_x_19_){
_start:
{
uint8_t v___x_20_; lean_object* v___x_21_; 
v___x_20_ = 0;
v___x_21_ = l_Lean_Environment_find_x3f(v_env_17_, v_n_18_, v___x_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
return v___x_20_;
}
else
{
lean_object* v_val_22_; uint8_t v___x_23_; 
v_val_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_val_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = l_Lean_ConstantInfo_hasValue(v_val_22_, v___x_20_);
lean_dec(v_val_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_24_, lean_object* v_n_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(v_env_24_, v_n_25_, v_x_26_);
lean_dec_ref(v_x_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v_k_31_; lean_object* v_v_32_; lean_object* v_l_33_; lean_object* v_r_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_k_31_ = lean_ctor_get(v_x_30_, 1);
v_v_32_ = lean_ctor_get(v_x_30_, 2);
v_l_33_ = lean_ctor_get(v_x_30_, 3);
v_r_34_ = lean_ctor_get(v_x_30_, 4);
v___x_35_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_29_, v_l_33_);
lean_inc(v_v_32_);
lean_inc(v_k_31_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_k_31_);
lean_ctor_set(v___x_36_, 1, v_v_32_);
v___x_37_ = lean_array_push(v___x_35_, v___x_36_);
v_init_29_ = v___x_37_;
v_x_30_ = v_r_34_;
goto _start;
}
else
{
return v_init_29_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_39_, v_x_40_);
lean_dec(v_x_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_44_, lean_object* v_s_45_, uint8_t v_x_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___f_47_ = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_47_, 0, v_env_44_);
v___x_48_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_47_, v_s_45_);
v___x_49_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_50_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v___x_49_, v___x_48_);
lean_dec(v___x_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_51_, lean_object* v_s_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_x_232__boxed_54_; lean_object* v_res_55_; 
v_x_232__boxed_54_ = lean_unbox(v_x_53_);
v_res_55_ = l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(v_env_51_, v_s_52_, v_x_232__boxed_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___f_69_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_70_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_71_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_72_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_70_, v___x_71_, v___f_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object* v_init_75_, lean_object* v_t_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_75_, v_t_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_78_, lean_object* v_t_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0(v_init_78_, v_t_79_);
lean_dec(v_t_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v___x_81_, uint8_t v___x_82_, uint8_t v_____do__lift_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
if (v_____do__lift_83_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(v___x_81_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_box(v___x_82_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v___x_93_, lean_object* v___x_94_, lean_object* v_____do__lift_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
uint8_t v___x_4038__boxed_101_; uint8_t v___x_4039__boxed_102_; uint8_t v_____do__lift_4040__boxed_103_; lean_object* v_res_104_; 
v___x_4038__boxed_101_ = lean_unbox(v___x_93_);
v___x_4039__boxed_102_ = lean_unbox(v___x_94_);
v_____do__lift_4040__boxed_103_ = lean_unbox(v_____do__lift_95_);
v_res_104_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_4038__boxed_101_, v___x_4039__boxed_102_, v_____do__lift_4040__boxed_103_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_104_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_105_, size_t v_i_106_, size_t v_stop_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_usize_dec_eq(v_i_106_, v_stop_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; uint8_t v_kind_110_; uint8_t v___x_111_; uint8_t v___x_112_; 
v___x_109_ = lean_array_uget_borrowed(v_as_105_, v_i_106_);
v_kind_110_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*9);
v___x_111_ = 1;
v___x_112_ = l_Lean_Elab_DefKind_isTheorem(v_kind_110_);
if (v___x_112_ == 0)
{
return v___x_111_;
}
else
{
if (v___x_108_ == 0)
{
size_t v___x_113_; size_t v___x_114_; 
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_add(v_i_106_, v___x_113_);
v_i_106_ = v___x_114_;
goto _start;
}
else
{
return v___x_111_;
}
}
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_117_, lean_object* v_i_118_, lean_object* v_stop_119_){
_start:
{
size_t v_i_boxed_120_; size_t v_stop_boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_i_boxed_120_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_stop_boxed_121_ = lean_unbox_usize(v_stop_119_);
lean_dec(v_stop_119_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_117_, v_i_boxed_120_, v_stop_boxed_121_);
lean_dec_ref(v_as_117_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_124_, lean_object* v_declNameNonRec_125_, lean_object* v_fixedParamPerms_126_, lean_object* v_fixpointType_127_, lean_object* v_as_128_, size_t v_i_129_, size_t v_stop_130_, lean_object* v_b_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = lean_usize_dec_eq(v_i_129_, v_stop_130_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v_levelParams_134_; lean_object* v_declName_135_; lean_object* v_type_136_; lean_object* v_value_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; size_t v___x_141_; size_t v___x_142_; 
v___x_133_ = lean_array_uget_borrowed(v_as_128_, v_i_129_);
v_levelParams_134_ = lean_ctor_get(v___x_133_, 1);
v_declName_135_ = lean_ctor_get(v___x_133_, 3);
v_type_136_ = lean_ctor_get(v___x_133_, 6);
v_value_137_ = lean_ctor_get(v___x_133_, 7);
v___x_138_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc_ref(v_fixpointType_127_);
lean_inc_ref(v_fixedParamPerms_126_);
lean_inc(v_declNameNonRec_125_);
lean_inc_ref(v___x_124_);
lean_inc_ref(v_value_137_);
lean_inc_ref(v_type_136_);
lean_inc(v_levelParams_134_);
lean_inc(v_declName_135_);
v___x_139_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_139_, 0, v_declName_135_);
lean_ctor_set(v___x_139_, 1, v_levelParams_134_);
lean_ctor_set(v___x_139_, 2, v_type_136_);
lean_ctor_set(v___x_139_, 3, v_value_137_);
lean_ctor_set(v___x_139_, 4, v___x_124_);
lean_ctor_set(v___x_139_, 5, v_declNameNonRec_125_);
lean_ctor_set(v___x_139_, 6, v_fixedParamPerms_126_);
lean_ctor_set(v___x_139_, 7, v_fixpointType_127_);
lean_inc(v_declName_135_);
v___x_140_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_138_, v_b_131_, v_declName_135_, v___x_139_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_add(v_i_129_, v___x_141_);
v_i_129_ = v___x_142_;
v_b_131_ = v___x_140_;
goto _start;
}
else
{
lean_dec_ref(v_fixpointType_127_);
lean_dec_ref(v_fixedParamPerms_126_);
lean_dec(v_declNameNonRec_125_);
lean_dec_ref(v___x_124_);
return v_b_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_144_, lean_object* v_declNameNonRec_145_, lean_object* v_fixedParamPerms_146_, lean_object* v_fixpointType_147_, lean_object* v_as_148_, lean_object* v_i_149_, lean_object* v_stop_150_, lean_object* v_b_151_){
_start:
{
size_t v_i_boxed_152_; size_t v_stop_boxed_153_; lean_object* v_res_154_; 
v_i_boxed_152_ = lean_unbox_usize(v_i_149_);
lean_dec(v_i_149_);
v_stop_boxed_153_ = lean_unbox_usize(v_stop_150_);
lean_dec(v_stop_150_);
v_res_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_144_, v_declNameNonRec_145_, v_fixedParamPerms_146_, v_fixpointType_147_, v_as_148_, v_i_boxed_152_, v_stop_boxed_153_, v_b_151_);
lean_dec_ref(v_as_148_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_155_, size_t v_i_156_, lean_object* v_bs_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = lean_usize_dec_lt(v_i_156_, v_sz_155_);
if (v___x_158_ == 0)
{
return v_bs_157_;
}
else
{
lean_object* v_v_159_; lean_object* v_declName_160_; lean_object* v___x_161_; lean_object* v_bs_x27_162_; size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; 
v_v_159_ = lean_array_uget_borrowed(v_bs_157_, v_i_156_);
v_declName_160_ = lean_ctor_get(v_v_159_, 3);
lean_inc(v_declName_160_);
v___x_161_ = lean_unsigned_to_nat(0u);
v_bs_x27_162_ = lean_array_uset(v_bs_157_, v_i_156_, v___x_161_);
v___x_163_ = ((size_t)1ULL);
v___x_164_ = lean_usize_add(v_i_156_, v___x_163_);
v___x_165_ = lean_array_uset(v_bs_x27_162_, v_i_156_, v_declName_160_);
v_i_156_ = v___x_164_;
v_bs_157_ = v___x_165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_167_, lean_object* v_i_168_, lean_object* v_bs_169_){
_start:
{
size_t v_sz_boxed_170_; size_t v_i_boxed_171_; lean_object* v_res_172_; 
v_sz_boxed_170_ = lean_unbox_usize(v_sz_167_);
lean_dec(v_sz_167_);
v_i_boxed_171_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_res_172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_170_, v_i_boxed_171_, v_bs_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_173_, size_t v_i_174_, size_t v_stop_175_, lean_object* v_b_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = lean_usize_dec_eq(v_i_174_, v_stop_175_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v_declName_182_; lean_object* v___x_183_; 
v___x_181_ = lean_array_uget_borrowed(v_as_173_, v_i_174_);
v_declName_182_ = lean_ctor_get(v___x_181_, 3);
lean_inc(v_declName_182_);
v___x_183_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_182_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; size_t v___x_185_; size_t v___x_186_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref(v___x_183_);
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_i_174_, v___x_185_);
v_i_174_ = v___x_186_;
v_b_176_ = v_a_184_;
goto _start;
}
else
{
return v___x_183_;
}
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_b_176_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_189_, lean_object* v_i_190_, lean_object* v_stop_191_, lean_object* v_b_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
size_t v_i_boxed_196_; size_t v_stop_boxed_197_; lean_object* v_res_198_; 
v_i_boxed_196_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_stop_boxed_197_ = lean_unbox_usize(v_stop_191_);
lean_dec(v_stop_191_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_189_, v_i_boxed_196_, v_stop_boxed_197_, v_b_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v_as_189_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t v___x_199_, lean_object* v_as_200_, size_t v_i_201_, size_t v_stop_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_eq(v_i_201_, v_stop_202_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v_type_214_; uint8_t v___x_215_; uint8_t v_a_217_; lean_object* v___x_220_; 
v___x_213_ = lean_array_uget_borrowed(v_as_200_, v_i_201_);
v_type_214_ = lean_ctor_get(v___x_213_, 6);
v___x_215_ = 1;
lean_inc_ref(v_type_214_);
v___x_220_ = l_Lean_Meta_isProp(v_type_214_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; uint8_t v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref(v___x_220_);
v___x_222_ = lean_unbox(v_a_221_);
lean_dec(v_a_221_);
if (v___x_222_ == 0)
{
v_a_217_ = v___x_199_;
goto v___jp_216_;
}
else
{
goto v___jp_208_;
}
}
else
{
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_223_; uint8_t v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_223_);
lean_dec_ref(v___x_220_);
v___x_224_ = lean_unbox(v_a_223_);
lean_dec(v_a_223_);
v_a_217_ = v___x_224_;
goto v___jp_216_;
}
else
{
return v___x_220_;
}
}
v___jp_216_:
{
if (v_a_217_ == 0)
{
goto v___jp_208_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_box(v___x_215_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
}
else
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = 0;
v___x_226_ = lean_box(v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
v___jp_208_:
{
size_t v___x_209_; size_t v___x_210_; 
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_201_, v___x_209_);
v_i_201_ = v___x_210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v___x_228_, lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_stop_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
uint8_t v___x_4143__boxed_237_; size_t v_i_boxed_238_; size_t v_stop_boxed_239_; lean_object* v_res_240_; 
v___x_4143__boxed_237_ = lean_unbox(v___x_228_);
v_i_boxed_238_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_stop_boxed_239_ = lean_unbox_usize(v_stop_231_);
lean_dec(v_stop_231_);
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4143__boxed_237_, v_as_229_, v_i_boxed_238_, v_stop_boxed_239_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec_ref(v_as_229_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_247_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
lean_ctor_set(v___x_247_, 3, v___x_246_);
lean_ctor_set(v___x_247_, 4, v___x_246_);
lean_ctor_set(v___x_247_, 5, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_248_, lean_object* v_declNameNonRec_249_, lean_object* v_fixedParamPerms_250_, lean_object* v_fixpointType_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_nextMacroScope_261_; lean_object* v_ngen_262_; lean_object* v_auxDeclNGen_263_; lean_object* v_traceState_264_; lean_object* v_messages_265_; lean_object* v_infoState_266_; lean_object* v_snapshotTasks_267_; lean_object* v___y_268_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___y_295_; lean_object* v___y_336_; uint8_t v___x_337_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_preDefs_248_);
v___x_337_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_337_ == 0)
{
goto v___jp_324_;
}
else
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_box(0);
v___x_339_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_339_ == 0)
{
if (v___x_337_ == 0)
{
goto v___jp_324_;
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_293_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_248_, v___x_340_, v___x_341_, v___x_338_, v_a_254_, v_a_255_);
v___y_336_ = v___x_342_;
goto v___jp_335_;
}
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_293_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_248_, v___x_343_, v___x_344_, v___x_338_, v_a_254_, v_a_255_);
v___y_336_ = v___x_345_;
goto v___jp_335_;
}
}
v___jp_257_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
v___jp_260_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_mctx_273_; lean_object* v_zetaDeltaFVarIds_274_; lean_object* v_postponed_275_; lean_object* v_diag_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_287_; 
v___x_269_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
v___x_270_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_270_, 0, v___y_268_);
lean_ctor_set(v___x_270_, 1, v_nextMacroScope_261_);
lean_ctor_set(v___x_270_, 2, v_ngen_262_);
lean_ctor_set(v___x_270_, 3, v_auxDeclNGen_263_);
lean_ctor_set(v___x_270_, 4, v_traceState_264_);
lean_ctor_set(v___x_270_, 5, v___x_269_);
lean_ctor_set(v___x_270_, 6, v_messages_265_);
lean_ctor_set(v___x_270_, 7, v_infoState_266_);
lean_ctor_set(v___x_270_, 8, v_snapshotTasks_267_);
v___x_271_ = lean_st_ref_set(v_a_255_, v___x_270_);
v___x_272_ = lean_st_ref_take(v_a_253_);
v_mctx_273_ = lean_ctor_get(v___x_272_, 0);
v_zetaDeltaFVarIds_274_ = lean_ctor_get(v___x_272_, 2);
v_postponed_275_ = lean_ctor_get(v___x_272_, 3);
v_diag_276_ = lean_ctor_get(v___x_272_, 4);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_272_, 1);
lean_dec(v_unused_288_);
v___x_278_ = v___x_272_;
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_diag_276_);
lean_inc(v_postponed_275_);
lean_inc(v_zetaDeltaFVarIds_274_);
lean_inc(v_mctx_273_);
lean_dec(v___x_272_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_mctx_273_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_zetaDeltaFVarIds_274_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_postponed_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_diag_276_);
v___x_282_ = v_reuseFailAlloc_286_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_st_ref_set(v_a_253_, v___x_282_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
v___jp_289_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(0);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
v___jp_294_:
{
if (lean_obj_tag(v___y_295_) == 0)
{
lean_object* v_a_296_; uint8_t v___x_297_; 
v_a_296_ = lean_ctor_get(v___y_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___y_295_);
v___x_297_ = lean_unbox(v_a_296_);
lean_dec(v_a_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v_env_299_; lean_object* v_nextMacroScope_300_; lean_object* v_ngen_301_; lean_object* v_auxDeclNGen_302_; lean_object* v_traceState_303_; lean_object* v_messages_304_; lean_object* v_infoState_305_; lean_object* v_snapshotTasks_306_; uint8_t v___x_307_; 
v___x_298_ = lean_st_ref_take(v_a_255_);
v_env_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc_ref(v_env_299_);
v_nextMacroScope_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc(v_nextMacroScope_300_);
v_ngen_301_ = lean_ctor_get(v___x_298_, 2);
lean_inc_ref(v_ngen_301_);
v_auxDeclNGen_302_ = lean_ctor_get(v___x_298_, 3);
lean_inc_ref(v_auxDeclNGen_302_);
v_traceState_303_ = lean_ctor_get(v___x_298_, 4);
lean_inc_ref(v_traceState_303_);
v_messages_304_ = lean_ctor_get(v___x_298_, 6);
lean_inc_ref(v_messages_304_);
v_infoState_305_ = lean_ctor_get(v___x_298_, 7);
lean_inc_ref(v_infoState_305_);
v_snapshotTasks_306_ = lean_ctor_get(v___x_298_, 8);
lean_inc_ref(v_snapshotTasks_306_);
lean_dec(v___x_298_);
v___x_307_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_307_ == 0)
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v_env_299_;
goto v___jp_260_;
}
else
{
size_t v_sz_308_; size_t v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_sz_308_ = lean_array_size(v_preDefs_248_);
v___x_309_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_248_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_308_, v___x_309_, v_preDefs_248_);
v___x_311_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_311_ == 0)
{
if (v___x_307_ == 0)
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v_env_299_;
goto v___jp_260_;
}
else
{
size_t v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_usize_of_nat(v___x_293_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_310_, v_declNameNonRec_249_, v_fixedParamPerms_250_, v_fixpointType_251_, v_preDefs_248_, v___x_309_, v___x_312_, v_env_299_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v___x_313_;
goto v___jp_260_;
}
}
else
{
size_t v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_usize_of_nat(v___x_293_);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_310_, v_declNameNonRec_249_, v_fixedParamPerms_250_, v_fixpointType_251_, v_preDefs_248_, v___x_309_, v___x_314_, v_env_299_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v___x_315_;
goto v___jp_260_;
}
}
}
else
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_257_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
v_a_316_ = lean_ctor_get(v___y_295_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___y_295_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___y_295_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___y_295_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
v___jp_324_:
{
uint8_t v___x_325_; 
v___x_325_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_325_ == 0)
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_289_;
}
else
{
if (v___x_325_ == 0)
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_289_;
}
else
{
size_t v___x_326_; size_t v___x_327_; uint8_t v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_293_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_248_, v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_289_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 0;
if (v___x_325_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_328_, v___x_329_, v___x_329_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
v___y_295_ = v___x_330_;
goto v___jp_294_;
}
else
{
if (v___x_325_ == 0)
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_257_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_328_, v_preDefs_248_, v___x_326_, v___x_327_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = lean_unbox(v_a_332_);
lean_dec(v_a_332_);
v___x_334_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_328_, v___x_329_, v___x_333_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
v___y_295_ = v___x_334_;
goto v___jp_294_;
}
else
{
v___y_295_ = v___x_331_;
goto v___jp_294_;
}
}
}
}
}
}
}
v___jp_335_:
{
if (lean_obj_tag(v___y_336_) == 0)
{
lean_dec_ref(v___y_336_);
goto v___jp_324_;
}
else
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
return v___y_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_346_, lean_object* v_declNameNonRec_347_, lean_object* v_fixedParamPerms_348_, lean_object* v_fixpointType_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_346_, v_declNameNonRec_347_, v_fixedParamPerms_348_, v_fixpointType_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_356_, size_t v_i_357_, size_t v_stop_358_, lean_object* v_b_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_356_, v_i_357_, v_stop_358_, v_b_359_, v___y_362_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_stop_368_, lean_object* v_b_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_368_);
lean_dec(v_stop_368_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_366_, v_i_boxed_375_, v_stop_boxed_376_, v_b_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec_ref(v_as_366_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_378_, lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_378_, v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_a_394_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_385_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_385_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_402_, v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_410_, lean_object* v_mvarId_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_419_, lean_object* v_mvarId_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_419_, v_mvarId_420_, v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_428_, lean_object* v_declNameNonRec_429_, lean_object* v_n_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_name_eq(v_n_430_, v_declName_428_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = lean_name_eq(v_n_430_, v_declNameNonRec_429_);
return v___x_432_;
}
else
{
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_433_, lean_object* v_declNameNonRec_434_, lean_object* v_n_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_433_, v_declNameNonRec_434_, v_n_435_);
lean_dec(v_n_435_);
lean_dec(v_declNameNonRec_434_);
lean_dec(v_declName_433_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_448_ = l_Lean_MessageData_ofFormat(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_451_, lean_object* v___f_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
lean_inc(v_mvarId_451_);
v___x_458_ = l_Lean_MVarId_getType_x27(v_mvarId_451_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_458_);
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_461_ = lean_unsigned_to_nat(3u);
v___x_462_ = l_Lean_Expr_isAppOfArity(v_a_459_, v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v_a_459_);
lean_dec_ref(v___f_452_);
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_464_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_465_ = l_Lean_Meta_throwTacticEx___redArg(v___x_463_, v_mvarId_451_, v___x_464_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_465_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; 
v___x_466_ = l_Lean_Expr_appFn_x21(v_a_459_);
v___x_467_ = l_Lean_Expr_appArg_x21(v___x_466_);
lean_dec_ref(v___x_466_);
v___x_468_ = 0;
v___x_469_ = l_Lean_Meta_deltaExpand(v___x_467_, v___f_452_, v___x_468_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
v___x_471_ = l_Lean_Expr_appArg_x21(v_a_459_);
lean_dec(v_a_459_);
v___x_472_ = l_Lean_Meta_mkEq(v_a_470_, v___x_471_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
v___x_474_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_451_, v_a_473_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_474_;
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_mvarId_451_);
v_a_475_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_472_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_472_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_a_459_);
lean_dec(v_mvarId_451_);
v_a_483_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_469_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_469_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v___f_452_);
lean_dec(v_mvarId_451_);
v_a_491_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_458_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_458_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_499_, lean_object* v___f_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_499_, v___f_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_507_, lean_object* v_declNameNonRec_508_, lean_object* v_mvarId_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v___f_515_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_515_, 0, v_declName_507_);
lean_closure_set(v___f_515_, 1, v_declNameNonRec_508_);
lean_inc(v_mvarId_509_);
v___f_516_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_516_, 0, v_mvarId_509_);
lean_closure_set(v___f_516_, 1, v___f_515_);
v___x_517_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_509_, v___f_516_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_518_, lean_object* v_declNameNonRec_519_, lean_object* v_mvarId_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_518_, v_declNameNonRec_519_, v_mvarId_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(lean_object* v_msg_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = l_Lean_instInhabitedExpr;
v___x_529_ = lean_panic_fn(v___x_528_, v_msg_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(lean_object* v_msgData_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; lean_object* v_env_537_; lean_object* v___x_538_; lean_object* v_mctx_539_; lean_object* v_lctx_540_; lean_object* v_options_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_536_ = lean_st_ref_get(v___y_534_);
v_env_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc_ref(v_env_537_);
lean_dec(v___x_536_);
v___x_538_ = lean_st_ref_get(v___y_532_);
v_mctx_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_ref(v_mctx_539_);
lean_dec(v___x_538_);
v_lctx_540_ = lean_ctor_get(v___y_531_, 2);
v_options_541_ = lean_ctor_get(v___y_533_, 2);
lean_inc_ref(v_options_541_);
lean_inc_ref(v_lctx_540_);
v___x_542_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_542_, 0, v_env_537_);
lean_ctor_set(v___x_542_, 1, v_mctx_539_);
lean_ctor_set(v___x_542_, 2, v_lctx_540_);
lean_ctor_set(v___x_542_, 3, v_options_541_);
v___x_543_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_msgData_530_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(lean_object* v_msgData_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msgData_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_ref_558_; lean_object* v___x_559_; lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_568_; 
v_ref_558_ = lean_ctor_get(v___y_555_, 5);
v___x_559_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_568_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
lean_inc(v_ref_558_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_ref_558_);
lean_ctor_set(v___x_564_, 1, v_a_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 1);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg___boxed(lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_575_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = l_Lean_Expr_bvar___override(v___x_596_);
return v___x_597_;
}
}
static size_t _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12(void){
_start:
{
lean_object* v___x_598_; size_t v___x_599_; 
v___x_598_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_599_ = lean_ptr_addr(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15));
v___x_604_ = lean_unsigned_to_nat(18u);
v___x_605_ = lean_unsigned_to_nat(1872u);
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14));
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13));
v___x_608_ = l_mkPanicMessageWithDecl(v___x_607_, v___x_606_, v___x_605_, v___x_604_, v___x_603_);
return v___x_608_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21(void){
_start:
{
lean_object* v___x_617_; lean_object* v_dummy_618_; 
v___x_617_ = lean_box(0);
v_dummy_618_ = l_Lean_Expr_sort___override(v___x_617_);
return v_dummy_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2));
v___x_631_ = lean_unsigned_to_nat(4u);
v___x_632_ = l_Lean_Expr_isAppOfArity(v_lhs_624_, v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4));
v___x_634_ = l_Lean_Expr_isAppOfArity(v_lhs_624_, v___x_633_, v___x_631_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; 
v___x_635_ = l_Lean_Expr_isApp(v_lhs_624_);
if (v___x_635_ == 0)
{
uint8_t v___x_636_; 
v___x_636_ = l_Lean_Expr_isProj(v_lhs_624_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_638_ = l_Lean_MessageData_ofExpr(v_lhs_624_);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_639_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = l_Lean_Expr_projExpr_x21(v_lhs_624_);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
lean_inc_ref(v___x_641_);
v___x_642_ = lean_infer_type(v___x_641_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v___x_642_);
v___x_644_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_641_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___y_649_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v___x_644_);
v___x_646_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_647_ = 0;
if (lean_obj_tag(v_lhs_624_) == 11)
{
lean_object* v_typeName_657_; lean_object* v_idx_658_; lean_object* v_struct_659_; lean_object* v___x_660_; size_t v___x_661_; size_t v___x_662_; uint8_t v___x_663_; 
v_typeName_657_ = lean_ctor_get(v_lhs_624_, 0);
v_idx_658_ = lean_ctor_get(v_lhs_624_, 1);
v_struct_659_ = lean_ctor_get(v_lhs_624_, 2);
v___x_660_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_661_ = lean_ptr_addr(v_struct_659_);
v___x_662_ = lean_usize_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12);
v___x_663_ = lean_usize_dec_eq(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_inc(v_idx_658_);
lean_inc(v_typeName_657_);
lean_dec_ref(v_lhs_624_);
v___x_664_ = l_Lean_Expr_proj___override(v_typeName_657_, v_idx_658_, v___x_660_);
v___y_649_ = v___x_664_;
goto v___jp_648_;
}
else
{
v___y_649_ = v_lhs_624_;
goto v___jp_648_;
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref(v_lhs_624_);
v___x_665_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
v___x_666_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(v___x_665_);
v___y_649_ = v___x_666_;
goto v___jp_648_;
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_650_ = l_Lean_mkLambda(v___x_646_, v___x_647_, v_a_643_, v___y_649_);
v___x_651_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10));
v___x_652_ = lean_unsigned_to_nat(2u);
v___x_653_ = lean_mk_empty_array_with_capacity(v___x_652_);
v___x_654_ = lean_array_push(v___x_653_, v___x_650_);
v___x_655_ = lean_array_push(v___x_654_, v_a_645_);
v___x_656_ = l_Lean_Meta_mkAppM(v___x_651_, v___x_655_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_656_;
}
}
else
{
lean_dec(v_a_643_);
lean_dec_ref(v_lhs_624_);
return v___x_644_;
}
}
else
{
lean_dec_ref(v___x_641_);
lean_dec_ref(v_lhs_624_);
return v___x_642_;
}
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = l_Lean_Expr_appFn_x21(v_lhs_624_);
v___x_668_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_667_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref(v___x_668_);
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18));
v___x_671_ = l_Lean_Expr_appArg_x21(v_lhs_624_);
lean_dec_ref(v_lhs_624_);
v___x_672_ = lean_unsigned_to_nat(2u);
v___x_673_ = lean_mk_empty_array_with_capacity(v___x_672_);
v___x_674_ = lean_array_push(v___x_673_, v_a_669_);
v___x_675_ = lean_array_push(v___x_674_, v___x_671_);
v___x_676_ = l_Lean_Meta_mkAppM(v___x_670_, v___x_675_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_676_;
}
else
{
lean_dec_ref(v_lhs_624_);
return v___x_668_;
}
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_dummy_681_; lean_object* v_nargs_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20));
v___x_678_ = l_Lean_Expr_getAppFn(v_lhs_624_);
v___x_679_ = l_Lean_Expr_constLevels_x21(v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = l_Lean_mkConst(v___x_677_, v___x_679_);
v_dummy_681_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_682_ = l_Lean_Expr_getAppNumArgs(v_lhs_624_);
lean_inc(v_nargs_682_);
v___x_683_ = lean_mk_array(v_nargs_682_, v_dummy_681_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_sub(v_nargs_682_, v___x_684_);
lean_dec(v_nargs_682_);
v___x_686_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_624_, v___x_683_, v___x_685_);
v___x_687_ = l_Lean_mkAppN(v___x_680_, v___x_686_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_dummy_693_; lean_object* v_nargs_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23));
v___x_690_ = l_Lean_Expr_getAppFn(v_lhs_624_);
v___x_691_ = l_Lean_Expr_constLevels_x21(v___x_690_);
lean_dec_ref(v___x_690_);
v___x_692_ = l_Lean_mkConst(v___x_689_, v___x_691_);
v_dummy_693_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_694_ = l_Lean_Expr_getAppNumArgs(v_lhs_624_);
lean_inc(v_nargs_694_);
v___x_695_ = lean_mk_array(v_nargs_694_, v_dummy_693_);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_sub(v_nargs_694_, v___x_696_);
lean_dec(v_nargs_694_);
v___x_698_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_624_, v___x_695_, v___x_697_);
v___x_699_ = l_Lean_mkAppN(v___x_692_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_00_u03b1_708_, lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(lean_object* v_00_u03b1_716_, lean_object* v_msg_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v_00_u03b1_716_, v_msg_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___f_731_; lean_object* v___x_1534__overap_732_; lean_object* v___x_733_; 
v___f_731_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1534__overap_732_ = lean_panic_fn(v___f_731_, v_msg_725_);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
v___x_733_ = lean_apply_5(v___x_1534__overap_732_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, lean_box(0));
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_ks_745_; lean_object* v_vs_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_770_; 
v_ks_745_ = lean_ctor_get(v_x_741_, 0);
v_vs_746_ = lean_ctor_get(v_x_741_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_770_ == 0)
{
v___x_748_ = v_x_741_;
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_vs_746_);
lean_inc(v_ks_745_);
lean_dec(v_x_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_array_get_size(v_ks_745_);
v___x_751_ = lean_nat_dec_lt(v_x_742_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_x_742_);
v___x_752_ = lean_array_push(v_ks_745_, v_x_743_);
v___x_753_ = lean_array_push(v_vs_746_, v_x_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_753_);
lean_ctor_set(v___x_748_, 0, v___x_752_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v_k_x27_757_; uint8_t v___x_758_; 
v_k_x27_757_ = lean_array_fget_borrowed(v_ks_745_, v_x_742_);
v___x_758_ = l_Lean_instBEqMVarId_beq(v_x_743_, v_k_x27_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_760_; 
if (v_isShared_749_ == 0)
{
v___x_760_ = v___x_748_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_ks_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_vs_746_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_x_742_, v___x_761_);
lean_dec(v_x_742_);
v_x_741_ = v___x_760_;
v_x_742_ = v___x_762_;
goto _start;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = lean_array_fset(v_ks_745_, v_x_742_, v_x_743_);
v___x_766_ = lean_array_fset(v_vs_746_, v_x_742_, v_x_744_);
lean_dec(v_x_742_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_766_);
lean_ctor_set(v___x_748_, 0, v___x_765_);
v___x_768_ = v___x_748_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_771_, lean_object* v_k_772_, lean_object* v_v_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_771_, v___x_774_, v_k_772_, v_v_773_);
return v___x_775_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; 
v___x_776_ = ((size_t)5ULL);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_shift_left(v___x_777_, v___x_776_);
return v___x_778_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; 
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_781_ = lean_usize_sub(v___x_780_, v___x_779_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_783_, size_t v_x_784_, size_t v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v_es_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; lean_object* v_j_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_es_788_ = lean_ctor_get(v_x_783_, 0);
v___x_789_ = ((size_t)5ULL);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_792_ = lean_usize_land(v_x_784_, v___x_791_);
v_j_793_ = lean_usize_to_nat(v___x_792_);
v___x_794_ = lean_array_get_size(v_es_788_);
v___x_795_ = lean_nat_dec_lt(v_j_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec(v_j_793_);
lean_dec(v_x_787_);
lean_dec(v_x_786_);
return v_x_783_;
}
else
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_832_; 
lean_inc_ref(v_es_788_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_x_783_, 0);
lean_dec(v_unused_833_);
v___x_797_ = v_x_783_;
v_isShared_798_ = v_isSharedCheck_832_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_x_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_832_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_v_799_; lean_object* v___x_800_; lean_object* v_xs_x27_801_; lean_object* v___y_803_; 
v_v_799_ = lean_array_fget(v_es_788_, v_j_793_);
v___x_800_ = lean_box(0);
v_xs_x27_801_ = lean_array_fset(v_es_788_, v_j_793_, v___x_800_);
switch(lean_obj_tag(v_v_799_))
{
case 0:
{
lean_object* v_key_808_; lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_key_808_ = lean_ctor_get(v_v_799_, 0);
v_val_809_ = lean_ctor_get(v_v_799_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_v_799_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v_v_799_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_inc(v_key_808_);
lean_dec(v_v_799_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint8_t v___x_813_; 
v___x_813_ = l_Lean_instBEqMVarId_beq(v_x_786_, v_key_808_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_del_object(v___x_811_);
v___x_814_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_808_, v_val_809_, v_x_786_, v_x_787_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___y_803_ = v___x_815_;
goto v___jp_802_;
}
else
{
lean_object* v___x_817_; 
lean_dec(v_val_809_);
lean_dec(v_key_808_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v_x_787_);
lean_ctor_set(v___x_811_, 0, v_x_786_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_x_786_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_x_787_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_803_ = v___x_817_;
goto v___jp_802_;
}
}
}
}
case 1:
{
lean_object* v_node_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_830_; 
v_node_820_ = lean_ctor_get(v_v_799_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_v_799_);
if (v_isSharedCheck_830_ == 0)
{
v___x_822_ = v_v_799_;
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_node_820_);
lean_dec(v_v_799_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_824_ = lean_usize_shift_right(v_x_784_, v___x_789_);
v___x_825_ = lean_usize_add(v_x_785_, v___x_790_);
v___x_826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_820_, v___x_824_, v___x_825_, v_x_786_, v_x_787_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_826_);
v___x_828_ = v___x_822_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v___y_803_ = v___x_828_;
goto v___jp_802_;
}
}
}
default: 
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_x_786_);
lean_ctor_set(v___x_831_, 1, v_x_787_);
v___y_803_ = v___x_831_;
goto v___jp_802_;
}
}
v___jp_802_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_array_fset(v_xs_x27_801_, v_j_793_, v___y_803_);
lean_dec(v_j_793_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_804_);
v___x_806_ = v___x_797_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
else
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_855_; 
v_ks_834_ = lean_ctor_get(v_x_783_, 0);
v_vs_835_ = lean_ctor_get(v_x_783_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_855_ == 0)
{
v___x_837_ = v_x_783_;
v_isShared_838_ = v_isSharedCheck_855_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_vs_835_);
lean_inc(v_ks_834_);
lean_dec(v_x_783_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_855_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_ks_834_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_vs_835_);
v___x_840_ = v_reuseFailAlloc_854_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v_newNode_841_; uint8_t v___y_843_; size_t v___x_849_; uint8_t v___x_850_; 
v_newNode_841_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_840_, v_x_786_, v_x_787_);
v___x_849_ = ((size_t)7ULL);
v___x_850_ = lean_usize_dec_le(v___x_849_, v_x_785_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_851_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_841_);
v___x_852_ = lean_unsigned_to_nat(4u);
v___x_853_ = lean_nat_dec_lt(v___x_851_, v___x_852_);
lean_dec(v___x_851_);
v___y_843_ = v___x_853_;
goto v___jp_842_;
}
else
{
v___y_843_ = v___x_850_;
goto v___jp_842_;
}
v___jp_842_:
{
if (v___y_843_ == 0)
{
lean_object* v_ks_844_; lean_object* v_vs_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_ks_844_ = lean_ctor_get(v_newNode_841_, 0);
lean_inc_ref(v_ks_844_);
v_vs_845_ = lean_ctor_get(v_newNode_841_, 1);
lean_inc_ref(v_vs_845_);
lean_dec_ref(v_newNode_841_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_848_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_785_, v_ks_844_, v_vs_845_, v___x_846_, v___x_847_);
lean_dec_ref(v_vs_845_);
lean_dec_ref(v_ks_844_);
return v___x_848_;
}
else
{
return v_newNode_841_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_856_, lean_object* v_keys_857_, lean_object* v_vals_858_, lean_object* v_i_859_, lean_object* v_entries_860_){
_start:
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = lean_array_get_size(v_keys_857_);
v___x_862_ = lean_nat_dec_lt(v_i_859_, v___x_861_);
if (v___x_862_ == 0)
{
lean_dec(v_i_859_);
return v_entries_860_;
}
else
{
lean_object* v_k_863_; lean_object* v_v_864_; uint64_t v___x_865_; size_t v_h_866_; size_t v___x_867_; lean_object* v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v_h_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_k_863_ = lean_array_fget_borrowed(v_keys_857_, v_i_859_);
v_v_864_ = lean_array_fget_borrowed(v_vals_858_, v_i_859_);
v___x_865_ = l_Lean_instHashableMVarId_hash(v_k_863_);
v_h_866_ = lean_uint64_to_usize(v___x_865_);
v___x_867_ = ((size_t)5ULL);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_sub(v_depth_856_, v___x_869_);
v___x_871_ = lean_usize_mul(v___x_867_, v___x_870_);
v_h_872_ = lean_usize_shift_right(v_h_866_, v___x_871_);
v___x_873_ = lean_nat_add(v_i_859_, v___x_868_);
lean_dec(v_i_859_);
lean_inc(v_v_864_);
lean_inc(v_k_863_);
v___x_874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_860_, v_h_872_, v_depth_856_, v_k_863_, v_v_864_);
v_i_859_ = v___x_873_;
v_entries_860_ = v___x_874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_876_, lean_object* v_keys_877_, lean_object* v_vals_878_, lean_object* v_i_879_, lean_object* v_entries_880_){
_start:
{
size_t v_depth_boxed_881_; lean_object* v_res_882_; 
v_depth_boxed_881_ = lean_unbox_usize(v_depth_876_);
lean_dec(v_depth_876_);
v_res_882_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_881_, v_keys_877_, v_vals_878_, v_i_879_, v_entries_880_);
lean_dec_ref(v_vals_878_);
lean_dec_ref(v_keys_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
size_t v_x_2119__boxed_888_; size_t v_x_2120__boxed_889_; lean_object* v_res_890_; 
v_x_2119__boxed_888_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_x_2120__boxed_889_ = lean_unbox_usize(v_x_885_);
lean_dec(v_x_885_);
v_res_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_883_, v_x_2119__boxed_888_, v_x_2120__boxed_889_, v_x_886_, v_x_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
uint64_t v___x_894_; size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_894_ = l_Lean_instHashableMVarId_hash(v_x_892_);
v___x_895_ = lean_uint64_to_usize(v___x_894_);
v___x_896_ = ((size_t)1ULL);
v___x_897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_891_, v___x_895_, v___x_896_, v_x_892_, v_x_893_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_898_, lean_object* v_val_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; lean_object* v_mctx_903_; lean_object* v_cache_904_; lean_object* v_zetaDeltaFVarIds_905_; lean_object* v_postponed_906_; lean_object* v_diag_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_934_; 
v___x_902_ = lean_st_ref_take(v___y_900_);
v_mctx_903_ = lean_ctor_get(v___x_902_, 0);
v_cache_904_ = lean_ctor_get(v___x_902_, 1);
v_zetaDeltaFVarIds_905_ = lean_ctor_get(v___x_902_, 2);
v_postponed_906_ = lean_ctor_get(v___x_902_, 3);
v_diag_907_ = lean_ctor_get(v___x_902_, 4);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_934_ == 0)
{
v___x_909_ = v___x_902_;
v_isShared_910_ = v_isSharedCheck_934_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_diag_907_);
lean_inc(v_postponed_906_);
lean_inc(v_zetaDeltaFVarIds_905_);
lean_inc(v_cache_904_);
lean_inc(v_mctx_903_);
lean_dec(v___x_902_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_934_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_depth_911_; lean_object* v_levelAssignDepth_912_; lean_object* v_mvarCounter_913_; lean_object* v_lDepth_914_; lean_object* v_decls_915_; lean_object* v_userNames_916_; lean_object* v_lAssignment_917_; lean_object* v_eAssignment_918_; lean_object* v_dAssignment_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_933_; 
v_depth_911_ = lean_ctor_get(v_mctx_903_, 0);
v_levelAssignDepth_912_ = lean_ctor_get(v_mctx_903_, 1);
v_mvarCounter_913_ = lean_ctor_get(v_mctx_903_, 2);
v_lDepth_914_ = lean_ctor_get(v_mctx_903_, 3);
v_decls_915_ = lean_ctor_get(v_mctx_903_, 4);
v_userNames_916_ = lean_ctor_get(v_mctx_903_, 5);
v_lAssignment_917_ = lean_ctor_get(v_mctx_903_, 6);
v_eAssignment_918_ = lean_ctor_get(v_mctx_903_, 7);
v_dAssignment_919_ = lean_ctor_get(v_mctx_903_, 8);
v_isSharedCheck_933_ = !lean_is_exclusive(v_mctx_903_);
if (v_isSharedCheck_933_ == 0)
{
v___x_921_ = v_mctx_903_;
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_dAssignment_919_);
lean_inc(v_eAssignment_918_);
lean_inc(v_lAssignment_917_);
lean_inc(v_userNames_916_);
lean_inc(v_decls_915_);
lean_inc(v_lDepth_914_);
lean_inc(v_mvarCounter_913_);
lean_inc(v_levelAssignDepth_912_);
lean_inc(v_depth_911_);
lean_dec(v_mctx_903_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_918_, v_mvarId_898_, v_val_899_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 7, v___x_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_depth_911_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_levelAssignDepth_912_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_mvarCounter_913_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_lDepth_914_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_decls_915_);
lean_ctor_set(v_reuseFailAlloc_932_, 5, v_userNames_916_);
lean_ctor_set(v_reuseFailAlloc_932_, 6, v_lAssignment_917_);
lean_ctor_set(v_reuseFailAlloc_932_, 7, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_932_, 8, v_dAssignment_919_);
v___x_925_ = v_reuseFailAlloc_932_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_925_);
v___x_927_ = v___x_909_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_cache_904_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_zetaDeltaFVarIds_905_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_postponed_906_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_diag_907_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_st_ref_set(v___y_900_, v___x_927_);
v___x_929_ = lean_box(0);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_935_, lean_object* v_val_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_935_, v_val_936_, v___y_937_);
lean_dec(v___y_937_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_943_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_944_ = lean_unsigned_to_nat(41u);
v___x_945_ = lean_unsigned_to_nat(68u);
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_947_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_948_ = l_mkPanicMessageWithDecl(v___x_947_, v___x_946_, v___x_945_, v___x_944_, v___x_943_);
return v___x_948_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_950_ = lean_unsigned_to_nat(51u);
v___x_951_ = lean_unsigned_to_nat(70u);
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_953_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_954_ = l_mkPanicMessageWithDecl(v___x_953_, v___x_952_, v___x_951_, v___x_950_, v___x_949_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
lean_inc(v_mvarId_955_);
v___x_961_ = l_Lean_MVarId_getType_x27(v_mvarId_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_964_ = lean_unsigned_to_nat(3u);
v___x_965_ = l_Lean_Expr_isAppOfArity(v_a_962_, v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v_a_962_);
lean_dec(v_mvarId_955_);
v___x_966_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_967_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_966_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = l_Lean_Expr_appFn_x21(v_a_962_);
v___x_969_ = l_Lean_Expr_appArg_x21(v___x_968_);
lean_dec_ref(v___x_968_);
v___x_970_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_969_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_970_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v_a_971_);
v___x_972_ = lean_infer_type(v_a_971_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; uint8_t v___x_974_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = l_Lean_Expr_isAppOfArity(v_a_973_, v___x_963_, v___x_964_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v_a_973_);
lean_dec(v_a_971_);
lean_dec(v_a_962_);
lean_dec(v_mvarId_955_);
v___x_975_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
v___x_976_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_975_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_Expr_appArg_x21(v_a_962_);
lean_dec(v_a_962_);
v___x_978_ = l_Lean_Expr_appArg_x21(v_a_973_);
lean_dec(v_a_973_);
v___x_979_ = l_Lean_Meta_mkEq(v___x_978_, v___x_977_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_box(0);
v___x_982_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_980_, v___x_981_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_982_);
lean_inc(v_a_983_);
v___x_984_ = l_Lean_Meta_mkEqTrans(v_a_971_, v_a_983_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec_ref(v___y_956_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_955_, v_a_985_, v___y_957_);
lean_dec(v___y_957_);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_986_, 0);
lean_dec(v_unused_995_);
v___x_988_ = v___x_986_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_dec(v___x_986_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = l_Lean_Expr_mvarId_x21(v_a_983_);
lean_dec(v_a_983_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_983_);
lean_dec(v___y_957_);
lean_dec(v_mvarId_955_);
v_a_996_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_984_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_984_);
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
lean_dec(v_a_971_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v_mvarId_955_);
v_a_1004_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_982_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_982_);
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
lean_dec(v_a_971_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v_mvarId_955_);
v_a_1012_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_979_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_979_);
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
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_a_971_);
lean_dec(v_a_962_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v_mvarId_955_);
v_a_1020_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_972_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_972_);
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
lean_dec(v_a_962_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v_mvarId_955_);
v_a_1028_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_970_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_970_);
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
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v_mvarId_955_);
v_a_1036_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_961_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_961_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; 
lean_inc(v_mvarId_1051_);
v___f_1057_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1057_, 0, v_mvarId_1051_);
v___x_1058_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1051_, v___f_1057_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1066_, lean_object* v_val_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1066_, v_val_1067_, v___y_1069_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1074_, lean_object* v_val_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1074_, v_val_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1083_, v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, size_t v_x_1089_, size_t v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1088_, v_x_1089_, v_x_1090_, v_x_1091_, v_x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
size_t v_x_2605__boxed_1100_; size_t v_x_2606__boxed_1101_; lean_object* v_res_1102_; 
v_x_2605__boxed_1100_ = lean_unbox_usize(v_x_1096_);
lean_dec(v_x_1096_);
v_x_2606__boxed_1101_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_res_1102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1094_, v_x_1095_, v_x_2605__boxed_1100_, v_x_2606__boxed_1101_, v_x_1098_, v_x_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1103_, lean_object* v_n_1104_, lean_object* v_k_1105_, lean_object* v_v_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1104_, v_k_1105_, v_v_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1108_, size_t v_depth_1109_, lean_object* v_keys_1110_, lean_object* v_vals_1111_, lean_object* v_heq_1112_, lean_object* v_i_1113_, lean_object* v_entries_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1109_, v_keys_1110_, v_vals_1111_, v_i_1113_, v_entries_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1116_, lean_object* v_depth_1117_, lean_object* v_keys_1118_, lean_object* v_vals_1119_, lean_object* v_heq_1120_, lean_object* v_i_1121_, lean_object* v_entries_1122_){
_start:
{
size_t v_depth_boxed_1123_; lean_object* v_res_1124_; 
v_depth_boxed_1123_ = lean_unbox_usize(v_depth_1117_);
lean_dec(v_depth_1117_);
v_res_1124_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1116_, v_depth_boxed_1123_, v_keys_1118_, v_vals_1119_, v_heq_1120_, v_i_1121_, v_entries_1122_);
lean_dec_ref(v_vals_1119_);
lean_dec_ref(v_keys_1118_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1126_, v_x_1127_, v_x_1128_, v_x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_cls_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_options_1137_; uint8_t v_hasTrace_1138_; 
v_options_1137_ = lean_ctor_get(v___y_1135_, 2);
v_hasTrace_1138_ = lean_ctor_get_uint8(v_options_1137_, sizeof(void*)*1);
if (v_hasTrace_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v_cls_1134_);
v___x_1139_ = lean_box(v_hasTrace_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v_inheritedTraceOptions_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_inheritedTraceOptions_1141_ = lean_ctor_get(v___y_1135_, 13);
v___x_1142_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1));
v___x_1143_ = l_Lean_Name_append(v___x_1142_, v_cls_1134_);
v___x_1144_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1141_, v_options_1137_, v___x_1143_);
lean_dec(v___x_1143_);
v___x_1145_ = lean_box(v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_cls_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v_cls_1147_, v___y_1148_);
lean_dec_ref(v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_cls_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v_cls_1151_, v___y_1154_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_cls_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_cls_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_1165_, lean_object* v_opt_1166_){
_start:
{
lean_object* v_name_1167_; lean_object* v_defValue_1168_; lean_object* v_map_1169_; lean_object* v___x_1170_; 
v_name_1167_ = lean_ctor_get(v_opt_1166_, 0);
v_defValue_1168_ = lean_ctor_get(v_opt_1166_, 1);
v_map_1169_ = lean_ctor_get(v_opts_1165_, 0);
v___x_1170_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1169_, v_name_1167_);
if (lean_obj_tag(v___x_1170_) == 0)
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_unbox(v_defValue_1168_);
return v___x_1171_;
}
else
{
lean_object* v_val_1172_; 
v_val_1172_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_val_1172_);
lean_dec_ref(v___x_1170_);
if (lean_obj_tag(v_val_1172_) == 1)
{
uint8_t v_v_1173_; 
v_v_1173_ = lean_ctor_get_uint8(v_val_1172_, 0);
lean_dec_ref(v_val_1172_);
return v_v_1173_;
}
else
{
uint8_t v___x_1174_; 
lean_dec(v_val_1172_);
v___x_1174_ = lean_unbox(v_defValue_1168_);
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_1175_, lean_object* v_opt_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_1175_, v_opt_1176_);
lean_dec_ref(v_opt_1176_);
lean_dec_ref(v_opts_1175_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_opts_1179_, lean_object* v_opt_1180_){
_start:
{
lean_object* v_name_1181_; lean_object* v_defValue_1182_; lean_object* v_map_1183_; lean_object* v___x_1184_; 
v_name_1181_ = lean_ctor_get(v_opt_1180_, 0);
v_defValue_1182_ = lean_ctor_get(v_opt_1180_, 1);
v_map_1183_ = lean_ctor_get(v_opts_1179_, 0);
v___x_1184_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1183_, v_name_1181_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_inc(v_defValue_1182_);
return v_defValue_1182_;
}
else
{
lean_object* v_val_1185_; 
v_val_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref(v___x_1184_);
if (lean_obj_tag(v_val_1185_) == 3)
{
lean_object* v_v_1186_; 
v_v_1186_ = lean_ctor_get(v_val_1185_, 0);
lean_inc(v_v_1186_);
lean_dec_ref(v_val_1185_);
return v_v_1186_;
}
else
{
lean_dec(v_val_1185_);
lean_inc(v_defValue_1182_);
return v_defValue_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_opts_1187_, lean_object* v_opt_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_opts_1187_, v_opt_1188_);
lean_dec_ref(v_opt_1188_);
lean_dec_ref(v_opts_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(lean_object* v_e_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = l_Lean_Expr_hasMVar(v_e_1190_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_e_1190_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v_mctx_1196_; lean_object* v___x_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v_cache_1201_; lean_object* v_zetaDeltaFVarIds_1202_; lean_object* v_postponed_1203_; lean_object* v_diag_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1213_; 
v___x_1195_ = lean_st_ref_get(v___y_1191_);
v_mctx_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_mctx_1196_);
lean_dec(v___x_1195_);
v___x_1197_ = l_Lean_instantiateMVarsCore(v_mctx_1196_, v_e_1190_);
v_fst_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_snd_1199_);
lean_dec_ref(v___x_1197_);
v___x_1200_ = lean_st_ref_take(v___y_1191_);
v_cache_1201_ = lean_ctor_get(v___x_1200_, 1);
v_zetaDeltaFVarIds_1202_ = lean_ctor_get(v___x_1200_, 2);
v_postponed_1203_ = lean_ctor_get(v___x_1200_, 3);
v_diag_1204_ = lean_ctor_get(v___x_1200_, 4);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1200_, 0);
lean_dec(v_unused_1214_);
v___x_1206_ = v___x_1200_;
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_diag_1204_);
lean_inc(v_postponed_1203_);
lean_inc(v_zetaDeltaFVarIds_1202_);
lean_inc(v_cache_1201_);
lean_dec(v___x_1200_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v_snd_1199_);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_snd_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_cache_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_zetaDeltaFVarIds_1202_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_postponed_1203_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_diag_1204_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_st_ref_set(v___y_1191_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_fst_1198_);
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg___boxed(lean_object* v_e_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_e_1215_, v___y_1216_);
lean_dec(v___y_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object* v_e_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_e_1219_, v___y_1221_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object* v_e_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v_e_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object* v_k_1233_, uint8_t v_allowLevelAssignments_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1234_, v_k_1233_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_a_1249_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1240_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1240_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object* v_k_1257_, lean_object* v_allowLevelAssignments_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1264_; lean_object* v_res_1265_; 
v_allowLevelAssignments_boxed_1264_ = lean_unbox(v_allowLevelAssignments_1258_);
v_res_1265_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_k_1257_, v_allowLevelAssignments_boxed_1264_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object* v_00_u03b1_1266_, lean_object* v_k_1267_, uint8_t v_allowLevelAssignments_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_k_1267_, v_allowLevelAssignments_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_k_1276_, lean_object* v_allowLevelAssignments_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1283_; lean_object* v_res_1284_; 
v_allowLevelAssignments_boxed_1283_ = lean_unbox(v_allowLevelAssignments_1277_);
v_res_1284_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(v_00_u03b1_1275_, v_k_1276_, v_allowLevelAssignments_boxed_1283_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object* v_thm_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v_env_1289_; lean_object* v_toConstantVal_1290_; lean_object* v_value_1291_; lean_object* v_all_1292_; uint8_t v___y_1294_; lean_object* v_type_1302_; uint8_t v___x_1303_; 
v___x_1288_ = lean_st_ref_get(v___y_1286_);
v_env_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref(v_env_1289_);
lean_dec(v___x_1288_);
v_toConstantVal_1290_ = lean_ctor_get(v_thm_1285_, 0);
v_value_1291_ = lean_ctor_get(v_thm_1285_, 1);
v_all_1292_ = lean_ctor_get(v_thm_1285_, 2);
v_type_1302_ = lean_ctor_get(v_toConstantVal_1290_, 2);
lean_inc_ref(v_env_1289_);
v___x_1303_ = l_Lean_Environment_hasUnsafe(v_env_1289_, v_type_1302_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; 
v___x_1304_ = l_Lean_Environment_hasUnsafe(v_env_1289_, v_value_1291_);
v___y_1294_ = v___x_1304_;
goto v___jp_1293_;
}
else
{
lean_dec_ref(v_env_1289_);
v___y_1294_ = v___x_1303_;
goto v___jp_1293_;
}
v___jp_1293_:
{
if (v___y_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_thm_1285_);
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc(v_all_1292_);
lean_inc_ref(v_value_1291_);
lean_inc_ref(v_toConstantVal_1290_);
lean_dec_ref(v_thm_1285_);
v___x_1297_ = lean_box(0);
v___x_1298_ = 0;
v___x_1299_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1299_, 0, v_toConstantVal_1290_);
lean_ctor_set(v___x_1299_, 1, v_value_1291_);
lean_ctor_set(v___x_1299_, 2, v___x_1297_);
lean_ctor_set(v___x_1299_, 3, v_all_1292_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*4, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object* v_thm_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_thm_1305_, v___y_1306_);
lean_dec(v___y_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object* v_thm_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_thm_1309_, v___y_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object* v_thm_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(v_thm_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0(lean_object* v_k_1323_, lean_object* v_b_1324_, lean_object* v_c_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
v___x_1331_ = lean_apply_7(v_k_1323_, v_b_1324_, v_c_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, lean_box(0));
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0___boxed(lean_object* v_k_1332_, lean_object* v_b_1333_, lean_object* v_c_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0(v_k_1332_, v_b_1333_, v_c_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(lean_object* v_e_1341_, lean_object* v_k_1342_, uint8_t v_cleanupAnnotations_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___f_1349_; uint8_t v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___f_1349_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1349_, 0, v_k_1342_);
v___x_1350_ = 1;
v___x_1351_ = 0;
v___x_1352_ = lean_box(0);
v___x_1353_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1341_, v___x_1350_, v___x_1351_, v___x_1350_, v___x_1351_, v___x_1352_, v___f_1349_, v_cleanupAnnotations_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1353_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1353_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___boxed(lean_object* v_e_1370_, lean_object* v_k_1371_, lean_object* v_cleanupAnnotations_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1378_; lean_object* v_res_1379_; 
v_cleanupAnnotations_boxed_1378_ = lean_unbox(v_cleanupAnnotations_1372_);
v_res_1379_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(v_e_1370_, v_k_1371_, v_cleanupAnnotations_boxed_1378_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9(lean_object* v_00_u03b1_1380_, lean_object* v_e_1381_, lean_object* v_k_1382_, uint8_t v_cleanupAnnotations_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(v_e_1381_, v_k_1382_, v_cleanupAnnotations_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___boxed(lean_object* v_00_u03b1_1390_, lean_object* v_e_1391_, lean_object* v_k_1392_, lean_object* v_cleanupAnnotations_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1399_; lean_object* v_res_1400_; 
v_cleanupAnnotations_boxed_1399_ = lean_unbox(v_cleanupAnnotations_1393_);
v_res_1400_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9(v_00_u03b1_1390_, v_e_1391_, v_k_1392_, v_cleanupAnnotations_boxed_1399_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(lean_object* v_o_1401_, lean_object* v_k_1402_, uint8_t v_v_1403_){
_start:
{
lean_object* v_map_1404_; uint8_t v_hasTrace_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1419_; 
v_map_1404_ = lean_ctor_get(v_o_1401_, 0);
v_hasTrace_1405_ = lean_ctor_get_uint8(v_o_1401_, sizeof(void*)*1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_o_1401_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1407_ = v_o_1401_;
v_isShared_1408_ = v_isSharedCheck_1419_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_map_1404_);
lean_dec(v_o_1401_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1419_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1409_, 0, v_v_1403_);
lean_inc(v_k_1402_);
v___x_1410_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1402_, v___x_1409_, v_map_1404_);
if (v_hasTrace_1405_ == 0)
{
lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1414_; 
v___x_1411_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1));
v___x_1412_ = l_Lean_Name_isPrefixOf(v___x_1411_, v_k_1402_);
lean_dec(v_k_1402_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1410_);
v___x_1414_ = v___x_1407_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1410_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*1, v___x_1412_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_k_1402_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1410_);
v___x_1417_ = v___x_1407_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*1, v_hasTrace_1405_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2___boxed(lean_object* v_o_1420_, lean_object* v_k_1421_, lean_object* v_v_1422_){
_start:
{
uint8_t v_v_boxed_1423_; lean_object* v_res_1424_; 
v_v_boxed_1423_ = lean_unbox(v_v_1422_);
v_res_1424_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(v_o_1420_, v_k_1421_, v_v_boxed_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_1425_, lean_object* v_opt_1426_, uint8_t v_val_1427_){
_start:
{
lean_object* v_name_1428_; lean_object* v___x_1429_; 
v_name_1428_ = lean_ctor_get(v_opt_1426_, 0);
lean_inc(v_name_1428_);
lean_dec_ref(v_opt_1426_);
v___x_1429_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(v_opts_1425_, v_name_1428_, v_val_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_1430_, lean_object* v_opt_1431_, lean_object* v_val_1432_){
_start:
{
uint8_t v_val_boxed_1433_; lean_object* v_res_1434_; 
v_val_boxed_1433_ = lean_unbox(v_val_1432_);
v_res_1434_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_1430_, v_opt_1431_, v_val_boxed_1433_);
return v_res_1434_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1435_; double v___x_1436_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_float_of_nat(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object* v_cls_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_ref_1447_; lean_object* v___x_1448_; lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1493_; 
v_ref_1447_ = lean_ctor_get(v___y_1444_, 5);
v___x_1448_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1493_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1493_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v_traceState_1454_; lean_object* v_env_1455_; lean_object* v_nextMacroScope_1456_; lean_object* v_ngen_1457_; lean_object* v_auxDeclNGen_1458_; lean_object* v_cache_1459_; lean_object* v_messages_1460_; lean_object* v_infoState_1461_; lean_object* v_snapshotTasks_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1492_; 
v___x_1453_ = lean_st_ref_take(v___y_1445_);
v_traceState_1454_ = lean_ctor_get(v___x_1453_, 4);
v_env_1455_ = lean_ctor_get(v___x_1453_, 0);
v_nextMacroScope_1456_ = lean_ctor_get(v___x_1453_, 1);
v_ngen_1457_ = lean_ctor_get(v___x_1453_, 2);
v_auxDeclNGen_1458_ = lean_ctor_get(v___x_1453_, 3);
v_cache_1459_ = lean_ctor_get(v___x_1453_, 5);
v_messages_1460_ = lean_ctor_get(v___x_1453_, 6);
v_infoState_1461_ = lean_ctor_get(v___x_1453_, 7);
v_snapshotTasks_1462_ = lean_ctor_get(v___x_1453_, 8);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1464_ = v___x_1453_;
v_isShared_1465_ = v_isSharedCheck_1492_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_snapshotTasks_1462_);
lean_inc(v_infoState_1461_);
lean_inc(v_messages_1460_);
lean_inc(v_cache_1459_);
lean_inc(v_traceState_1454_);
lean_inc(v_auxDeclNGen_1458_);
lean_inc(v_ngen_1457_);
lean_inc(v_nextMacroScope_1456_);
lean_inc(v_env_1455_);
lean_dec(v___x_1453_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1492_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
uint64_t v_tid_1466_; lean_object* v_traces_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1491_; 
v_tid_1466_ = lean_ctor_get_uint64(v_traceState_1454_, sizeof(void*)*1);
v_traces_1467_ = lean_ctor_get(v_traceState_1454_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_traceState_1454_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1469_ = v_traceState_1454_;
v_isShared_1470_ = v_isSharedCheck_1491_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_traces_1467_);
lean_dec(v_traceState_1454_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1491_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; double v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0);
v___x_1473_ = 0;
v___x_1474_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1));
v___x_1475_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1475_, 0, v_cls_1440_);
lean_ctor_set(v___x_1475_, 1, v___x_1471_);
lean_ctor_set(v___x_1475_, 2, v___x_1474_);
lean_ctor_set_float(v___x_1475_, sizeof(void*)*3, v___x_1472_);
lean_ctor_set_float(v___x_1475_, sizeof(void*)*3 + 8, v___x_1472_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*3 + 16, v___x_1473_);
v___x_1476_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2));
v___x_1477_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v_a_1449_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
lean_inc(v_ref_1447_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_ref_1447_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_PersistentArray_push___redArg(v_traces_1467_, v___x_1478_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1479_);
v___x_1481_ = v___x_1469_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1479_);
lean_ctor_set_uint64(v_reuseFailAlloc_1490_, sizeof(void*)*1, v_tid_1466_);
v___x_1481_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___x_1481_);
v___x_1483_ = v___x_1464_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_env_1455_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_nextMacroScope_1456_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_ngen_1457_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_auxDeclNGen_1458_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1489_, 5, v_cache_1459_);
lean_ctor_set(v_reuseFailAlloc_1489_, 6, v_messages_1460_);
lean_ctor_set(v_reuseFailAlloc_1489_, 7, v_infoState_1461_);
lean_ctor_set(v_reuseFailAlloc_1489_, 8, v_snapshotTasks_1462_);
v___x_1483_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = lean_st_ref_set(v___y_1445_, v___x_1483_);
v___x_1485_ = lean_box(0);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1485_);
v___x_1487_ = v___x_1451_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object* v_cls_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v_cls_1494_, v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4));
v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v_declName_1511_, lean_object* v_declNameNonRec_1512_, lean_object* v___x_1513_, lean_object* v___x_1514_, lean_object* v_a_1515_, lean_object* v_____r_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; uint8_t v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v_fileName_1532_; lean_object* v_fileMap_1533_; lean_object* v_currRecDepth_1534_; lean_object* v_ref_1535_; lean_object* v_currNamespace_1536_; lean_object* v_openDecls_1537_; lean_object* v_initHeartbeats_1538_; lean_object* v_maxHeartbeats_1539_; lean_object* v_quotContext_1540_; lean_object* v_currMacroScope_1541_; lean_object* v_cancelTk_x3f_1542_; uint8_t v_suppressElabErrors_1543_; lean_object* v_inheritedTraceOptions_1544_; lean_object* v___y_1545_; lean_object* v___y_1574_; uint8_t v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1599_; uint8_t v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; uint8_t v___y_1636_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___x_1714_; 
v___x_1714_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1511_, v_declNameNonRec_1512_, v___x_1513_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1772_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref(v___x_1714_);
lean_inc(v___x_1514_);
v___x_1752_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1514_, v___y_1519_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1772_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1772_;
goto v_resetjp_1754_;
}
v___jp_1716_:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_1715_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1743_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref(v___x_1721_);
lean_inc(v___x_1514_);
v___x_1723_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1514_, v___y_1719_);
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1743_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1743_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_unbox(v_a_1724_);
lean_dec(v_a_1724_);
if (v___x_1728_ == 0)
{
lean_del_object(v___x_1726_);
v___y_1704_ = v_a_1722_;
v___y_1705_ = v___y_1717_;
v___y_1706_ = v___y_1718_;
v___y_1707_ = v___y_1719_;
v___y_1708_ = v___y_1720_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3);
lean_inc(v_a_1722_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 1);
lean_ctor_set(v___x_1726_, 0, v_a_1722_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1722_);
v___x_1731_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1729_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
lean_inc(v___x_1514_);
v___x_1733_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1514_, v___x_1732_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_dec_ref(v___x_1733_);
v___y_1704_ = v_a_1722_;
v___y_1705_ = v___y_1717_;
v___y_1706_ = v___y_1718_;
v___y_1707_ = v___y_1719_;
v___y_1708_ = v___y_1720_;
goto v___jp_1703_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1515_);
lean_dec(v___x_1514_);
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
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
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref(v_a_1515_);
lean_dec(v___x_1514_);
v_a_1744_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1721_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1721_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
v_resetjp_1754_:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_unbox(v_a_1753_);
lean_dec(v_a_1753_);
if (v___x_1757_ == 0)
{
lean_del_object(v___x_1755_);
v___y_1717_ = v___y_1517_;
v___y_1718_ = v___y_1518_;
v___y_1719_ = v___y_1519_;
v___y_1720_ = v___y_1520_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5);
lean_inc(v_a_1715_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 1);
lean_ctor_set(v___x_1755_, 0, v_a_1715_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1715_);
v___x_1760_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1758_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
lean_inc(v___x_1514_);
v___x_1762_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1514_, v___x_1761_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_dec_ref(v___x_1762_);
v___y_1717_ = v___y_1517_;
v___y_1718_ = v___y_1518_;
v___y_1719_ = v___y_1519_;
v___y_1720_ = v___y_1520_;
goto v___jp_1716_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1515_);
lean_dec(v___x_1514_);
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_a_1515_);
lean_dec(v___x_1514_);
v_a_1773_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1714_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1714_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
v___jp_1522_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1546_ = l_Lean_maxRecDepth;
v___x_1547_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v___y_1530_, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1548_, 0, v_fileName_1532_);
lean_ctor_set(v___x_1548_, 1, v_fileMap_1533_);
lean_ctor_set(v___x_1548_, 2, v___y_1530_);
lean_ctor_set(v___x_1548_, 3, v_currRecDepth_1534_);
lean_ctor_set(v___x_1548_, 4, v___x_1547_);
lean_ctor_set(v___x_1548_, 5, v_ref_1535_);
lean_ctor_set(v___x_1548_, 6, v_currNamespace_1536_);
lean_ctor_set(v___x_1548_, 7, v_openDecls_1537_);
lean_ctor_set(v___x_1548_, 8, v_initHeartbeats_1538_);
lean_ctor_set(v___x_1548_, 9, v_maxHeartbeats_1539_);
lean_ctor_set(v___x_1548_, 10, v_quotContext_1540_);
lean_ctor_set(v___x_1548_, 11, v_currMacroScope_1541_);
lean_ctor_set(v___x_1548_, 12, v_cancelTk_x3f_1542_);
lean_ctor_set(v___x_1548_, 13, v_inheritedTraceOptions_1544_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*14, v___y_1528_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*14 + 1, v_suppressElabErrors_1543_);
v___x_1549_ = l_Lean_MVarId_refl(v___y_1527_, v___y_1524_, v___y_1526_, v___y_1529_, v___x_1548_, v___y_1545_);
lean_dec_ref(v___x_1548_);
lean_dec_ref(v___y_1526_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; lean_object* v_a_1551_; uint8_t v___x_1552_; 
lean_dec_ref(v___x_1549_);
lean_inc(v___x_1514_);
v___x_1550_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1514_, v___y_1525_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = lean_unbox(v_a_1551_);
lean_dec(v_a_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref(v___y_1525_);
lean_dec(v___x_1514_);
v___x_1553_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_a_1515_, v___y_1529_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1);
v___x_1555_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1514_, v___x_1554_, v___y_1531_, v___y_1529_, v___y_1525_, v___y_1523_);
lean_dec_ref(v___y_1525_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1556_; 
lean_dec_ref(v___x_1555_);
v___x_1556_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_a_1515_, v___y_1529_);
return v___x_1556_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_a_1515_);
v_a_1557_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1555_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_a_1515_);
lean_dec(v___x_1514_);
v_a_1565_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1549_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1549_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
v___jp_1573_:
{
lean_object* v_fileName_1585_; lean_object* v_fileMap_1586_; lean_object* v_currRecDepth_1587_; lean_object* v_ref_1588_; lean_object* v_currNamespace_1589_; lean_object* v_openDecls_1590_; lean_object* v_initHeartbeats_1591_; lean_object* v_maxHeartbeats_1592_; lean_object* v_quotContext_1593_; lean_object* v_currMacroScope_1594_; lean_object* v_cancelTk_x3f_1595_; uint8_t v_suppressElabErrors_1596_; lean_object* v_inheritedTraceOptions_1597_; 
v_fileName_1585_ = lean_ctor_get(v___y_1583_, 0);
lean_inc_ref(v_fileName_1585_);
v_fileMap_1586_ = lean_ctor_get(v___y_1583_, 1);
lean_inc_ref(v_fileMap_1586_);
v_currRecDepth_1587_ = lean_ctor_get(v___y_1583_, 3);
lean_inc(v_currRecDepth_1587_);
v_ref_1588_ = lean_ctor_get(v___y_1583_, 5);
lean_inc(v_ref_1588_);
v_currNamespace_1589_ = lean_ctor_get(v___y_1583_, 6);
lean_inc(v_currNamespace_1589_);
v_openDecls_1590_ = lean_ctor_get(v___y_1583_, 7);
lean_inc(v_openDecls_1590_);
v_initHeartbeats_1591_ = lean_ctor_get(v___y_1583_, 8);
lean_inc(v_initHeartbeats_1591_);
v_maxHeartbeats_1592_ = lean_ctor_get(v___y_1583_, 9);
lean_inc(v_maxHeartbeats_1592_);
v_quotContext_1593_ = lean_ctor_get(v___y_1583_, 10);
lean_inc(v_quotContext_1593_);
v_currMacroScope_1594_ = lean_ctor_get(v___y_1583_, 11);
lean_inc(v_currMacroScope_1594_);
v_cancelTk_x3f_1595_ = lean_ctor_get(v___y_1583_, 12);
lean_inc(v_cancelTk_x3f_1595_);
v_suppressElabErrors_1596_ = lean_ctor_get_uint8(v___y_1583_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1597_ = lean_ctor_get(v___y_1583_, 13);
lean_inc_ref(v_inheritedTraceOptions_1597_);
lean_dec_ref(v___y_1583_);
v___y_1523_ = v___y_1574_;
v___y_1524_ = v___y_1575_;
v___y_1525_ = v___y_1576_;
v___y_1526_ = v___y_1577_;
v___y_1527_ = v___y_1578_;
v___y_1528_ = v___y_1579_;
v___y_1529_ = v___y_1580_;
v___y_1530_ = v___y_1581_;
v___y_1531_ = v___y_1582_;
v_fileName_1532_ = v_fileName_1585_;
v_fileMap_1533_ = v_fileMap_1586_;
v_currRecDepth_1534_ = v_currRecDepth_1587_;
v_ref_1535_ = v_ref_1588_;
v_currNamespace_1536_ = v_currNamespace_1589_;
v_openDecls_1537_ = v_openDecls_1590_;
v_initHeartbeats_1538_ = v_initHeartbeats_1591_;
v_maxHeartbeats_1539_ = v_maxHeartbeats_1592_;
v_quotContext_1540_ = v_quotContext_1593_;
v_currMacroScope_1541_ = v_currMacroScope_1594_;
v_cancelTk_x3f_1542_ = v_cancelTk_x3f_1595_;
v_suppressElabErrors_1543_ = v_suppressElabErrors_1596_;
v_inheritedTraceOptions_1544_ = v_inheritedTraceOptions_1597_;
v___y_1545_ = v___y_1584_;
goto v___jp_1522_;
}
v___jp_1598_:
{
if (v___y_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v_env_1610_; lean_object* v_nextMacroScope_1611_; lean_object* v_ngen_1612_; lean_object* v_auxDeclNGen_1613_; lean_object* v_traceState_1614_; lean_object* v_messages_1615_; lean_object* v_infoState_1616_; lean_object* v_snapshotTasks_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1627_; 
v___x_1609_ = lean_st_ref_take(v___y_1599_);
v_env_1610_ = lean_ctor_get(v___x_1609_, 0);
v_nextMacroScope_1611_ = lean_ctor_get(v___x_1609_, 1);
v_ngen_1612_ = lean_ctor_get(v___x_1609_, 2);
v_auxDeclNGen_1613_ = lean_ctor_get(v___x_1609_, 3);
v_traceState_1614_ = lean_ctor_get(v___x_1609_, 4);
v_messages_1615_ = lean_ctor_get(v___x_1609_, 6);
v_infoState_1616_ = lean_ctor_get(v___x_1609_, 7);
v_snapshotTasks_1617_ = lean_ctor_get(v___x_1609_, 8);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v___x_1609_, 5);
lean_dec(v_unused_1628_);
v___x_1619_ = v___x_1609_;
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_snapshotTasks_1617_);
lean_inc(v_infoState_1616_);
lean_inc(v_messages_1615_);
lean_inc(v_traceState_1614_);
lean_inc(v_auxDeclNGen_1613_);
lean_inc(v_ngen_1612_);
lean_inc(v_nextMacroScope_1611_);
lean_inc(v_env_1610_);
lean_dec(v___x_1609_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1621_ = l_Lean_Kernel_enableDiag(v_env_1610_, v___y_1604_);
v___x_1622_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 5, v___x_1622_);
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_nextMacroScope_1611_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_ngen_1612_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_auxDeclNGen_1613_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v_traceState_1614_);
lean_ctor_set(v_reuseFailAlloc_1626_, 5, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1626_, 6, v_messages_1615_);
lean_ctor_set(v_reuseFailAlloc_1626_, 7, v_infoState_1616_);
lean_ctor_set(v_reuseFailAlloc_1626_, 8, v_snapshotTasks_1617_);
v___x_1624_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_st_ref_set(v___y_1599_, v___x_1624_);
lean_inc_ref(v___y_1601_);
v___y_1574_ = v___y_1599_;
v___y_1575_ = v___y_1600_;
v___y_1576_ = v___y_1601_;
v___y_1577_ = v___y_1602_;
v___y_1578_ = v___y_1603_;
v___y_1579_ = v___y_1604_;
v___y_1580_ = v___y_1606_;
v___y_1581_ = v___y_1605_;
v___y_1582_ = v___y_1607_;
v___y_1583_ = v___y_1601_;
v___y_1584_ = v___y_1599_;
goto v___jp_1573_;
}
}
}
else
{
lean_inc_ref(v___y_1601_);
v___y_1574_ = v___y_1599_;
v___y_1575_ = v___y_1600_;
v___y_1576_ = v___y_1601_;
v___y_1577_ = v___y_1602_;
v___y_1578_ = v___y_1603_;
v___y_1579_ = v___y_1604_;
v___y_1580_ = v___y_1606_;
v___y_1581_ = v___y_1605_;
v___y_1582_ = v___y_1607_;
v___y_1583_ = v___y_1601_;
v___y_1584_ = v___y_1599_;
goto v___jp_1573_;
}
}
v___jp_1629_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v_foApprox_1639_; uint8_t v_ctxApprox_1640_; uint8_t v_quasiPatternApprox_1641_; uint8_t v_constApprox_1642_; uint8_t v_isDefEqStuckEx_1643_; uint8_t v_unificationHints_1644_; uint8_t v_proofIrrelevance_1645_; uint8_t v_assignSyntheticOpaque_1646_; uint8_t v_offsetCnstrs_1647_; uint8_t v_etaStruct_1648_; uint8_t v_univApprox_1649_; uint8_t v_iota_1650_; uint8_t v_beta_1651_; uint8_t v_proj_1652_; uint8_t v_zeta_1653_; uint8_t v_zetaDelta_1654_; uint8_t v_zetaUnused_1655_; uint8_t v_zetaHave_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1702_; 
v___x_1637_ = lean_st_ref_get(v___y_1630_);
v___x_1638_ = l_Lean_Meta_Context_config(v___y_1635_);
v_foApprox_1639_ = lean_ctor_get_uint8(v___x_1638_, 0);
v_ctxApprox_1640_ = lean_ctor_get_uint8(v___x_1638_, 1);
v_quasiPatternApprox_1641_ = lean_ctor_get_uint8(v___x_1638_, 2);
v_constApprox_1642_ = lean_ctor_get_uint8(v___x_1638_, 3);
v_isDefEqStuckEx_1643_ = lean_ctor_get_uint8(v___x_1638_, 4);
v_unificationHints_1644_ = lean_ctor_get_uint8(v___x_1638_, 5);
v_proofIrrelevance_1645_ = lean_ctor_get_uint8(v___x_1638_, 6);
v_assignSyntheticOpaque_1646_ = lean_ctor_get_uint8(v___x_1638_, 7);
v_offsetCnstrs_1647_ = lean_ctor_get_uint8(v___x_1638_, 8);
v_etaStruct_1648_ = lean_ctor_get_uint8(v___x_1638_, 10);
v_univApprox_1649_ = lean_ctor_get_uint8(v___x_1638_, 11);
v_iota_1650_ = lean_ctor_get_uint8(v___x_1638_, 12);
v_beta_1651_ = lean_ctor_get_uint8(v___x_1638_, 13);
v_proj_1652_ = lean_ctor_get_uint8(v___x_1638_, 14);
v_zeta_1653_ = lean_ctor_get_uint8(v___x_1638_, 15);
v_zetaDelta_1654_ = lean_ctor_get_uint8(v___x_1638_, 16);
v_zetaUnused_1655_ = lean_ctor_get_uint8(v___x_1638_, 17);
v_zetaHave_1656_ = lean_ctor_get_uint8(v___x_1638_, 18);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1658_ = v___x_1638_;
v_isShared_1659_ = v_isSharedCheck_1702_;
goto v_resetjp_1657_;
}
else
{
lean_dec(v___x_1638_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1702_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
uint8_t v_trackZetaDelta_1660_; lean_object* v_zetaDeltaSet_1661_; lean_object* v_lctx_1662_; lean_object* v_localInstances_1663_; lean_object* v_defEqCtx_x3f_1664_; lean_object* v_synthPendingDepth_1665_; lean_object* v_canUnfold_x3f_1666_; uint8_t v_univApprox_1667_; uint8_t v_inTypeClassResolution_1668_; uint8_t v_cacheInferType_1669_; lean_object* v_fileName_1670_; lean_object* v_fileMap_1671_; lean_object* v_options_1672_; lean_object* v_currRecDepth_1673_; lean_object* v_ref_1674_; lean_object* v_currNamespace_1675_; lean_object* v_openDecls_1676_; lean_object* v_initHeartbeats_1677_; lean_object* v_maxHeartbeats_1678_; lean_object* v_quotContext_1679_; lean_object* v_currMacroScope_1680_; lean_object* v_cancelTk_x3f_1681_; uint8_t v_suppressElabErrors_1682_; lean_object* v_inheritedTraceOptions_1683_; lean_object* v_env_1684_; lean_object* v_config_1686_; 
v_trackZetaDelta_1660_ = lean_ctor_get_uint8(v___y_1635_, sizeof(void*)*7);
v_zetaDeltaSet_1661_ = lean_ctor_get(v___y_1635_, 1);
v_lctx_1662_ = lean_ctor_get(v___y_1635_, 2);
v_localInstances_1663_ = lean_ctor_get(v___y_1635_, 3);
v_defEqCtx_x3f_1664_ = lean_ctor_get(v___y_1635_, 4);
v_synthPendingDepth_1665_ = lean_ctor_get(v___y_1635_, 5);
v_canUnfold_x3f_1666_ = lean_ctor_get(v___y_1635_, 6);
v_univApprox_1667_ = lean_ctor_get_uint8(v___y_1635_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1668_ = lean_ctor_get_uint8(v___y_1635_, sizeof(void*)*7 + 2);
v_cacheInferType_1669_ = lean_ctor_get_uint8(v___y_1635_, sizeof(void*)*7 + 3);
v_fileName_1670_ = lean_ctor_get(v___y_1632_, 0);
v_fileMap_1671_ = lean_ctor_get(v___y_1632_, 1);
v_options_1672_ = lean_ctor_get(v___y_1632_, 2);
v_currRecDepth_1673_ = lean_ctor_get(v___y_1632_, 3);
v_ref_1674_ = lean_ctor_get(v___y_1632_, 5);
v_currNamespace_1675_ = lean_ctor_get(v___y_1632_, 6);
v_openDecls_1676_ = lean_ctor_get(v___y_1632_, 7);
v_initHeartbeats_1677_ = lean_ctor_get(v___y_1632_, 8);
v_maxHeartbeats_1678_ = lean_ctor_get(v___y_1632_, 9);
v_quotContext_1679_ = lean_ctor_get(v___y_1632_, 10);
v_currMacroScope_1680_ = lean_ctor_get(v___y_1632_, 11);
v_cancelTk_x3f_1681_ = lean_ctor_get(v___y_1632_, 12);
v_suppressElabErrors_1682_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1683_ = lean_ctor_get(v___y_1632_, 13);
v_env_1684_ = lean_ctor_get(v___x_1637_, 0);
lean_inc_ref(v_env_1684_);
lean_dec(v___x_1637_);
if (v_isShared_1659_ == 0)
{
v_config_1686_ = v___x_1658_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 0, v_foApprox_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 1, v_ctxApprox_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 2, v_quasiPatternApprox_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 3, v_constApprox_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 4, v_isDefEqStuckEx_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 5, v_unificationHints_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 6, v_proofIrrelevance_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 7, v_assignSyntheticOpaque_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 8, v_offsetCnstrs_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 10, v_etaStruct_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 11, v_univApprox_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 12, v_iota_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 13, v_beta_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 14, v_proj_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 15, v_zeta_1653_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 16, v_zetaDelta_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 17, v_zetaUnused_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1701_, 18, v_zetaHave_1656_);
v_config_1686_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v_key_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; uint8_t v___x_1700_; 
lean_ctor_set_uint8(v_config_1686_, 9, v___y_1636_);
v___x_1687_ = l_Lean_Meta_Context_configKey(v___y_1635_);
v___x_1688_ = 2ULL;
v___x_1689_ = lean_uint64_shift_right(v___x_1687_, v___x_1688_);
v___x_1690_ = lean_uint64_shift_left(v___x_1689_, v___x_1688_);
v___x_1691_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1636_);
v_key_1692_ = lean_uint64_lor(v___x_1690_, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1693_, 0, v_config_1686_);
lean_ctor_set_uint64(v___x_1693_, sizeof(void*)*1, v_key_1692_);
lean_inc(v_canUnfold_x3f_1666_);
lean_inc(v_synthPendingDepth_1665_);
lean_inc(v_defEqCtx_x3f_1664_);
lean_inc_ref(v_localInstances_1663_);
lean_inc_ref(v_lctx_1662_);
lean_inc(v_zetaDeltaSet_1661_);
v___x_1694_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_zetaDeltaSet_1661_);
lean_ctor_set(v___x_1694_, 2, v_lctx_1662_);
lean_ctor_set(v___x_1694_, 3, v_localInstances_1663_);
lean_ctor_set(v___x_1694_, 4, v_defEqCtx_x3f_1664_);
lean_ctor_set(v___x_1694_, 5, v_synthPendingDepth_1665_);
lean_ctor_set(v___x_1694_, 6, v_canUnfold_x3f_1666_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*7, v_trackZetaDelta_1660_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*7 + 1, v_univApprox_1667_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1668_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*7 + 3, v_cacheInferType_1669_);
v___x_1695_ = l_Lean_Meta_smartUnfolding;
v___x_1696_ = 0;
lean_inc_ref(v_options_1672_);
v___x_1697_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_options_1672_, v___x_1695_, v___x_1696_);
v___x_1698_ = l_Lean_diagnostics;
v___x_1699_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_1697_, v___x_1698_);
v___x_1700_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1684_);
lean_dec_ref(v_env_1684_);
if (v___x_1700_ == 0)
{
if (v___x_1699_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1683_);
lean_inc(v_cancelTk_x3f_1681_);
lean_inc(v_currMacroScope_1680_);
lean_inc(v_quotContext_1679_);
lean_inc(v_maxHeartbeats_1678_);
lean_inc(v_initHeartbeats_1677_);
lean_inc(v_openDecls_1676_);
lean_inc(v_currNamespace_1675_);
lean_inc(v_ref_1674_);
lean_inc(v_currRecDepth_1673_);
lean_inc_ref(v_fileMap_1671_);
lean_inc_ref(v_fileName_1670_);
v___y_1523_ = v___y_1630_;
v___y_1524_ = v___y_1631_;
v___y_1525_ = v___y_1632_;
v___y_1526_ = v___x_1694_;
v___y_1527_ = v___y_1633_;
v___y_1528_ = v___x_1699_;
v___y_1529_ = v___y_1634_;
v___y_1530_ = v___x_1697_;
v___y_1531_ = v___y_1635_;
v_fileName_1532_ = v_fileName_1670_;
v_fileMap_1533_ = v_fileMap_1671_;
v_currRecDepth_1534_ = v_currRecDepth_1673_;
v_ref_1535_ = v_ref_1674_;
v_currNamespace_1536_ = v_currNamespace_1675_;
v_openDecls_1537_ = v_openDecls_1676_;
v_initHeartbeats_1538_ = v_initHeartbeats_1677_;
v_maxHeartbeats_1539_ = v_maxHeartbeats_1678_;
v_quotContext_1540_ = v_quotContext_1679_;
v_currMacroScope_1541_ = v_currMacroScope_1680_;
v_cancelTk_x3f_1542_ = v_cancelTk_x3f_1681_;
v_suppressElabErrors_1543_ = v_suppressElabErrors_1682_;
v_inheritedTraceOptions_1544_ = v_inheritedTraceOptions_1683_;
v___y_1545_ = v___y_1630_;
goto v___jp_1522_;
}
else
{
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___y_1632_;
v___y_1602_ = v___x_1694_;
v___y_1603_ = v___y_1633_;
v___y_1604_ = v___x_1699_;
v___y_1605_ = v___x_1697_;
v___y_1606_ = v___y_1634_;
v___y_1607_ = v___y_1635_;
v___y_1608_ = v___x_1700_;
goto v___jp_1598_;
}
}
else
{
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___y_1632_;
v___y_1602_ = v___x_1694_;
v___y_1603_ = v___y_1633_;
v___y_1604_ = v___x_1699_;
v___y_1605_ = v___x_1697_;
v___y_1606_ = v___y_1634_;
v___y_1607_ = v___y_1635_;
v___y_1608_ = v___x_1699_;
goto v___jp_1598_;
}
}
}
}
v___jp_1703_:
{
lean_object* v___x_1709_; uint8_t v_transparency_1710_; uint8_t v___x_1711_; uint8_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1709_ = l_Lean_Meta_Context_config(v___y_1705_);
v_transparency_1710_ = lean_ctor_get_uint8(v___x_1709_, 9);
lean_dec_ref(v___x_1709_);
v___x_1711_ = 0;
v___x_1712_ = 1;
v___x_1713_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1710_, v___x_1711_);
if (v___x_1713_ == 0)
{
lean_inc_ref(v___y_1707_);
v___y_1630_ = v___y_1708_;
v___y_1631_ = v___x_1712_;
v___y_1632_ = v___y_1707_;
v___y_1633_ = v___y_1704_;
v___y_1634_ = v___y_1706_;
v___y_1635_ = v___y_1705_;
v___y_1636_ = v_transparency_1710_;
goto v___jp_1629_;
}
else
{
lean_inc_ref(v___y_1707_);
v___y_1630_ = v___y_1708_;
v___y_1631_ = v___x_1712_;
v___y_1632_ = v___y_1707_;
v___y_1633_ = v___y_1704_;
v___y_1634_ = v___y_1706_;
v___y_1635_ = v___y_1705_;
v___y_1636_ = v___x_1711_;
goto v___jp_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_declName_1781_, lean_object* v_declNameNonRec_1782_, lean_object* v___x_1783_, lean_object* v___x_1784_, lean_object* v_a_1785_, lean_object* v_____r_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v_declName_1781_, v_declNameNonRec_1782_, v___x_1783_, v___x_1784_, v_a_1785_, v_____r_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1792_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_declName_1808_, lean_object* v_a_1809_, lean_object* v___x_1810_, lean_object* v_declNameNonRec_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___y_1818_; lean_object* v___y_1819_; uint8_t v___y_1820_; lean_object* v___y_1830_; lean_object* v_a_1831_; lean_object* v___y_1835_; lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1809_, v___x_1810_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1865_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6));
v___x_1840_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1839_, v___y_1814_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1865_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1865_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = l_Lean_Expr_mvarId_x21(v_a_1838_);
v___x_1846_ = lean_unbox(v_a_1841_);
lean_dec(v_a_1841_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_del_object(v___x_1843_);
v___x_1847_ = lean_box(0);
lean_inc(v_declName_1808_);
v___x_1848_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v_declName_1808_, v_declNameNonRec_1811_, v___x_1845_, v___x_1839_, v_a_1838_, v___x_1847_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
v___y_1835_ = v___x_1848_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8);
lean_inc(v___x_1845_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 1);
lean_ctor_set(v___x_1843_, 0, v___x_1845_);
v___x_1851_ = v___x_1843_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1845_);
v___x_1851_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1849_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1839_, v___x_1852_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref(v___x_1853_);
lean_inc(v_declName_1808_);
v___x_1855_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v_declName_1808_, v_declNameNonRec_1811_, v___x_1845_, v___x_1839_, v_a_1838_, v_a_1854_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
v___y_1835_ = v___x_1855_;
goto v___jp_1834_;
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v___x_1845_);
lean_dec(v_a_1838_);
lean_dec(v_declNameNonRec_1811_);
v_a_1856_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1853_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1853_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
lean_inc(v_a_1856_);
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
v___y_1830_ = v___x_1861_;
v_a_1831_ = v_a_1856_;
goto v___jp_1829_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_1811_);
v___y_1835_ = v___x_1837_;
goto v___jp_1834_;
}
v___jp_1817_:
{
if (v___y_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v___y_1818_);
v___x_1821_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
v___x_1822_ = l_Lean_MessageData_ofConstName(v_declName_1808_, v___y_1820_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_Exception_toMessageData(v___y_1819_);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_1827_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
return v___x_1828_;
}
else
{
lean_dec_ref(v___y_1819_);
lean_dec(v_declName_1808_);
return v___y_1818_;
}
}
v___jp_1829_:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Lean_Exception_isInterrupt(v_a_1831_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
lean_inc_ref(v_a_1831_);
v___x_1833_ = l_Lean_Exception_isRuntime(v_a_1831_);
v___y_1818_ = v___y_1830_;
v___y_1819_ = v_a_1831_;
v___y_1820_ = v___x_1833_;
goto v___jp_1817_;
}
else
{
v___y_1818_ = v___y_1830_;
v___y_1819_ = v_a_1831_;
v___y_1820_ = v___x_1832_;
goto v___jp_1817_;
}
}
v___jp_1834_:
{
if (lean_obj_tag(v___y_1835_) == 0)
{
lean_dec(v_declName_1808_);
return v___y_1835_;
}
else
{
lean_object* v_a_1836_; 
v_a_1836_ = lean_ctor_get(v___y_1835_, 0);
lean_inc(v_a_1836_);
v___y_1830_ = v___y_1835_;
v_a_1831_ = v_a_1836_;
goto v___jp_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_declName_1866_, lean_object* v_a_1867_, lean_object* v___x_1868_, lean_object* v_declNameNonRec_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1866_, v_a_1867_, v___x_1868_, v_declNameNonRec_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
if (lean_obj_tag(v_a_1876_) == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = l_List_reverse___redArg(v_a_1877_);
return v___x_1878_;
}
else
{
lean_object* v_head_1879_; lean_object* v_tail_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
v_head_1879_ = lean_ctor_get(v_a_1876_, 0);
v_tail_1880_ = lean_ctor_get(v_a_1876_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_a_1876_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1882_ = v_a_1876_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_tail_1880_);
lean_inc(v_head_1879_);
lean_dec(v_a_1876_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = l_Lean_mkLevelParam(v_head_1879_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 1, v_a_1877_);
lean_ctor_set(v___x_1882_, 0, v___x_1884_);
v___x_1886_ = v___x_1882_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_a_1877_);
v___x_1886_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
v_a_1876_ = v_tail_1880_;
v_a_1877_ = v___x_1886_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_levelParams_1890_, lean_object* v_declName_1891_, lean_object* v_declNameNonRec_1892_, lean_object* v_name_1893_, lean_object* v_xs_1894_, lean_object* v_body_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; lean_object* v_us_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1901_ = lean_box(0);
lean_inc(v_levelParams_1890_);
v_us_1902_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_1890_, v___x_1901_);
lean_inc(v_declName_1891_);
v___x_1903_ = l_Lean_mkConst(v_declName_1891_, v_us_1902_);
v___x_1904_ = l_Lean_mkAppN(v___x_1903_, v_xs_1894_);
v___x_1905_ = l_Lean_Meta_mkEq(v___x_1904_, v_body_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; lean_object* v___f_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = lean_box(0);
lean_inc(v_a_1906_);
v___f_1908_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1908_, 0, v_declName_1891_);
lean_closure_set(v___f_1908_, 1, v_a_1906_);
lean_closure_set(v___f_1908_, 2, v___x_1907_);
lean_closure_set(v___f_1908_, 3, v_declNameNonRec_1892_);
v___x_1909_ = 0;
v___x_1910_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___f_1908_, v___x_1909_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; uint8_t v___x_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
v___x_1912_ = 1;
v___x_1913_ = 1;
v___x_1914_ = l_Lean_Meta_mkForallFVars(v_xs_1894_, v_a_1906_, v___x_1909_, v___x_1912_, v___x_1912_, v___x_1913_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
v___x_1916_ = l_Lean_Meta_letToHave(v_a_1915_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = l_Lean_Meta_mkLambdaFVars(v_xs_1894_, v_a_1911_, v___x_1909_, v___x_1912_, v___x_1909_, v___x_1912_, v___x_1913_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
lean_inc(v_name_1893_);
v___x_1920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1920_, 0, v_name_1893_);
lean_ctor_set(v___x_1920_, 1, v_levelParams_1890_);
lean_ctor_set(v___x_1920_, 2, v_a_1917_);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_name_1893_);
lean_ctor_set(v___x_1921_, 1, v___x_1901_);
v___x_1922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v_a_1919_);
lean_ctor_set(v___x_1922_, 2, v___x_1921_);
v___x_1923_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v___x_1922_, v___y_1899_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = l_Lean_addDecl(v_a_1924_, v___x_1909_, v___y_1898_, v___y_1899_);
return v___x_1925_;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_a_1917_);
lean_dec(v_name_1893_);
lean_dec(v_levelParams_1890_);
v_a_1926_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1918_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1918_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_a_1911_);
lean_dec(v_name_1893_);
lean_dec(v_levelParams_1890_);
v_a_1934_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1916_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1916_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_a_1911_);
lean_dec(v_name_1893_);
lean_dec(v_levelParams_1890_);
v_a_1942_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1914_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1914_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_a_1906_);
lean_dec(v_name_1893_);
lean_dec(v_levelParams_1890_);
v_a_1950_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1910_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1910_);
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
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_name_1893_);
lean_dec(v_declNameNonRec_1892_);
lean_dec(v_declName_1891_);
lean_dec(v_levelParams_1890_);
v_a_1958_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1905_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1905_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_levelParams_1966_, lean_object* v_declName_1967_, lean_object* v_declNameNonRec_1968_, lean_object* v_name_1969_, lean_object* v_xs_1970_, lean_object* v_body_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_levelParams_1966_, v_declName_1967_, v_declNameNonRec_1968_, v_name_1969_, v_xs_1970_, v_body_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v_xs_1970_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_1978_, lean_object* v_info_1979_, lean_object* v_name_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v_levelParams_1987_; lean_object* v_value_1988_; lean_object* v_declNameNonRec_1989_; lean_object* v_fileName_1990_; lean_object* v_fileMap_1991_; lean_object* v_options_1992_; lean_object* v_currRecDepth_1993_; lean_object* v_ref_1994_; lean_object* v_currNamespace_1995_; lean_object* v_openDecls_1996_; lean_object* v_initHeartbeats_1997_; lean_object* v_maxHeartbeats_1998_; lean_object* v_quotContext_1999_; lean_object* v_currMacroScope_2000_; lean_object* v_cancelTk_x3f_2001_; uint8_t v_suppressElabErrors_2002_; lean_object* v_inheritedTraceOptions_2003_; lean_object* v_env_2004_; lean_object* v___f_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v_fileName_2012_; lean_object* v_fileMap_2013_; lean_object* v_currRecDepth_2014_; lean_object* v_ref_2015_; lean_object* v_currNamespace_2016_; lean_object* v_openDecls_2017_; lean_object* v_initHeartbeats_2018_; lean_object* v_maxHeartbeats_2019_; lean_object* v_quotContext_2020_; lean_object* v_currMacroScope_2021_; lean_object* v_cancelTk_x3f_2022_; uint8_t v_suppressElabErrors_2023_; lean_object* v_inheritedTraceOptions_2024_; lean_object* v___y_2025_; uint8_t v___y_2031_; uint8_t v___x_2052_; 
v___x_1986_ = lean_st_ref_get(v_a_1984_);
v_levelParams_1987_ = lean_ctor_get(v_info_1979_, 1);
lean_inc(v_levelParams_1987_);
v_value_1988_ = lean_ctor_get(v_info_1979_, 3);
lean_inc_ref(v_value_1988_);
v_declNameNonRec_1989_ = lean_ctor_get(v_info_1979_, 5);
lean_inc(v_declNameNonRec_1989_);
lean_dec_ref(v_info_1979_);
v_fileName_1990_ = lean_ctor_get(v_a_1983_, 0);
lean_inc_ref(v_fileName_1990_);
v_fileMap_1991_ = lean_ctor_get(v_a_1983_, 1);
lean_inc_ref(v_fileMap_1991_);
v_options_1992_ = lean_ctor_get(v_a_1983_, 2);
lean_inc_ref(v_options_1992_);
v_currRecDepth_1993_ = lean_ctor_get(v_a_1983_, 3);
lean_inc(v_currRecDepth_1993_);
v_ref_1994_ = lean_ctor_get(v_a_1983_, 5);
lean_inc(v_ref_1994_);
v_currNamespace_1995_ = lean_ctor_get(v_a_1983_, 6);
lean_inc(v_currNamespace_1995_);
v_openDecls_1996_ = lean_ctor_get(v_a_1983_, 7);
lean_inc(v_openDecls_1996_);
v_initHeartbeats_1997_ = lean_ctor_get(v_a_1983_, 8);
lean_inc(v_initHeartbeats_1997_);
v_maxHeartbeats_1998_ = lean_ctor_get(v_a_1983_, 9);
lean_inc(v_maxHeartbeats_1998_);
v_quotContext_1999_ = lean_ctor_get(v_a_1983_, 10);
lean_inc(v_quotContext_1999_);
v_currMacroScope_2000_ = lean_ctor_get(v_a_1983_, 11);
lean_inc(v_currMacroScope_2000_);
v_cancelTk_x3f_2001_ = lean_ctor_get(v_a_1983_, 12);
lean_inc(v_cancelTk_x3f_2001_);
v_suppressElabErrors_2002_ = lean_ctor_get_uint8(v_a_1983_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2003_ = lean_ctor_get(v_a_1983_, 13);
lean_inc_ref(v_inheritedTraceOptions_2003_);
lean_dec_ref(v_a_1983_);
v_env_2004_ = lean_ctor_get(v___x_1986_, 0);
lean_inc_ref(v_env_2004_);
lean_dec(v___x_1986_);
v___f_2005_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed), 11, 4);
lean_closure_set(v___f_2005_, 0, v_levelParams_1987_);
lean_closure_set(v___f_2005_, 1, v_declName_1978_);
lean_closure_set(v___f_2005_, 2, v_declNameNonRec_1989_);
lean_closure_set(v___f_2005_, 3, v_name_1980_);
v___x_2006_ = 0;
v___x_2007_ = l_Lean_Meta_tactic_hygienic;
v___x_2008_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_options_1992_, v___x_2007_, v___x_2006_);
v___x_2009_ = l_Lean_diagnostics;
v___x_2010_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_2008_, v___x_2009_);
v___x_2052_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2004_);
lean_dec_ref(v_env_2004_);
if (v___x_2052_ == 0)
{
if (v___x_2010_ == 0)
{
v_fileName_2012_ = v_fileName_1990_;
v_fileMap_2013_ = v_fileMap_1991_;
v_currRecDepth_2014_ = v_currRecDepth_1993_;
v_ref_2015_ = v_ref_1994_;
v_currNamespace_2016_ = v_currNamespace_1995_;
v_openDecls_2017_ = v_openDecls_1996_;
v_initHeartbeats_2018_ = v_initHeartbeats_1997_;
v_maxHeartbeats_2019_ = v_maxHeartbeats_1998_;
v_quotContext_2020_ = v_quotContext_1999_;
v_currMacroScope_2021_ = v_currMacroScope_2000_;
v_cancelTk_x3f_2022_ = v_cancelTk_x3f_2001_;
v_suppressElabErrors_2023_ = v_suppressElabErrors_2002_;
v_inheritedTraceOptions_2024_ = v_inheritedTraceOptions_2003_;
v___y_2025_ = v_a_1984_;
goto v___jp_2011_;
}
else
{
v___y_2031_ = v___x_2052_;
goto v___jp_2030_;
}
}
else
{
v___y_2031_ = v___x_2010_;
goto v___jp_2030_;
}
v___jp_2011_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2026_ = l_Lean_maxRecDepth;
v___x_2027_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v___x_2008_, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2028_, 0, v_fileName_2012_);
lean_ctor_set(v___x_2028_, 1, v_fileMap_2013_);
lean_ctor_set(v___x_2028_, 2, v___x_2008_);
lean_ctor_set(v___x_2028_, 3, v_currRecDepth_2014_);
lean_ctor_set(v___x_2028_, 4, v___x_2027_);
lean_ctor_set(v___x_2028_, 5, v_ref_2015_);
lean_ctor_set(v___x_2028_, 6, v_currNamespace_2016_);
lean_ctor_set(v___x_2028_, 7, v_openDecls_2017_);
lean_ctor_set(v___x_2028_, 8, v_initHeartbeats_2018_);
lean_ctor_set(v___x_2028_, 9, v_maxHeartbeats_2019_);
lean_ctor_set(v___x_2028_, 10, v_quotContext_2020_);
lean_ctor_set(v___x_2028_, 11, v_currMacroScope_2021_);
lean_ctor_set(v___x_2028_, 12, v_cancelTk_x3f_2022_);
lean_ctor_set(v___x_2028_, 13, v_inheritedTraceOptions_2024_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*14, v___x_2010_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*14 + 1, v_suppressElabErrors_2023_);
v___x_2029_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(v_value_1988_, v___f_2005_, v___x_2006_, v_a_1981_, v_a_1982_, v___x_2028_, v___y_2025_);
lean_dec_ref(v___x_2028_);
return v___x_2029_;
}
v___jp_2030_:
{
if (v___y_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v_env_2033_; lean_object* v_nextMacroScope_2034_; lean_object* v_ngen_2035_; lean_object* v_auxDeclNGen_2036_; lean_object* v_traceState_2037_; lean_object* v_messages_2038_; lean_object* v_infoState_2039_; lean_object* v_snapshotTasks_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
v___x_2032_ = lean_st_ref_take(v_a_1984_);
v_env_2033_ = lean_ctor_get(v___x_2032_, 0);
v_nextMacroScope_2034_ = lean_ctor_get(v___x_2032_, 1);
v_ngen_2035_ = lean_ctor_get(v___x_2032_, 2);
v_auxDeclNGen_2036_ = lean_ctor_get(v___x_2032_, 3);
v_traceState_2037_ = lean_ctor_get(v___x_2032_, 4);
v_messages_2038_ = lean_ctor_get(v___x_2032_, 6);
v_infoState_2039_ = lean_ctor_get(v___x_2032_, 7);
v_snapshotTasks_2040_ = lean_ctor_get(v___x_2032_, 8);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2032_, 5);
lean_dec(v_unused_2051_);
v___x_2042_ = v___x_2032_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_snapshotTasks_2040_);
lean_inc(v_infoState_2039_);
lean_inc(v_messages_2038_);
lean_inc(v_traceState_2037_);
lean_inc(v_auxDeclNGen_2036_);
lean_inc(v_ngen_2035_);
lean_inc(v_nextMacroScope_2034_);
lean_inc(v_env_2033_);
lean_dec(v___x_2032_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = l_Lean_Kernel_enableDiag(v_env_2033_, v___x_2010_);
v___x_2045_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 5, v___x_2045_);
lean_ctor_set(v___x_2042_, 0, v___x_2044_);
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_nextMacroScope_2034_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_ngen_2035_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_auxDeclNGen_2036_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_traceState_2037_);
lean_ctor_set(v_reuseFailAlloc_2049_, 5, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2049_, 6, v_messages_2038_);
lean_ctor_set(v_reuseFailAlloc_2049_, 7, v_infoState_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 8, v_snapshotTasks_2040_);
v___x_2047_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_st_ref_set(v_a_1984_, v___x_2047_);
v_fileName_2012_ = v_fileName_1990_;
v_fileMap_2013_ = v_fileMap_1991_;
v_currRecDepth_2014_ = v_currRecDepth_1993_;
v_ref_2015_ = v_ref_1994_;
v_currNamespace_2016_ = v_currNamespace_1995_;
v_openDecls_2017_ = v_openDecls_1996_;
v_initHeartbeats_2018_ = v_initHeartbeats_1997_;
v_maxHeartbeats_2019_ = v_maxHeartbeats_1998_;
v_quotContext_2020_ = v_quotContext_1999_;
v_currMacroScope_2021_ = v_currMacroScope_2000_;
v_cancelTk_x3f_2022_ = v_cancelTk_x3f_2001_;
v_suppressElabErrors_2023_ = v_suppressElabErrors_2002_;
v_inheritedTraceOptions_2024_ = v_inheritedTraceOptions_2003_;
v___y_2025_ = v_a_1984_;
goto v___jp_2011_;
}
}
}
else
{
v_fileName_2012_ = v_fileName_1990_;
v_fileMap_2013_ = v_fileMap_1991_;
v_currRecDepth_2014_ = v_currRecDepth_1993_;
v_ref_2015_ = v_ref_1994_;
v_currNamespace_2016_ = v_currNamespace_1995_;
v_openDecls_2017_ = v_openDecls_1996_;
v_initHeartbeats_2018_ = v_initHeartbeats_1997_;
v_maxHeartbeats_2019_ = v_maxHeartbeats_1998_;
v_quotContext_2020_ = v_quotContext_1999_;
v_currMacroScope_2021_ = v_currMacroScope_2000_;
v_cancelTk_x3f_2022_ = v_cancelTk_x3f_2001_;
v_suppressElabErrors_2023_ = v_suppressElabErrors_2002_;
v_inheritedTraceOptions_2024_ = v_inheritedTraceOptions_2003_;
v___y_2025_ = v_a_1984_;
goto v___jp_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_2053_, lean_object* v_info_2054_, lean_object* v_name_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2053_, v_info_2054_, v_name_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_2062_, lean_object* v_info_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2069_; lean_object* v_env_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2069_ = lean_st_ref_get(v_a_2067_);
v_env_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc_ref(v_env_2070_);
lean_dec(v___x_2069_);
v___x_2071_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2062_);
v___x_2072_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2070_, v_declName_2062_, v___x_2071_);
lean_inc(v___x_2072_);
lean_inc(v_declName_2062_);
v___x_2073_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_2073_, 0, v_declName_2062_);
lean_closure_set(v___x_2073_, 1, v_info_2063_);
lean_closure_set(v___x_2073_, 2, v___x_2072_);
lean_inc_ref(v_a_2066_);
lean_inc(v___x_2072_);
v___x_2074_ = l_Lean_Meta_realizeConst(v_declName_2062_, v___x_2072_, v___x_2073_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2074_, 0);
lean_dec(v_unused_2082_);
v___x_2076_ = v___x_2074_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v___x_2074_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2072_);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2072_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v___x_2072_);
v_a_2083_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2074_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2074_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_2091_, lean_object* v_info_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2091_, v_info_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v_env_2107_; lean_object* v_env_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; 
v___x_2105_ = lean_st_ref_get(v_a_2103_);
v___x_2106_ = lean_st_ref_get(v_a_2103_);
v_env_2107_ = lean_ctor_get(v___x_2105_, 0);
lean_inc_ref(v_env_2107_);
lean_dec(v___x_2105_);
v_env_2108_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_ref(v_env_2108_);
lean_dec(v___x_2106_);
v___x_2109_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2099_);
v___x_2110_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2107_, v_declName_2099_, v___x_2109_);
v___x_2111_ = 1;
lean_inc(v___x_2110_);
lean_inc_ref(v_env_2108_);
v___x_2112_ = l_Lean_Environment_contains(v_env_2108_, v___x_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v_toEnvExtension_2114_; lean_object* v_asyncMode_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v___x_2110_);
v___x_2113_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc_ref(v_toEnvExtension_2114_);
v_asyncMode_2115_ = lean_ctor_get(v_toEnvExtension_2114_, 2);
lean_inc(v_asyncMode_2115_);
lean_dec_ref(v_toEnvExtension_2114_);
v___x_2116_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_2117_ = 0;
lean_inc(v_declName_2099_);
v___x_2118_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2116_, v___x_2113_, v_env_2108_, v_declName_2099_, v_asyncMode_2115_, v___x_2117_);
lean_dec(v_asyncMode_2115_);
if (lean_obj_tag(v___x_2118_) == 1)
{
lean_object* v_val_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2143_; 
v_val_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2143_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_val_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2143_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2099_, v_val_2119_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2134_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v_a_2124_);
v___x_2129_ = v___x_2121_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2129_);
v___x_2131_ = v___x_2126_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_2121_);
v_a_2135_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2123_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2123_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec(v___x_2118_);
lean_dec(v_declName_2099_);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref(v_env_2108_);
lean_dec(v_declName_2099_);
v___x_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2110_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_2158_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_2160_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo);
res = l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_PartialFixpoint_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_eqnInfoExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
}
#ifdef __cplusplus
}
#endif
