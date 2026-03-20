// Lean compiler output
// Module: Lean.Elab.Tactic.Monotonicity
// Imports: public import Lean.Meta.Tactic.Split public import Lean.Elab.RecAppSyntax public import Lean.Elab.Tactic.Basic public import Init.Internal.Order
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MVarId_applyConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Split_splitMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lambda expected"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_headBetaUnderLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Monotonicity"};
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "monotoneExt"};
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 197, 232, 151, 31, 114, 201, 85)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 32, 30, 204, 89, 199, 107, 6)}};
static const lean_object* l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_monotoneExt;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`[partial_fixpoint_monotone]` attribute only applies to lemmas proving "};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "monotone"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 75, 136, 217, 100, 156, 144, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(59, 196, 222, 254, 197, 21, 130, 124)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__11_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 140, 192, 110, 71, 240, 154, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__11_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__11_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__12_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__11_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 212, 4, 86, 247, 163, 94, 38)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__12_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__12_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__13_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__12_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(153, 5, 202, 81, 145, 168, 87, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__13_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__13_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__14_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__14_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__14_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__15_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__13_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__14_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 98, 16, 138, 84, 251, 15, 66)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__15_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__15_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__16_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__16_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__16_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__17_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__15_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__16_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 172, 22, 91, 113, 32, 182, 37)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__17_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__17_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__18_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__17_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(196, 216, 82, 243, 114, 148, 94, 90)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__18_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__18_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__19_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__18_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 87, 240, 225, 46, 211, 118, 82)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__19_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__19_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__20_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__19_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 80, 35, 149, 15, 44, 32, 194)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__20_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__20_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__21_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__20_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(196, 138, 207, 136, 221, 178, 18, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__21_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__21_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__22_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__21_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1250514167) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(15, 167, 57, 65, 131, 192, 222, 112)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__22_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__22_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__23_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__23_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__23_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__24_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__22_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__23_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(196, 57, 247, 147, 241, 42, 251, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__24_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__24_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__25_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__25_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__25_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__26_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__24_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__25_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(208, 123, 4, 22, 209, 130, 42, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__26_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__26_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__27_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__26_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 207, 190, 114, 40, 155, 255, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__27_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__27_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__28_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "partial_fixpoint_monotone"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__28_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__28_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__29_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__28_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 165, 223, 223, 117, 142, 190, 151)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__29_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__29_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__30_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__29_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__30_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__30_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__31_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "monotonicity theorem"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__31_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__31_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__32_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__27_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__29_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__31_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__32_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__32_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__33_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__32_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__30_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__33_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__33_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 302, .m_capacity = 302, .m_length = 301, .m_data = "Registers a monotonicity theorem for `partial_fixpoint`.\n\nMonotonicity theorems should have `Lean.Order.monotone ...` as a conclusion. They are used in the\n`monotonicity` tactic (scoped in the `Lean.Order` namespace) to automatically prove monotonicity\nfor functions defined using `partial_fixpoint`.\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_findMonoThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_findMonoThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Failed to prove monotonicity of:"};
static const lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Tried to apply "};
static const lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5;
static const lean_string_object l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", but failed."};
static const lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Could not apply "};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoCall___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__0;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "monotone_id"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__1 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 180, 187, 101, 53, 255, 91, 19)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__2 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__2_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Internal error in `solveMonoCall "};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__3 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__4;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "`: unexpected type "};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__5 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoCall___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__6;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "`: whnfUntil failed\?"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__7 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoCall___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__8;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 86, 242, 24, 111, 107, 219, 193)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__9 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__9_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instPartialOrderPProd"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__10 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__10_value),LEAN_SCALAR_PTR_LITERAL(60, 246, 155, 2, 86, 129, 181, 75)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__11 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__11_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PProd"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__12 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__12_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "monotone_snd"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__13 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__12_value),LEAN_SCALAR_PTR_LITERAL(141, 95, 229, 62, 87, 161, 97, 26)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__13_value),LEAN_SCALAR_PTR_LITERAL(145, 36, 129, 200, 116, 223, 208, 172)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__14 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__14_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "monotone_fst"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__15 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__12_value),LEAN_SCALAR_PTR_LITERAL(141, 95, 229, 62, 87, 161, 97, 26)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__15_value),LEAN_SCALAR_PTR_LITERAL(23, 221, 93, 233, 17, 53, 114, 138)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__16 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__16_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "`: unexpected instance "};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__17 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoCall___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__18;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "instOrderPi"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__19 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__19_value),LEAN_SCALAR_PTR_LITERAL(30, 250, 76, 182, 73, 26, 134, 241)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__20 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__20_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "monotone_apply"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__21 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoCall___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__21_value),LEAN_SCALAR_PTR_LITERAL(244, 112, 58, 82, 85, 83, 41, 80)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___closed__22 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoCall___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateLambdaE!"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "monotonicity"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(147, 139, 141, 172, 97, 219, 238, 39)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Succeeded with "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__8(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Unexpected goal:"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Failed to assign "};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " to goal"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__7 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Found recursive call "};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__9 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__11 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__12 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__12_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Found monoThms: "};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__13 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Unexpected number of goals after `"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__15 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "monotone_of_monotone_apply"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__17 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__17_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "monotone_const"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__18 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__18_value;
static const lean_string_object l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "monotonicity at\n"};
static const lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__19 = (const lean_object*)&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Monotonicity_defaultFailK___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__0_value)} };
static const lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 245, 3, 217, 93, 200, 5, 81)}};
static const lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0 = (const lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalMonotonicity"};
static const lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__1 = (const lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 197, 232, 151, 31, 114, 201, 85)}};
static const lean_ctor_object l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(189, 224, 16, 213, 21, 188, 162, 150)}};
static const lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2 = (const lean_object*)&l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1();
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__14_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 201, 9, 248, 23, 22, 82, 31)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__16_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 124, 55, 0, 61, 150, 105, 219)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 86, 80, 96, 10, 59, 39, 88)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 231, 15, 142, 19, 15, 154, 34)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 228, 167, 115, 3, 238, 9, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Monotonicity_initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 144, 174, 51, 65, 124, 69, 78)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)(((size_t)(67824763) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(238, 77, 166, 112, 74, 143, 150, 206)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__23_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 237, 179, 170, 14, 176, 42, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__25_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 235, 234, 51, 254, 116, 149, 232)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(76, 179, 59, 228, 129, 35, 160, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = l_Lean_instInhabitedExpr;
v___x_3_ = lean_panic_fn(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__2));
v___x_8_ = lean_unsigned_to_nat(19u);
v___x_9_ = lean_unsigned_to_nat(1907u);
v___x_10_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__1));
v___x_11_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__0));
v___x_12_ = l_mkPanicMessageWithDecl(v___x_11_, v___x_10_, v___x_9_, v___x_8_, v___x_7_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1(lean_object* v_b_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; uint8_t v___x_16_; 
v___x_14_ = l_Lean_Expr_bindingBody_x21(v_b_13_);
v___x_15_ = 0;
v___x_16_ = l_Lean_Expr_isHeadBetaTarget(v___x_14_, v___x_15_);
if (v___x_16_ == 0)
{
lean_dec_ref(v___x_14_);
return v_b_13_;
}
else
{
if (lean_obj_tag(v_b_13_) == 6)
{
lean_object* v_binderName_17_; lean_object* v_binderType_18_; lean_object* v_body_19_; uint8_t v_binderInfo_20_; uint8_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___y_25_; size_t v___x_32_; size_t v___x_33_; uint8_t v___x_34_; 
v_binderName_17_ = lean_ctor_get(v_b_13_, 0);
v_binderType_18_ = lean_ctor_get(v_b_13_, 1);
v_body_19_ = lean_ctor_get(v_b_13_, 2);
v_binderInfo_20_ = lean_ctor_get_uint8(v_b_13_, sizeof(void*)*3 + 8);
v___x_21_ = l_Lean_Expr_bindingInfo_x21(v_b_13_);
v___x_22_ = l_Lean_Expr_bindingDomain_x21(v_b_13_);
v___x_23_ = l_Lean_Expr_headBeta(v___x_14_);
v___x_32_ = lean_ptr_addr(v_binderType_18_);
v___x_33_ = lean_ptr_addr(v___x_22_);
v___x_34_ = lean_usize_dec_eq(v___x_32_, v___x_33_);
if (v___x_34_ == 0)
{
v___y_25_ = v___x_34_;
goto v___jp_24_;
}
else
{
size_t v___x_35_; size_t v___x_36_; uint8_t v___x_37_; 
v___x_35_ = lean_ptr_addr(v_body_19_);
v___x_36_ = lean_ptr_addr(v___x_23_);
v___x_37_ = lean_usize_dec_eq(v___x_35_, v___x_36_);
v___y_25_ = v___x_37_;
goto v___jp_24_;
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
lean_object* v___x_26_; 
lean_inc(v_binderName_17_);
lean_dec_ref(v_b_13_);
v___x_26_ = l_Lean_Expr_lam___override(v_binderName_17_, v___x_22_, v___x_23_, v___x_21_);
v_b_13_ = v___x_26_;
goto _start;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_20_, v___x_21_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
lean_inc(v_binderName_17_);
lean_dec_ref(v_b_13_);
v___x_29_ = l_Lean_Expr_lam___override(v_binderName_17_, v___x_22_, v___x_23_, v___x_21_);
v_b_13_ = v___x_29_;
goto _start;
}
else
{
lean_dec_ref(v___x_23_);
lean_dec_ref(v___x_22_);
goto _start;
}
}
}
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec_ref(v___x_14_);
lean_dec_ref(v_b_13_);
v___x_38_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__3);
v___x_39_ = l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(v___x_38_);
v_b_13_ = v___x_39_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_headBetaUnderLambda(lean_object* v_f_41_){
_start:
{
lean_object* v_f_42_; uint8_t v___x_43_; 
v_f_42_ = l_Lean_Expr_headBeta(v_f_41_);
v___x_43_ = l_Lean_Expr_isLambda(v_f_42_);
if (v___x_43_ == 0)
{
return v_f_42_;
}
else
{
lean_object* v___x_44_; 
v___x_44_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1(v_f_42_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(uint8_t v_x_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_47_, 0, v___y_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed(lean_object* v_x_48_, lean_object* v___y_49_){
_start:
{
uint8_t v_x_1555__boxed_50_; lean_object* v_res_51_; 
v_x_1555__boxed_50_ = lean_unbox(v_x_48_);
v_res_51_ = l_Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(v_x_1555__boxed_50_, v___y_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_52_, lean_object* v_vals_53_, lean_object* v_i_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = lean_array_get_size(v_keys_52_);
v___x_57_ = lean_nat_dec_lt(v_i_54_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec(v_i_54_);
v___x_58_ = lean_box(0);
return v___x_58_;
}
else
{
lean_object* v_k_x27_59_; uint8_t v___x_60_; 
v_k_x27_59_ = lean_array_fget_borrowed(v_keys_52_, v_i_54_);
v___x_60_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_55_, v_k_x27_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_i_54_, v___x_61_);
lean_dec(v_i_54_);
v_i_54_ = v___x_62_;
goto _start;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_array_fget_borrowed(v_vals_53_, v_i_54_);
lean_dec(v_i_54_);
lean_inc(v___x_64_);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_66_, lean_object* v_vals_67_, lean_object* v_i_68_, lean_object* v_k_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_keys_66_, v_vals_67_, v_i_68_, v_k_69_);
lean_dec(v_k_69_);
lean_dec_ref(v_vals_67_);
lean_dec_ref(v_keys_66_);
return v_res_70_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; 
v___x_71_ = ((size_t)5ULL);
v___x_72_ = ((size_t)1ULL);
v___x_73_ = lean_usize_shift_left(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; 
v___x_74_ = ((size_t)1ULL);
v___x_75_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
v___x_76_ = lean_usize_sub(v___x_75_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_77_, size_t v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v_es_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
v_es_80_ = lean_ctor_get(v_x_77_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_77_);
if (v_isSharedCheck_101_ == 0)
{
v___x_82_ = v_x_77_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_es_80_);
lean_dec(v_x_77_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v_j_88_; lean_object* v___x_89_; 
v___x_84_ = lean_box(2);
v___x_85_ = ((size_t)5ULL);
v___x_86_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_87_ = lean_usize_land(v_x_78_, v___x_86_);
v_j_88_ = lean_usize_to_nat(v___x_87_);
v___x_89_ = lean_array_get(v___x_84_, v_es_80_, v_j_88_);
lean_dec(v_j_88_);
lean_dec_ref(v_es_80_);
switch(lean_obj_tag(v___x_89_))
{
case 0:
{
lean_object* v_key_90_; lean_object* v_val_91_; uint8_t v___x_92_; 
v_key_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_key_90_);
v_val_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc(v_val_91_);
lean_dec_ref(v___x_89_);
v___x_92_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_79_, v_key_90_);
lean_dec(v_key_90_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec(v_val_91_);
lean_del_object(v___x_82_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_95_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 1);
lean_ctor_set(v___x_82_, 0, v_val_91_);
v___x_95_ = v___x_82_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_val_91_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
case 1:
{
lean_object* v_node_97_; size_t v___x_98_; 
lean_del_object(v___x_82_);
v_node_97_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_node_97_);
lean_dec_ref(v___x_89_);
v___x_98_ = lean_usize_shift_right(v_x_78_, v___x_85_);
v_x_77_ = v_node_97_;
v_x_78_ = v___x_98_;
goto _start;
}
default: 
{
lean_object* v___x_100_; 
lean_del_object(v___x_82_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
}
}
}
else
{
lean_object* v_ks_102_; lean_object* v_vs_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_ks_102_ = lean_ctor_get(v_x_77_, 0);
lean_inc_ref(v_ks_102_);
v_vs_103_ = lean_ctor_get(v_x_77_, 1);
lean_inc_ref(v_vs_103_);
lean_dec_ref(v_x_77_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ks_102_, v_vs_103_, v___x_104_, v_x_79_);
lean_dec_ref(v_vs_103_);
lean_dec_ref(v_ks_102_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
size_t v_x_1594__boxed_109_; lean_object* v_res_110_; 
v_x_1594__boxed_109_ = lean_unbox_usize(v_x_107_);
lean_dec(v_x_107_);
v_res_110_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_106_, v_x_1594__boxed_109_, v_x_108_);
lean_dec(v_x_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint64_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; 
v___x_113_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_112_);
v___x_114_ = lean_uint64_to_usize(v___x_113_);
v___x_115_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_111_, v___x_114_, v_x_112_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_116_, v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_msg_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0);
v___x_122_ = lean_panic_fn(v___x_121_, v_msg_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__10(lean_object* v_vs_123_, lean_object* v_v_124_, lean_object* v_i_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_array_get_size(v_vs_123_);
v___x_127_ = lean_nat_dec_lt(v_i_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_dec(v_i_125_);
v___x_128_ = lean_array_push(v_vs_123_, v_v_124_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_array_fget_borrowed(v_vs_123_, v_i_125_);
v___x_130_ = lean_name_eq(v_v_124_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_add(v_i_125_, v___x_131_);
lean_dec(v_i_125_);
v_i_125_ = v___x_132_;
goto _start;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_array_fset(v_vs_123_, v_i_125_, v_v_124_);
lean_dec(v_i_125_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_vs_135_, lean_object* v_v_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__10(v_vs_135_, v_v_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
lean_object* v_fst_141_; lean_object* v_fst_142_; uint8_t v___x_143_; 
v_fst_141_ = lean_ctor_get(v_a_139_, 0);
v_fst_142_ = lean_ctor_get(v_b_140_, 0);
v___x_143_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_141_, v_fst_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_a_144_, v_b_145_);
lean_dec_ref(v_b_145_);
lean_dec_ref(v_a_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(lean_object* v_x_148_, lean_object* v_keys_149_, lean_object* v_v_150_, lean_object* v_k_151_, lean_object* v_x_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_c_155_; lean_object* v___x_156_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v_x_148_, v___x_153_);
v_c_155_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_149_, v_v_150_, v___x_154_);
lean_dec(v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_k_151_);
lean_ctor_set(v___x_156_, 1, v_c_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_157_, lean_object* v_keys_158_, lean_object* v_v_159_, lean_object* v_k_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_157_, v_keys_158_, v_v_159_, v_k_160_, v_x_161_);
lean_dec_ref(v_keys_158_);
lean_dec(v_x_157_);
return v_res_162_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__0));
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_x_167_, lean_object* v_keys_168_, lean_object* v_v_169_, lean_object* v_k_170_, lean_object* v_as_171_, lean_object* v_k_172_, lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_mid_177_; lean_object* v_midVal_178_; uint8_t v___x_179_; 
v___x_175_ = lean_nat_add(v_x_173_, v_x_174_);
v___x_176_ = lean_unsigned_to_nat(1u);
v_mid_177_ = lean_nat_shiftr(v___x_175_, v___x_176_);
lean_dec(v___x_175_);
v_midVal_178_ = lean_array_fget(v_as_171_, v_mid_177_);
v___x_179_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_midVal_178_, v_k_172_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
lean_dec(v_x_174_);
v___x_180_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_172_, v_midVal_178_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; 
lean_dec(v_x_173_);
v___x_181_ = lean_array_get_size(v_as_171_);
v___x_182_ = lean_nat_dec_lt(v_mid_177_, v___x_181_);
if (v___x_182_ == 0)
{
lean_dec(v_midVal_178_);
lean_dec(v_mid_177_);
lean_dec(v_k_170_);
lean_dec(v_v_169_);
return v_as_171_;
}
else
{
lean_object* v_snd_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_195_; 
v_snd_183_ = lean_ctor_get(v_midVal_178_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_midVal_178_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_midVal_178_, 0);
lean_dec(v_unused_196_);
v___x_185_ = v_midVal_178_;
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_snd_183_);
lean_dec(v_midVal_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v_xs_x27_188_; lean_object* v___x_189_; lean_object* v_c_190_; lean_object* v___x_192_; 
v___x_187_ = lean_box(0);
v_xs_x27_188_ = lean_array_fset(v_as_171_, v_mid_177_, v___x_187_);
v___x_189_ = lean_nat_add(v_x_167_, v___x_176_);
v_c_190_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2(v_keys_168_, v_v_169_, v___x_189_, v_snd_183_);
lean_dec(v___x_189_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v_c_190_);
lean_ctor_set(v___x_185_, 0, v_k_170_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_c_190_);
v___x_192_ = v_reuseFailAlloc_194_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; 
v___x_193_ = lean_array_fset(v_xs_x27_188_, v_mid_177_, v___x_192_);
lean_dec(v_mid_177_);
return v___x_193_;
}
}
}
}
else
{
lean_dec(v_midVal_178_);
v_x_174_ = v_mid_177_;
goto _start;
}
}
else
{
uint8_t v___x_198_; 
lean_dec(v_midVal_178_);
v___x_198_ = lean_nat_dec_eq(v_mid_177_, v_x_173_);
if (v___x_198_ == 0)
{
lean_dec(v_x_173_);
v_x_173_ = v_mid_177_;
goto _start;
}
else
{
lean_object* v___x_200_; lean_object* v_c_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_j_204_; lean_object* v_as_205_; lean_object* v___x_206_; 
lean_dec(v_mid_177_);
lean_dec(v_x_174_);
v___x_200_ = lean_nat_add(v_x_167_, v___x_176_);
v_c_201_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_168_, v_v_169_, v___x_200_);
lean_dec(v___x_200_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_k_170_);
lean_ctor_set(v___x_202_, 1, v_c_201_);
v___x_203_ = lean_nat_add(v_x_173_, v___x_176_);
lean_dec(v_x_173_);
v_j_204_ = lean_array_get_size(v_as_171_);
v_as_205_ = lean_array_push(v_as_171_, v___x_202_);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_203_, v_as_205_, v_j_204_);
lean_dec(v___x_203_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6(lean_object* v_x_207_, lean_object* v_keys_208_, lean_object* v_v_209_, lean_object* v_k_210_, lean_object* v_as_211_, lean_object* v_k_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = lean_array_get_size(v_as_211_);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_eq(v___x_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_array_fget_borrowed(v_as_211_, v___x_214_);
v___x_217_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_212_, v___x_216_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
v___x_218_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_216_, v_k_212_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; 
v___x_219_ = lean_nat_dec_lt(v___x_214_, v___x_213_);
if (v___x_219_ == 0)
{
lean_dec(v_k_210_);
lean_dec(v_v_209_);
return v_as_211_;
}
else
{
lean_object* v___x_220_; lean_object* v_xs_x27_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_inc(v___x_216_);
v___x_220_ = lean_box(0);
v_xs_x27_221_ = lean_array_fset(v_as_211_, v___x_214_, v___x_220_);
v___x_222_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_207_, v_keys_208_, v_v_209_, v_k_210_, v___x_216_);
v___x_223_ = lean_array_fset(v_xs_x27_221_, v___x_214_, v___x_222_);
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_sub(v___x_213_, v___x_224_);
v___x_226_ = lean_array_fget_borrowed(v_as_211_, v___x_225_);
v___x_227_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_226_, v_k_212_);
if (v___x_227_ == 0)
{
uint8_t v___x_228_; 
v___x_228_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_212_, v___x_226_);
if (v___x_228_ == 0)
{
uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_lt(v___x_225_, v___x_213_);
if (v___x_229_ == 0)
{
lean_dec(v___x_225_);
lean_dec(v_k_210_);
lean_dec(v_v_209_);
return v_as_211_;
}
else
{
lean_object* v___x_230_; lean_object* v_xs_x27_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_inc(v___x_226_);
v___x_230_ = lean_box(0);
v_xs_x27_231_ = lean_array_fset(v_as_211_, v___x_225_, v___x_230_);
v___x_232_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_207_, v_keys_208_, v_v_209_, v_k_210_, v___x_226_);
v___x_233_ = lean_array_fset(v_xs_x27_231_, v___x_225_, v___x_232_);
lean_dec(v___x_225_);
return v___x_233_;
}
}
else
{
lean_object* v___x_234_; 
v___x_234_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_207_, v_keys_208_, v_v_209_, v_k_210_, v_as_211_, v_k_212_, v___x_214_, v___x_225_);
return v___x_234_;
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v___x_225_);
v___x_235_ = lean_box(0);
v___x_236_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_207_, v_keys_208_, v_v_209_, v_k_210_, v___x_235_);
v___x_237_ = lean_array_push(v_as_211_, v___x_236_);
return v___x_237_;
}
}
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_as_240_; lean_object* v___x_241_; 
v___x_238_ = lean_box(0);
v___x_239_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_207_, v_keys_208_, v_v_209_, v_k_210_, v___x_238_);
v_as_240_ = lean_array_push(v_as_211_, v___x_239_);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_214_, v_as_240_, v___x_213_);
return v___x_241_;
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_box(0);
v___x_243_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_207_, v_keys_208_, v_v_209_, v_k_210_, v___x_242_);
v___x_244_ = lean_array_push(v_as_211_, v___x_243_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_keys_245_, lean_object* v_v_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_vs_249_; lean_object* v_children_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_267_; 
v_vs_249_ = lean_ctor_get(v_x_248_, 0);
v_children_250_ = lean_ctor_get(v_x_248_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_267_ == 0)
{
v___x_252_ = v_x_248_;
v_isShared_253_ = v_isSharedCheck_267_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_children_250_);
lean_inc(v_vs_249_);
lean_dec(v_x_248_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_267_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_array_get_size(v_keys_245_);
v___x_255_ = lean_nat_dec_lt(v_x_247_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_vs_249_, v_v_246_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_256_);
v___x_258_ = v___x_252_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_children_250_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
else
{
lean_object* v_k_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_c_263_; lean_object* v___x_265_; 
v_k_260_ = lean_array_fget_borrowed(v_keys_245_, v_x_247_);
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__1);
lean_inc(v_k_260_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_k_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_inc(v_k_260_);
v_c_263_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_247_, v_keys_245_, v_v_246_, v_k_260_, v_children_250_, v___x_262_);
lean_dec_ref(v___x_262_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_c_263_);
v___x_265_ = v___x_252_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_vs_249_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_c_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(lean_object* v_x_268_, lean_object* v_keys_269_, lean_object* v_v_270_, lean_object* v_k_271_, lean_object* v_x_272_){
_start:
{
lean_object* v_snd_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_283_; 
v_snd_273_ = lean_ctor_get(v_x_272_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_272_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_x_272_, 0);
lean_dec(v_unused_284_);
v___x_275_ = v_x_272_;
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_snd_273_);
lean_dec(v_x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_c_279_; lean_object* v___x_281_; 
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_x_268_, v___x_277_);
v_c_279_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2(v_keys_269_, v_v_270_, v___x_278_, v_snd_273_);
lean_dec(v___x_278_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_c_279_);
lean_ctor_set(v___x_275_, 0, v_k_271_);
v___x_281_ = v___x_275_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_k_271_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_c_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_285_, lean_object* v_keys_286_, lean_object* v_v_287_, lean_object* v_k_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_285_, v_keys_286_, v_v_287_, v_k_288_, v_x_289_);
lean_dec_ref(v_keys_286_);
lean_dec(v_x_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_keys_291_, lean_object* v_v_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2(v_keys_291_, v_v_292_, v_x_293_, v_x_294_);
lean_dec(v_x_293_);
lean_dec_ref(v_keys_291_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_x_296_, lean_object* v_keys_297_, lean_object* v_v_298_, lean_object* v_k_299_, lean_object* v_as_300_, lean_object* v_k_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_296_, v_keys_297_, v_v_298_, v_k_299_, v_as_300_, v_k_301_, v_x_302_, v_x_303_);
lean_dec_ref(v_k_301_);
lean_dec_ref(v_keys_297_);
lean_dec(v_x_296_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(lean_object* v_x_305_, lean_object* v_keys_306_, lean_object* v_v_307_, lean_object* v_k_308_, lean_object* v_as_309_, lean_object* v_k_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_305_, v_keys_306_, v_v_307_, v_k_308_, v_as_309_, v_k_310_);
lean_dec_ref(v_k_310_);
lean_dec_ref(v_keys_306_);
lean_dec(v_x_305_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v_ks_316_; lean_object* v_vs_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_341_; 
v_ks_316_ = lean_ctor_get(v_x_312_, 0);
v_vs_317_ = lean_ctor_get(v_x_312_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_312_);
if (v_isSharedCheck_341_ == 0)
{
v___x_319_ = v_x_312_;
v_isShared_320_ = v_isSharedCheck_341_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_vs_317_);
lean_inc(v_ks_316_);
lean_dec(v_x_312_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_341_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_array_get_size(v_ks_316_);
v___x_322_ = lean_nat_dec_lt(v_x_313_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
lean_dec(v_x_313_);
v___x_323_ = lean_array_push(v_ks_316_, v_x_314_);
v___x_324_ = lean_array_push(v_vs_317_, v_x_315_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_324_);
lean_ctor_set(v___x_319_, 0, v___x_323_);
v___x_326_ = v___x_319_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
else
{
lean_object* v_k_x27_328_; uint8_t v___x_329_; 
v_k_x27_328_ = lean_array_fget_borrowed(v_ks_316_, v_x_313_);
v___x_329_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_314_, v_k_x27_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_331_; 
if (v_isShared_320_ == 0)
{
v___x_331_ = v___x_319_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_ks_316_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_vs_317_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_x_313_, v___x_332_);
lean_dec(v_x_313_);
v_x_312_ = v___x_331_;
v_x_313_ = v___x_333_;
goto _start;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_array_fset(v_ks_316_, v_x_313_, v_x_314_);
v___x_337_ = lean_array_fset(v_vs_317_, v_x_313_, v_x_315_);
lean_dec(v_x_313_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_337_);
lean_ctor_set(v___x_319_, 0, v___x_336_);
v___x_339_ = v___x_319_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_n_342_, lean_object* v_k_343_, lean_object* v_v_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_342_, v___x_345_, v_k_343_, v_v_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_348_, size_t v_x_349_, size_t v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v_es_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v_j_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_es_353_ = lean_ctor_get(v_x_348_, 0);
v___x_354_ = ((size_t)5ULL);
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_357_ = lean_usize_land(v_x_349_, v___x_356_);
v_j_358_ = lean_usize_to_nat(v___x_357_);
v___x_359_ = lean_array_get_size(v_es_353_);
v___x_360_ = lean_nat_dec_lt(v_j_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_dec(v_j_358_);
lean_dec(v_x_352_);
lean_dec(v_x_351_);
return v_x_348_;
}
else
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_397_; 
lean_inc_ref(v_es_353_);
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_x_348_, 0);
lean_dec(v_unused_398_);
v___x_362_ = v_x_348_;
v_isShared_363_ = v_isSharedCheck_397_;
goto v_resetjp_361_;
}
else
{
lean_dec(v_x_348_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_397_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_v_364_; lean_object* v___x_365_; lean_object* v_xs_x27_366_; lean_object* v___y_368_; 
v_v_364_ = lean_array_fget(v_es_353_, v_j_358_);
v___x_365_ = lean_box(0);
v_xs_x27_366_ = lean_array_fset(v_es_353_, v_j_358_, v___x_365_);
switch(lean_obj_tag(v_v_364_))
{
case 0:
{
lean_object* v_key_373_; lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_384_; 
v_key_373_ = lean_ctor_get(v_v_364_, 0);
v_val_374_ = lean_ctor_get(v_v_364_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_v_364_);
if (v_isSharedCheck_384_ == 0)
{
v___x_376_ = v_v_364_;
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_inc(v_key_373_);
lean_dec(v_v_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_351_, v_key_373_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_del_object(v___x_376_);
v___x_379_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_373_, v_val_374_, v_x_351_, v_x_352_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___y_368_ = v___x_380_;
goto v___jp_367_;
}
else
{
lean_object* v___x_382_; 
lean_dec(v_val_374_);
lean_dec(v_key_373_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v_x_352_);
lean_ctor_set(v___x_376_, 0, v_x_351_);
v___x_382_ = v___x_376_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_x_351_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_x_352_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
v___y_368_ = v___x_382_;
goto v___jp_367_;
}
}
}
}
case 1:
{
lean_object* v_node_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_395_; 
v_node_385_ = lean_ctor_get(v_v_364_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v_v_364_);
if (v_isSharedCheck_395_ == 0)
{
v___x_387_ = v_v_364_;
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_node_385_);
lean_dec(v_v_364_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_389_ = lean_usize_shift_right(v_x_349_, v___x_354_);
v___x_390_ = lean_usize_add(v_x_350_, v___x_355_);
v___x_391_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_node_385_, v___x_389_, v___x_390_, v_x_351_, v_x_352_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_391_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v___y_368_ = v___x_393_;
goto v___jp_367_;
}
}
}
default: 
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_x_351_);
lean_ctor_set(v___x_396_, 1, v_x_352_);
v___y_368_ = v___x_396_;
goto v___jp_367_;
}
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_array_fset(v_xs_x27_366_, v_j_358_, v___y_368_);
lean_dec(v_j_358_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_369_);
v___x_371_ = v___x_362_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
else
{
lean_object* v_ks_399_; lean_object* v_vs_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_420_; 
v_ks_399_ = lean_ctor_get(v_x_348_, 0);
v_vs_400_ = lean_ctor_get(v_x_348_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_420_ == 0)
{
v___x_402_ = v_x_348_;
v_isShared_403_ = v_isSharedCheck_420_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_vs_400_);
lean_inc(v_ks_399_);
lean_dec(v_x_348_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_420_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_ks_399_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_vs_400_);
v___x_405_ = v_reuseFailAlloc_419_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v_newNode_406_; uint8_t v___y_408_; size_t v___x_414_; uint8_t v___x_415_; 
v_newNode_406_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(v___x_405_, v_x_351_, v_x_352_);
v___x_414_ = ((size_t)7ULL);
v___x_415_ = lean_usize_dec_le(v___x_414_, v_x_350_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_406_);
v___x_417_ = lean_unsigned_to_nat(4u);
v___x_418_ = lean_nat_dec_lt(v___x_416_, v___x_417_);
lean_dec(v___x_416_);
v___y_408_ = v___x_418_;
goto v___jp_407_;
}
else
{
v___y_408_ = v___x_415_;
goto v___jp_407_;
}
v___jp_407_:
{
if (v___y_408_ == 0)
{
lean_object* v_ks_409_; lean_object* v_vs_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_ks_409_ = lean_ctor_get(v_newNode_406_, 0);
lean_inc_ref(v_ks_409_);
v_vs_410_ = lean_ctor_get(v_newNode_406_, 1);
lean_inc_ref(v_vs_410_);
lean_dec_ref(v_newNode_406_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0);
v___x_413_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_x_350_, v_ks_409_, v_vs_410_, v___x_411_, v___x_412_);
lean_dec_ref(v_vs_410_);
lean_dec_ref(v_ks_409_);
return v___x_413_;
}
else
{
return v_newNode_406_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(size_t v_depth_421_, lean_object* v_keys_422_, lean_object* v_vals_423_, lean_object* v_i_424_, lean_object* v_entries_425_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_array_get_size(v_keys_422_);
v___x_427_ = lean_nat_dec_lt(v_i_424_, v___x_426_);
if (v___x_427_ == 0)
{
lean_dec(v_i_424_);
return v_entries_425_;
}
else
{
lean_object* v_k_428_; lean_object* v_v_429_; uint64_t v___x_430_; size_t v_h_431_; size_t v___x_432_; lean_object* v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v_h_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_k_428_ = lean_array_fget_borrowed(v_keys_422_, v_i_424_);
v_v_429_ = lean_array_fget_borrowed(v_vals_423_, v_i_424_);
v___x_430_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_428_);
v_h_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = ((size_t)5ULL);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_sub(v_depth_421_, v___x_434_);
v___x_436_ = lean_usize_mul(v___x_432_, v___x_435_);
v_h_437_ = lean_usize_shift_right(v_h_431_, v___x_436_);
v___x_438_ = lean_nat_add(v_i_424_, v___x_433_);
lean_dec(v_i_424_);
lean_inc(v_v_429_);
lean_inc(v_k_428_);
v___x_439_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_entries_425_, v_h_437_, v_depth_421_, v_k_428_, v_v_429_);
v_i_424_ = v___x_438_;
v_entries_425_ = v___x_439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_441_, lean_object* v_keys_442_, lean_object* v_vals_443_, lean_object* v_i_444_, lean_object* v_entries_445_){
_start:
{
size_t v_depth_boxed_446_; lean_object* v_res_447_; 
v_depth_boxed_446_ = lean_unbox_usize(v_depth_441_);
lean_dec(v_depth_441_);
v_res_447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_446_, v_keys_442_, v_vals_443_, v_i_444_, v_entries_445_);
lean_dec_ref(v_vals_443_);
lean_dec_ref(v_keys_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
size_t v_x_2000__boxed_453_; size_t v_x_2001__boxed_454_; lean_object* v_res_455_; 
v_x_2000__boxed_453_ = lean_unbox_usize(v_x_449_);
lean_dec(v_x_449_);
v_x_2001__boxed_454_ = lean_unbox_usize(v_x_450_);
lean_dec(v_x_450_);
v_res_455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_448_, v_x_2000__boxed_453_, v_x_2001__boxed_454_, v_x_451_, v_x_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
uint64_t v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v___x_459_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_457_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_456_, v___x_460_, v___x_461_, v_x_457_, v_x_458_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__3(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__2));
v___x_467_ = lean_unsigned_to_nat(23u);
v___x_468_ = lean_unsigned_to_nat(166u);
v___x_469_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__1));
v___x_470_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__0));
v___x_471_ = l_mkPanicMessageWithDecl(v___x_470_, v___x_469_, v___x_468_, v___x_467_, v___x_466_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0(lean_object* v_d_472_, lean_object* v_keys_473_, lean_object* v_v_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_475_ = lean_array_get_size(v_keys_473_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_nat_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v_k_479_; lean_object* v___x_480_; 
v___x_478_ = lean_box(0);
v_k_479_ = lean_array_get_borrowed(v___x_478_, v_keys_473_, v___x_476_);
lean_inc_ref(v_d_472_);
v___x_480_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___redArg(v_d_472_, v_k_479_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_481_; lean_object* v_c_482_; lean_object* v___x_483_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v_c_482_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_473_, v_v_474_, v___x_481_);
lean_inc(v_k_479_);
v___x_483_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_472_, v_k_479_, v_c_482_);
return v___x_483_;
}
else
{
lean_object* v_val_484_; lean_object* v___x_485_; lean_object* v_c_486_; lean_object* v___x_487_; 
v_val_484_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_val_484_);
lean_dec_ref(v___x_480_);
v___x_485_ = lean_unsigned_to_nat(1u);
v_c_486_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2(v_keys_473_, v_v_474_, v___x_485_, v_val_484_);
lean_inc(v_k_479_);
v___x_487_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_472_, v_k_479_, v_c_486_);
return v___x_487_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_v_474_);
lean_dec_ref(v_d_472_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___closed__3);
v___x_489_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3(v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_490_, lean_object* v_keys_491_, lean_object* v_v_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0(v_d_490_, v_keys_491_, v_v_492_);
lean_dec_ref(v_keys_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(lean_object* v_dt_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; 
v_fst_496_ = lean_ctor_get(v_x_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v_x_495_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v_x_495_);
v___x_498_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0(v_dt_494_, v_snd_497_, v_fst_496_);
lean_dec(v_snd_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(lean_object* v___y_499_){
_start:
{
lean_inc_ref(v___y_499_);
return v___y_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed(lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(v___y_500_);
lean_dec_ref(v___y_500_);
return v_res_501_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_, &l_Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__once, _init_l_Lean_Meta_Monotonicity_initFn___closed__8_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___f_517_ = ((lean_object*)(l_Lean_Meta_Monotonicity_initFn___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_));
v___f_518_ = ((lean_object*)(l_Lean_Meta_Monotonicity_initFn___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_));
v___x_519_ = lean_obj_once(&l_Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_, &l_Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__once, _init_l_Lean_Meta_Monotonicity_initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_);
v___f_520_ = ((lean_object*)(l_Lean_Meta_Monotonicity_initFn___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_));
v___x_521_ = ((lean_object*)(l_Lean_Meta_Monotonicity_initFn___closed__7_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_));
v___x_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___f_520_);
lean_ctor_set(v___x_522_, 2, v___x_519_);
lean_ctor_set(v___x_522_, 3, v___f_518_);
lean_ctor_set(v___x_522_, 4, v___f_517_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_, &l_Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__once, _init_l_Lean_Meta_Monotonicity_initFn___closed__10_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_);
v___x_525_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2____boxed(lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_();
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_532_, v_x_533_, v_x_534_);
lean_dec(v_x_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_536_, lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_537_, v_x_538_, v_x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_541_, lean_object* v_x_542_, size_t v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_542_, v_x_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_546_, lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
size_t v_x_2318__boxed_550_; lean_object* v_res_551_; 
v_x_2318__boxed_550_ = lean_unbox_usize(v_x_548_);
lean_dec(v_x_548_);
v_res_551_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_546_, v_x_547_, v_x_2318__boxed_550_, v_x_549_);
lean_dec(v_x_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b2_552_, lean_object* v_x_553_, size_t v_x_554_, size_t v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_553_, v_x_554_, v_x_555_, v_x_556_, v_x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
size_t v_x_2329__boxed_565_; size_t v_x_2330__boxed_566_; lean_object* v_res_567_; 
v_x_2329__boxed_565_ = lean_unbox_usize(v_x_561_);
lean_dec(v_x_561_);
v_x_2330__boxed_566_ = lean_unbox_usize(v_x_562_);
lean_dec(v_x_562_);
v_res_567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_559_, v_x_560_, v_x_2329__boxed_565_, v_x_2330__boxed_566_, v_x_563_, v_x_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_568_, lean_object* v_keys_569_, lean_object* v_vals_570_, lean_object* v_heq_571_, lean_object* v_i_572_, lean_object* v_k_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_keys_569_, v_vals_570_, v_i_572_, v_k_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_575_, lean_object* v_keys_576_, lean_object* v_vals_577_, lean_object* v_heq_578_, lean_object* v_i_579_, lean_object* v_k_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_575_, v_keys_576_, v_vals_577_, v_heq_578_, v_i_579_, v_k_580_);
lean_dec(v_k_580_);
lean_dec_ref(v_vals_577_);
lean_dec_ref(v_keys_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_582_, lean_object* v_n_583_, lean_object* v_k_584_, lean_object* v_v_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(v_n_583_, v_k_584_, v_v_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_587_, size_t v_depth_588_, lean_object* v_keys_589_, lean_object* v_vals_590_, lean_object* v_heq_591_, lean_object* v_i_592_, lean_object* v_entries_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_depth_588_, v_keys_589_, v_vals_590_, v_i_592_, v_entries_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_595_, lean_object* v_depth_596_, lean_object* v_keys_597_, lean_object* v_vals_598_, lean_object* v_heq_599_, lean_object* v_i_600_, lean_object* v_entries_601_){
_start:
{
size_t v_depth_boxed_602_; lean_object* v_res_603_; 
v_depth_boxed_602_ = lean_unbox_usize(v_depth_596_);
lean_dec(v_depth_596_);
v_res_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(v_00_u03b2_595_, v_depth_boxed_602_, v_keys_597_, v_vals_598_, v_heq_599_, v_i_600_, v_entries_601_);
lean_dec_ref(v_vals_598_);
lean_dec_ref(v_keys_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12(lean_object* v_x_604_, lean_object* v_keys_605_, lean_object* v_v_606_, lean_object* v_k_607_, lean_object* v_as_608_, lean_object* v_k_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_604_, v_keys_605_, v_v_606_, v_k_607_, v_as_608_, v_k_609_, v_x_610_, v_x_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_x_615_, lean_object* v_keys_616_, lean_object* v_v_617_, lean_object* v_k_618_, lean_object* v_as_619_, lean_object* v_k_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12(v_x_615_, v_keys_616_, v_v_617_, v_k_618_, v_as_619_, v_k_620_, v_x_621_, v_x_622_, v_x_623_, v_x_624_);
lean_dec_ref(v_k_620_);
lean_dec_ref(v_keys_616_);
lean_dec(v_x_615_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_627_, v_x_628_, v_x_629_, v_x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_632_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_638_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
lean_ctor_set(v___x_638_, 3, v___x_637_);
lean_ctor_set(v___x_638_, 4, v___x_637_);
lean_ctor_set(v___x_638_, 5, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg(lean_object* v_ext_639_, lean_object* v_b_640_, uint8_t v_kind_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_currNamespace_646_; lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v_nextMacroScope_649_; lean_object* v_ngen_650_; lean_object* v_auxDeclNGen_651_; lean_object* v_traceState_652_; lean_object* v_messages_653_; lean_object* v_infoState_654_; lean_object* v_snapshotTasks_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_682_; 
v_currNamespace_646_ = lean_ctor_get(v___y_643_, 6);
lean_inc(v_currNamespace_646_);
lean_dec_ref(v___y_643_);
v___x_647_ = lean_st_ref_take(v___y_644_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
v_nextMacroScope_649_ = lean_ctor_get(v___x_647_, 1);
v_ngen_650_ = lean_ctor_get(v___x_647_, 2);
v_auxDeclNGen_651_ = lean_ctor_get(v___x_647_, 3);
v_traceState_652_ = lean_ctor_get(v___x_647_, 4);
v_messages_653_ = lean_ctor_get(v___x_647_, 6);
v_infoState_654_ = lean_ctor_get(v___x_647_, 7);
v_snapshotTasks_655_ = lean_ctor_get(v___x_647_, 8);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_647_, 5);
lean_dec(v_unused_683_);
v___x_657_ = v___x_647_;
v_isShared_658_ = v_isSharedCheck_682_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snapshotTasks_655_);
lean_inc(v_infoState_654_);
lean_inc(v_messages_653_);
lean_inc(v_traceState_652_);
lean_inc(v_auxDeclNGen_651_);
lean_inc(v_ngen_650_);
lean_inc(v_nextMacroScope_649_);
lean_inc(v_env_648_);
lean_dec(v___x_647_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_682_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_659_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_648_, v_ext_639_, v_b_640_, v_kind_641_, v_currNamespace_646_);
v___x_660_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 5, v___x_660_);
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_nextMacroScope_649_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_ngen_650_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_auxDeclNGen_651_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_traceState_652_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_messages_653_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v_infoState_654_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v_snapshotTasks_655_);
v___x_662_ = v_reuseFailAlloc_681_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_mctx_665_; lean_object* v_zetaDeltaFVarIds_666_; lean_object* v_postponed_667_; lean_object* v_diag_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_679_; 
v___x_663_ = lean_st_ref_set(v___y_644_, v___x_662_);
v___x_664_ = lean_st_ref_take(v___y_642_);
v_mctx_665_ = lean_ctor_get(v___x_664_, 0);
v_zetaDeltaFVarIds_666_ = lean_ctor_get(v___x_664_, 2);
v_postponed_667_ = lean_ctor_get(v___x_664_, 3);
v_diag_668_ = lean_ctor_get(v___x_664_, 4);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_664_, 1);
lean_dec(v_unused_680_);
v___x_670_ = v___x_664_;
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_diag_668_);
lean_inc(v_postponed_667_);
lean_inc(v_zetaDeltaFVarIds_666_);
lean_inc(v_mctx_665_);
lean_dec(v___x_664_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_mctx_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_zetaDeltaFVarIds_666_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_postponed_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_diag_668_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_st_ref_set(v___y_642_, v___x_674_);
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_ext_684_, lean_object* v_b_685_, lean_object* v_kind_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_kind_boxed_691_; lean_object* v_res_692_; 
v_kind_boxed_691_ = lean_unbox(v_kind_686_);
v_res_692_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg(v_ext_684_, v_b_685_, v_kind_boxed_691_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec(v___y_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_693_, lean_object* v_00_u03b2_694_, lean_object* v_00_u03c3_695_, lean_object* v_ext_696_, lean_object* v_b_697_, uint8_t v_kind_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg(v_ext_696_, v_b_697_, v_kind_698_, v___y_700_, v___y_701_, v___y_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_00_u03c3_707_, lean_object* v_ext_708_, lean_object* v_b_709_, lean_object* v_kind_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v_kind_boxed_716_; lean_object* v_res_717_; 
v_kind_boxed_716_ = lean_unbox(v_kind_710_);
v_res_717_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1(v_00_u03b1_705_, v_00_u03b2_706_, v_00_u03c3_707_, v_ext_708_, v_b_709_, v_kind_boxed_716_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v_k_718_, lean_object* v_b_719_, lean_object* v_c_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_apply_7(v_k_718_, v_b_719_, v_c_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, lean_box(0));
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v_k_727_, lean_object* v_b_728_, lean_object* v_c_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_727_, v_b_728_, v_c_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg(lean_object* v_e_736_, lean_object* v_maxFVars_737_, lean_object* v_k_738_, uint8_t v_cleanupAnnotations_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___f_745_; uint8_t v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_745_, 0, v_k_738_);
v___x_746_ = 1;
v___x_747_ = 0;
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_maxFVars_737_);
v___x_749_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_736_, v___x_746_, v___x_747_, v___x_746_, v___x_747_, v___x_748_, v___f_745_, v_cleanupAnnotations_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec_ref(v___x_748_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_749_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_749_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_e_766_, lean_object* v_maxFVars_767_, lean_object* v_k_768_, lean_object* v_cleanupAnnotations_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_775_; lean_object* v_res_776_; 
v_cleanupAnnotations_boxed_775_ = lean_unbox(v_cleanupAnnotations_769_);
v_res_776_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg(v_e_766_, v_maxFVars_767_, v_k_768_, v_cleanupAnnotations_boxed_775_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b1_777_, lean_object* v_e_778_, lean_object* v_maxFVars_779_, lean_object* v_k_780_, uint8_t v_cleanupAnnotations_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg(v_e_778_, v_maxFVars_779_, v_k_780_, v_cleanupAnnotations_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b1_788_, lean_object* v_e_789_, lean_object* v_maxFVars_790_, lean_object* v_k_791_, lean_object* v_cleanupAnnotations_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_798_; lean_object* v_res_799_; 
v_cleanupAnnotations_boxed_798_ = lean_unbox(v_cleanupAnnotations_792_);
v_res_799_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2(v_00_u03b1_788_, v_e_789_, v_maxFVars_790_, v_k_791_, v_cleanupAnnotations_boxed_798_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v_env_807_; lean_object* v___x_808_; lean_object* v_mctx_809_; lean_object* v_lctx_810_; lean_object* v_options_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_806_ = lean_st_ref_get(v___y_804_);
v_env_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref(v_env_807_);
lean_dec(v___x_806_);
v___x_808_ = lean_st_ref_get(v___y_802_);
v_mctx_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_ref(v_mctx_809_);
lean_dec(v___x_808_);
v_lctx_810_ = lean_ctor_get(v___y_801_, 2);
v_options_811_ = lean_ctor_get(v___y_803_, 2);
lean_inc_ref(v_options_811_);
lean_inc_ref(v_lctx_810_);
v___x_812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_812_, 0, v_env_807_);
lean_ctor_set(v___x_812_, 1, v_mctx_809_);
lean_ctor_set(v___x_812_, 2, v_lctx_810_);
lean_ctor_set(v___x_812_, 3, v_options_811_);
v___x_813_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_msgData_800_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0(v_msgData_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_ref_828_; lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_ref_828_ = lean_ctor_get(v___y_825_, 5);
v___x_829_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0(v_msg_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_ref_828_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_ref_828_);
lean_ctor_set(v___x_834_, 1, v_a_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 1);
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v_msg_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_848_ = l_Lean_stringToMessageData(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v___x_851_, lean_object* v_x_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_858_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_860_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_861_ = l_Lean_Name_mkStr3(v___x_851_, v___x_859_, v___x_860_);
v___x_862_ = 0;
v___x_863_ = l_Lean_MessageData_ofConstName(v___x_861_, v___x_862_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_858_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_864_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v___x_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___x_866_, v_x_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_873_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_874_; uint64_t v___x_875_; 
v___x_874_ = 2;
v___x_875_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v_decl_876_, uint8_t v_kind_877_, lean_object* v_x_878_, lean_object* v_e_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; uint8_t v_foApprox_886_; uint8_t v_ctxApprox_887_; uint8_t v_quasiPatternApprox_888_; uint8_t v_constApprox_889_; uint8_t v_isDefEqStuckEx_890_; uint8_t v_unificationHints_891_; uint8_t v_proofIrrelevance_892_; uint8_t v_assignSyntheticOpaque_893_; uint8_t v_offsetCnstrs_894_; uint8_t v_etaStruct_895_; uint8_t v_univApprox_896_; uint8_t v_iota_897_; uint8_t v_beta_898_; uint8_t v_proj_899_; uint8_t v_zeta_900_; uint8_t v_zetaDelta_901_; uint8_t v_zetaUnused_902_; uint8_t v_zetaHave_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_956_; 
v___x_885_ = l_Lean_Meta_Context_config(v___y_880_);
v_foApprox_886_ = lean_ctor_get_uint8(v___x_885_, 0);
v_ctxApprox_887_ = lean_ctor_get_uint8(v___x_885_, 1);
v_quasiPatternApprox_888_ = lean_ctor_get_uint8(v___x_885_, 2);
v_constApprox_889_ = lean_ctor_get_uint8(v___x_885_, 3);
v_isDefEqStuckEx_890_ = lean_ctor_get_uint8(v___x_885_, 4);
v_unificationHints_891_ = lean_ctor_get_uint8(v___x_885_, 5);
v_proofIrrelevance_892_ = lean_ctor_get_uint8(v___x_885_, 6);
v_assignSyntheticOpaque_893_ = lean_ctor_get_uint8(v___x_885_, 7);
v_offsetCnstrs_894_ = lean_ctor_get_uint8(v___x_885_, 8);
v_etaStruct_895_ = lean_ctor_get_uint8(v___x_885_, 10);
v_univApprox_896_ = lean_ctor_get_uint8(v___x_885_, 11);
v_iota_897_ = lean_ctor_get_uint8(v___x_885_, 12);
v_beta_898_ = lean_ctor_get_uint8(v___x_885_, 13);
v_proj_899_ = lean_ctor_get_uint8(v___x_885_, 14);
v_zeta_900_ = lean_ctor_get_uint8(v___x_885_, 15);
v_zetaDelta_901_ = lean_ctor_get_uint8(v___x_885_, 16);
v_zetaUnused_902_ = lean_ctor_get_uint8(v___x_885_, 17);
v_zetaHave_903_ = lean_ctor_get_uint8(v___x_885_, 18);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_956_ == 0)
{
v___x_905_ = v___x_885_;
v_isShared_906_ = v_isSharedCheck_956_;
goto v_resetjp_904_;
}
else
{
lean_dec(v___x_885_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_956_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
uint8_t v_trackZetaDelta_907_; lean_object* v_zetaDeltaSet_908_; lean_object* v_lctx_909_; lean_object* v_localInstances_910_; lean_object* v_defEqCtx_x3f_911_; lean_object* v_synthPendingDepth_912_; lean_object* v_canUnfold_x3f_913_; uint8_t v_univApprox_914_; uint8_t v_inTypeClassResolution_915_; uint8_t v_cacheInferType_916_; uint8_t v___x_917_; lean_object* v_config_919_; 
v_trackZetaDelta_907_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*7);
v_zetaDeltaSet_908_ = lean_ctor_get(v___y_880_, 1);
lean_inc(v_zetaDeltaSet_908_);
v_lctx_909_ = lean_ctor_get(v___y_880_, 2);
lean_inc_ref(v_lctx_909_);
v_localInstances_910_ = lean_ctor_get(v___y_880_, 3);
lean_inc_ref(v_localInstances_910_);
v_defEqCtx_x3f_911_ = lean_ctor_get(v___y_880_, 4);
lean_inc(v_defEqCtx_x3f_911_);
v_synthPendingDepth_912_ = lean_ctor_get(v___y_880_, 5);
lean_inc(v_synthPendingDepth_912_);
v_canUnfold_x3f_913_ = lean_ctor_get(v___y_880_, 6);
lean_inc(v_canUnfold_x3f_913_);
v_univApprox_914_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_915_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*7 + 2);
v_cacheInferType_916_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*7 + 3);
v___x_917_ = 2;
if (v_isShared_906_ == 0)
{
v_config_919_ = v___x_905_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 0, v_foApprox_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 1, v_ctxApprox_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 2, v_quasiPatternApprox_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 3, v_constApprox_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 4, v_isDefEqStuckEx_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 5, v_unificationHints_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 6, v_proofIrrelevance_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 7, v_assignSyntheticOpaque_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 8, v_offsetCnstrs_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 10, v_etaStruct_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 11, v_univApprox_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 12, v_iota_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 13, v_beta_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 14, v_proj_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 15, v_zeta_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 16, v_zetaDelta_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 17, v_zetaUnused_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, 18, v_zetaHave_903_);
v_config_919_ = v_reuseFailAlloc_955_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
uint64_t v___x_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_947_; 
lean_ctor_set_uint8(v_config_919_, 9, v___x_917_);
v___x_920_ = l_Lean_Meta_Context_configKey(v___y_880_);
v_isSharedCheck_947_ = !lean_is_exclusive(v___y_880_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; 
v_unused_948_ = lean_ctor_get(v___y_880_, 6);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v___y_880_, 5);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v___y_880_, 4);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v___y_880_, 3);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v___y_880_, 2);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v___y_880_, 1);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v___y_880_, 0);
lean_dec(v_unused_954_);
v___x_922_ = v___y_880_;
v_isShared_923_ = v_isSharedCheck_947_;
goto v_resetjp_921_;
}
else
{
lean_dec(v___y_880_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_947_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
uint64_t v___x_924_; uint64_t v___x_925_; uint8_t v___x_926_; uint64_t v___x_927_; uint64_t v___x_928_; uint64_t v_key_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_924_ = 2ULL;
v___x_925_ = lean_uint64_shift_right(v___x_920_, v___x_924_);
v___x_926_ = 0;
v___x_927_ = lean_uint64_shift_left(v___x_925_, v___x_924_);
v___x_928_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v_key_929_ = lean_uint64_lor(v___x_927_, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_930_, 0, v_config_919_);
lean_ctor_set_uint64(v___x_930_, sizeof(void*)*1, v_key_929_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_930_);
v___x_932_ = v___x_922_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_zetaDeltaSet_908_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_lctx_909_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_localInstances_910_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_defEqCtx_x3f_911_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_synthPendingDepth_912_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_canUnfold_x3f_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*7, v_trackZetaDelta_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*7 + 1, v_univApprox_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*7 + 2, v_inTypeClassResolution_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*7 + 3, v_cacheInferType_916_);
v___x_932_ = v_reuseFailAlloc_946_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; 
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
v___x_933_ = l_Lean_Meta_DiscrTree_mkPath(v_e_879_, v___x_926_, v___x_932_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = l_Lean_Meta_Monotonicity_monotoneExt;
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_decl_876_);
lean_ctor_set(v___x_936_, 1, v_a_934_);
v___x_937_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg(v___x_935_, v___x_936_, v_kind_877_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec(v___y_881_);
return v___x_937_;
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec(v_decl_876_);
v_a_938_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_933_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_933_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v_decl_957_, lean_object* v_kind_958_, lean_object* v_x_959_, lean_object* v_e_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
uint8_t v_kind_boxed_966_; lean_object* v_res_967_; 
v_kind_boxed_966_ = lean_unbox(v_kind_958_);
v_res_967_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v_decl_957_, v_kind_boxed_966_, v_x_959_, v_e_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec_ref(v_x_959_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v___f_968_, lean_object* v_f_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; 
v___x_975_ = l_Lean_Meta_Monotonicity_headBetaUnderLambda(v_f_969_);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = 0;
v___x_978_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg(v___x_975_, v___x_976_, v___f_968_, v___x_977_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v___f_979_, lean_object* v_f_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___f_979_, v_f_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v_res_986_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
lean_ctor_set(v___x_992_, 3, v___x_990_);
lean_ctor_set(v___x_992_, 4, v___x_990_);
lean_ctor_set(v___x_992_, 5, v___x_990_);
lean_ctor_set(v___x_992_, 6, v___x_990_);
lean_ctor_set(v___x_992_, 7, v___x_990_);
lean_ctor_set(v___x_992_, 8, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_unsigned_to_nat(32u);
v___x_994_ = lean_mk_empty_array_with_capacity(v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_996_ = ((size_t)5ULL);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_unsigned_to_nat(32u);
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1001_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
lean_ctor_set(v___x_1001_, 2, v___x_997_);
lean_ctor_set(v___x_1001_, 3, v___x_997_);
lean_ctor_set_usize(v___x_1001_, 4, v___x_996_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = lean_box(1);
v___x_1003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_1004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
lean_ctor_set(v___x_1005_, 2, v___x_1002_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1027_, lean_object* v_declHint_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v_env_1032_; uint8_t v___x_1033_; 
v___x_1031_ = lean_st_ref_get(v___y_1029_);
v_env_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc_ref(v_env_1032_);
lean_dec(v___x_1031_);
v___x_1033_ = l_Lean_Name_isAnonymous(v_declHint_1028_);
if (v___x_1033_ == 0)
{
uint8_t v_isExporting_1034_; 
v_isExporting_1034_ = lean_ctor_get_uint8(v_env_1032_, sizeof(void*)*8);
if (v_isExporting_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1028_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_msg_1027_);
return v___x_1035_;
}
else
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
lean_inc_ref(v_env_1032_);
v___x_1036_ = l_Lean_Environment_setExporting(v_env_1032_, v___x_1033_);
lean_inc(v_declHint_1028_);
lean_inc_ref(v___x_1036_);
v___x_1037_ = l_Lean_Environment_contains(v___x_1036_, v_declHint_1028_, v_isExporting_1034_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1028_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_msg_1027_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_c_1044_; lean_object* v___x_1045_; 
v___x_1039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1041_ = l_Lean_Options_empty;
v___x_1042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1036_);
lean_ctor_set(v___x_1042_, 1, v___x_1039_);
lean_ctor_set(v___x_1042_, 2, v___x_1040_);
lean_ctor_set(v___x_1042_, 3, v___x_1041_);
lean_inc(v_declHint_1028_);
v___x_1043_ = l_Lean_MessageData_ofConstName(v_declHint_1028_, v___x_1033_);
v_c_1044_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1044_, 0, v___x_1042_);
lean_ctor_set(v_c_1044_, 1, v___x_1043_);
v___x_1045_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1032_, v_declHint_1028_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1028_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_c_1044_);
v___x_1048_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_MessageData_note(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_msg_1027_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
else
{
lean_object* v_val_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1088_; 
v_val_1053_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1055_ = v___x_1045_;
v_isShared_1056_ = v_isSharedCheck_1088_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_val_1053_);
lean_dec(v___x_1045_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1088_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_mod_1060_; uint8_t v___x_1061_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = l_Lean_Environment_header(v_env_1032_);
lean_dec_ref(v_env_1032_);
v___x_1059_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1058_);
v_mod_1060_ = lean_array_get(v___x_1057_, v___x_1059_, v_val_1053_);
lean_dec(v_val_1053_);
lean_dec_ref(v___x_1059_);
v___x_1061_ = l_Lean_isPrivateName(v_declHint_1028_);
lean_dec(v_declHint_1028_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_c_1044_);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_ofName(v_mod_1060_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_MessageData_note(v___x_1069_);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_msg_1027_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1071_);
v___x_1073_ = v___x_1055_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1075_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v_c_1044_);
v___x_1077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_MessageData_ofName(v_mod_1060_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_MessageData_note(v___x_1082_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_msg_1027_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1084_);
v___x_1086_ = v___x_1055_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1089_; 
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1028_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_msg_1027_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1090_, lean_object* v_declHint_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1090_, v_declHint_1091_, v___y_1092_);
lean_dec(v___y_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_1095_, lean_object* v_declHint_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1112_; 
v___x_1102_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1095_, v_declHint_1096_, v___y_1100_);
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1107_ = l_Lean_unknownIdentifierMessageTag;
v___x_1108_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v_a_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_1113_, lean_object* v_declHint_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9(v_msg_1113_, v_declHint_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_1121_, lean_object* v_msg_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_fileName_1128_; lean_object* v_fileMap_1129_; lean_object* v_options_1130_; lean_object* v_currRecDepth_1131_; lean_object* v_maxRecDepth_1132_; lean_object* v_ref_1133_; lean_object* v_currNamespace_1134_; lean_object* v_openDecls_1135_; lean_object* v_initHeartbeats_1136_; lean_object* v_maxHeartbeats_1137_; lean_object* v_quotContext_1138_; lean_object* v_currMacroScope_1139_; uint8_t v_diag_1140_; lean_object* v_cancelTk_x3f_1141_; uint8_t v_suppressElabErrors_1142_; lean_object* v_inheritedTraceOptions_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1152_; 
v_fileName_1128_ = lean_ctor_get(v___y_1125_, 0);
v_fileMap_1129_ = lean_ctor_get(v___y_1125_, 1);
v_options_1130_ = lean_ctor_get(v___y_1125_, 2);
v_currRecDepth_1131_ = lean_ctor_get(v___y_1125_, 3);
v_maxRecDepth_1132_ = lean_ctor_get(v___y_1125_, 4);
v_ref_1133_ = lean_ctor_get(v___y_1125_, 5);
v_currNamespace_1134_ = lean_ctor_get(v___y_1125_, 6);
v_openDecls_1135_ = lean_ctor_get(v___y_1125_, 7);
v_initHeartbeats_1136_ = lean_ctor_get(v___y_1125_, 8);
v_maxHeartbeats_1137_ = lean_ctor_get(v___y_1125_, 9);
v_quotContext_1138_ = lean_ctor_get(v___y_1125_, 10);
v_currMacroScope_1139_ = lean_ctor_get(v___y_1125_, 11);
v_diag_1140_ = lean_ctor_get_uint8(v___y_1125_, sizeof(void*)*14);
v_cancelTk_x3f_1141_ = lean_ctor_get(v___y_1125_, 12);
v_suppressElabErrors_1142_ = lean_ctor_get_uint8(v___y_1125_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1143_ = lean_ctor_get(v___y_1125_, 13);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___y_1125_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1145_ = v___y_1125_;
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_inheritedTraceOptions_1143_);
lean_inc(v_cancelTk_x3f_1141_);
lean_inc(v_currMacroScope_1139_);
lean_inc(v_quotContext_1138_);
lean_inc(v_maxHeartbeats_1137_);
lean_inc(v_initHeartbeats_1136_);
lean_inc(v_openDecls_1135_);
lean_inc(v_currNamespace_1134_);
lean_inc(v_ref_1133_);
lean_inc(v_maxRecDepth_1132_);
lean_inc(v_currRecDepth_1131_);
lean_inc(v_options_1130_);
lean_inc(v_fileMap_1129_);
lean_inc(v_fileName_1128_);
lean_dec(v___y_1125_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_ref_1147_; lean_object* v___x_1149_; 
v_ref_1147_ = l_Lean_replaceRef(v_ref_1121_, v_ref_1133_);
lean_dec(v_ref_1133_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 5, v_ref_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_fileName_1128_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_fileMap_1129_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_options_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_currRecDepth_1131_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_maxRecDepth_1132_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_ref_1147_);
lean_ctor_set(v_reuseFailAlloc_1151_, 6, v_currNamespace_1134_);
lean_ctor_set(v_reuseFailAlloc_1151_, 7, v_openDecls_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 8, v_initHeartbeats_1136_);
lean_ctor_set(v_reuseFailAlloc_1151_, 9, v_maxHeartbeats_1137_);
lean_ctor_set(v_reuseFailAlloc_1151_, 10, v_quotContext_1138_);
lean_ctor_set(v_reuseFailAlloc_1151_, 11, v_currMacroScope_1139_);
lean_ctor_set(v_reuseFailAlloc_1151_, 12, v_cancelTk_x3f_1141_);
lean_ctor_set(v_reuseFailAlloc_1151_, 13, v_inheritedTraceOptions_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, sizeof(void*)*14, v_diag_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, sizeof(void*)*14 + 1, v_suppressElabErrors_1142_);
v___x_1149_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v_msg_1122_, v___y_1123_, v___y_1124_, v___x_1149_, v___y_1126_);
lean_dec_ref(v___x_1149_);
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1153_, lean_object* v_msg_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1153_, v_msg_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v_ref_1153_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_1161_, lean_object* v_msg_1162_, lean_object* v_declHint_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v_a_1170_; lean_object* v___x_1171_; 
v___x_1169_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9(v_msg_1162_, v_declHint_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1161_, v_a_1170_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_1172_, lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(v_ref_1172_, v_msg_1173_, v_declHint_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v_ref_1172_);
return v_res_1180_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1183_ = l_Lean_stringToMessageData(v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1186_ = l_Lean_stringToMessageData(v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object* v_ref_1187_, lean_object* v_constName_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1194_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1195_ = 0;
lean_inc(v_constName_1188_);
v___x_1196_ = l_Lean_MessageData_ofConstName(v_constName_1188_, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1194_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(v_ref_1187_, v___x_1199_, v_constName_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_1201_, lean_object* v_constName_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ref_1201_, v_constName_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v_ref_1201_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_constName_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_ref_1215_; lean_object* v___x_1216_; 
v_ref_1215_ = lean_ctor_get(v___y_1212_, 5);
lean_inc(v_ref_1215_);
v___x_1216_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ref_1215_, v_constName_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v_ref_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_constName_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(v_constName_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3(lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v_env_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_st_ref_get(v___y_1228_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = 0;
lean_inc(v_constName_1224_);
v___x_1233_ = l_Lean_Environment_find_x3f(v_env_1231_, v_constName_1224_, v___x_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v___x_1234_;
}
else
{
lean_object* v_val_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___y_1227_);
lean_dec(v_constName_1224_);
v_val_1235_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1233_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_val_1235_);
lean_dec(v___x_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 0);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_val_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3___boxed(lean_object* v_constName_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3(v_constName_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1249_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1254_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
lean_ctor_set(v___x_1254_, 2, v___x_1253_);
lean_ctor_set(v___x_1254_, 3, v___x_1253_);
lean_ctor_set(v___x_1254_, 4, v___x_1253_);
lean_ctor_set(v___x_1254_, 5, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
lean_ctor_set(v___x_1256_, 2, v___x_1255_);
lean_ctor_set(v___x_1256_, 3, v___x_1255_);
lean_ctor_set(v___x_1256_, 4, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v___x_1257_, lean_object* v___x_1258_, lean_object* v___f_1259_, lean_object* v___x_1260_, lean_object* v_decl_1261_, lean_object* v_x_1262_, uint8_t v_kind_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___y_1287_; lean_object* v___x_1297_; 
v___x_1267_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_1268_ = 0;
v___x_1269_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1270_ = lean_unsigned_to_nat(32u);
v___x_1271_ = lean_mk_empty_array_with_capacity(v___x_1270_);
v___x_1272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1273_ = ((size_t)5ULL);
lean_inc_n(v___x_1257_, 2);
v___x_1274_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1271_);
lean_ctor_set(v___x_1274_, 2, v___x_1257_);
lean_ctor_set(v___x_1274_, 3, v___x_1257_);
lean_ctor_set_usize(v___x_1274_, 4, v___x_1273_);
v___x_1275_ = lean_box(1);
lean_inc_ref(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1269_);
lean_ctor_set(v___x_1276_, 1, v___x_1274_);
lean_ctor_set(v___x_1276_, 2, v___x_1275_);
v___x_1277_ = lean_mk_empty_array_with_capacity(v___x_1257_);
v___x_1278_ = lean_box(0);
v___x_1279_ = 1;
lean_inc(v___x_1257_);
lean_inc_ref(v___x_1277_);
lean_inc_ref(v___x_1276_);
lean_inc(v___x_1258_);
v___x_1280_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1280_, 0, v___x_1267_);
lean_ctor_set(v___x_1280_, 1, v___x_1258_);
lean_ctor_set(v___x_1280_, 2, v___x_1276_);
lean_ctor_set(v___x_1280_, 3, v___x_1277_);
lean_ctor_set(v___x_1280_, 4, v___x_1278_);
lean_ctor_set(v___x_1280_, 5, v___x_1257_);
lean_ctor_set(v___x_1280_, 6, v___x_1278_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*7, v___x_1268_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*7 + 1, v___x_1268_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*7 + 2, v___x_1268_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*7 + 3, v___x_1279_);
lean_inc_n(v___x_1257_, 3);
v___x_1281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1257_);
lean_ctor_set(v___x_1281_, 1, v___x_1257_);
lean_ctor_set(v___x_1281_, 2, v___x_1257_);
lean_ctor_set(v___x_1281_, 3, v___x_1269_);
lean_ctor_set(v___x_1281_, 4, v___x_1269_);
lean_ctor_set(v___x_1281_, 5, v___x_1269_);
lean_ctor_set(v___x_1281_, 6, v___x_1269_);
lean_ctor_set(v___x_1281_, 7, v___x_1269_);
lean_ctor_set(v___x_1281_, 8, v___x_1269_);
v___x_1282_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1283_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
lean_inc(v___x_1258_);
v___x_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1281_);
lean_ctor_set(v___x_1284_, 1, v___x_1282_);
lean_ctor_set(v___x_1284_, 2, v___x_1258_);
lean_ctor_set(v___x_1284_, 3, v___x_1274_);
lean_ctor_set(v___x_1284_, 4, v___x_1283_);
v___x_1285_ = lean_st_mk_ref(v___x_1284_);
lean_inc_ref(v___y_1264_);
lean_inc(v_decl_1261_);
v___x_1297_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3(v_decl_1261_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; uint8_t v_foApprox_1300_; uint8_t v_ctxApprox_1301_; uint8_t v_quasiPatternApprox_1302_; uint8_t v_constApprox_1303_; uint8_t v_isDefEqStuckEx_1304_; uint8_t v_unificationHints_1305_; uint8_t v_proofIrrelevance_1306_; uint8_t v_assignSyntheticOpaque_1307_; uint8_t v_offsetCnstrs_1308_; uint8_t v_etaStruct_1309_; uint8_t v_univApprox_1310_; uint8_t v_iota_1311_; uint8_t v_beta_1312_; uint8_t v_proj_1313_; uint8_t v_zeta_1314_; uint8_t v_zetaDelta_1315_; uint8_t v_zetaUnused_1316_; uint8_t v_zetaHave_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1391_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = l_Lean_Meta_Context_config(v___x_1280_);
v_foApprox_1300_ = lean_ctor_get_uint8(v___x_1299_, 0);
v_ctxApprox_1301_ = lean_ctor_get_uint8(v___x_1299_, 1);
v_quasiPatternApprox_1302_ = lean_ctor_get_uint8(v___x_1299_, 2);
v_constApprox_1303_ = lean_ctor_get_uint8(v___x_1299_, 3);
v_isDefEqStuckEx_1304_ = lean_ctor_get_uint8(v___x_1299_, 4);
v_unificationHints_1305_ = lean_ctor_get_uint8(v___x_1299_, 5);
v_proofIrrelevance_1306_ = lean_ctor_get_uint8(v___x_1299_, 6);
v_assignSyntheticOpaque_1307_ = lean_ctor_get_uint8(v___x_1299_, 7);
v_offsetCnstrs_1308_ = lean_ctor_get_uint8(v___x_1299_, 8);
v_etaStruct_1309_ = lean_ctor_get_uint8(v___x_1299_, 10);
v_univApprox_1310_ = lean_ctor_get_uint8(v___x_1299_, 11);
v_iota_1311_ = lean_ctor_get_uint8(v___x_1299_, 12);
v_beta_1312_ = lean_ctor_get_uint8(v___x_1299_, 13);
v_proj_1313_ = lean_ctor_get_uint8(v___x_1299_, 14);
v_zeta_1314_ = lean_ctor_get_uint8(v___x_1299_, 15);
v_zetaDelta_1315_ = lean_ctor_get_uint8(v___x_1299_, 16);
v_zetaUnused_1316_ = lean_ctor_get_uint8(v___x_1299_, 17);
v_zetaHave_1317_ = lean_ctor_get_uint8(v___x_1299_, 18);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1319_ = v___x_1299_;
v_isShared_1320_ = v_isSharedCheck_1391_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v___x_1299_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1391_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; uint8_t v___x_1322_; uint8_t v___x_1323_; lean_object* v_config_1325_; 
v___x_1321_ = l_Lean_ConstantInfo_type(v_a_1298_);
lean_dec(v_a_1298_);
v___x_1322_ = 0;
v___x_1323_ = 2;
if (v_isShared_1320_ == 0)
{
v_config_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 0, v_foApprox_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 1, v_ctxApprox_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 2, v_quasiPatternApprox_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 3, v_constApprox_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 4, v_isDefEqStuckEx_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 5, v_unificationHints_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 6, v_proofIrrelevance_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 7, v_assignSyntheticOpaque_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 8, v_offsetCnstrs_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 10, v_etaStruct_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 11, v_univApprox_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 12, v_iota_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 13, v_beta_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 14, v_proj_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 15, v_zeta_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 16, v_zetaDelta_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 17, v_zetaUnused_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, 18, v_zetaHave_1317_);
v_config_1325_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
uint64_t v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v___x_1330_; uint64_t v_key_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_ctor_set_uint8(v_config_1325_, 9, v___x_1323_);
v___x_1326_ = l_Lean_Meta_Context_configKey(v___x_1280_);
v___x_1327_ = 2ULL;
v___x_1328_ = lean_uint64_shift_right(v___x_1326_, v___x_1327_);
v___x_1329_ = lean_uint64_shift_left(v___x_1328_, v___x_1327_);
v___x_1330_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v_key_1331_ = lean_uint64_lor(v___x_1329_, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1332_, 0, v_config_1325_);
lean_ctor_set_uint64(v___x_1332_, sizeof(void*)*1, v_key_1331_);
v___x_1333_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___x_1258_);
lean_ctor_set(v___x_1333_, 2, v___x_1276_);
lean_ctor_set(v___x_1333_, 3, v___x_1277_);
lean_ctor_set(v___x_1333_, 4, v___x_1278_);
lean_ctor_set(v___x_1333_, 5, v___x_1257_);
lean_ctor_set(v___x_1333_, 6, v___x_1278_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*7, v___x_1268_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*7 + 1, v___x_1268_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*7 + 2, v___x_1268_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*7 + 3, v___x_1279_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___x_1285_);
v___x_1334_ = l_Lean_Meta_forallMetaTelescopeReducing(v___x_1321_, v___x_1278_, v___x_1322_, v___x_1333_, v___x_1285_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v_snd_1336_; lean_object* v_snd_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v___x_1334_);
v_snd_1336_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_snd_1336_);
lean_dec(v_a_1335_);
v_snd_1337_ = lean_ctor_get(v_snd_1336_, 1);
lean_inc(v_snd_1337_);
lean_dec(v_snd_1336_);
v___x_1338_ = l_Lean_Expr_cleanupAnnotations(v_snd_1337_);
v___x_1339_ = l_Lean_Expr_isApp(v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v___x_1338_);
lean_dec(v_decl_1261_);
lean_dec_ref(v___x_1260_);
v___x_1340_ = lean_box(0);
lean_inc(v___x_1285_);
v___x_1341_ = lean_apply_6(v___f_1259_, v___x_1340_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_, lean_box(0));
v___y_1287_ = v___x_1341_;
goto v___jp_1286_;
}
else
{
lean_object* v_arg_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_arg_1342_ = lean_ctor_get(v___x_1338_, 1);
lean_inc_ref(v_arg_1342_);
v___x_1343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1338_);
v___x_1344_ = l_Lean_Expr_isApp(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_arg_1342_);
lean_dec(v_decl_1261_);
lean_dec_ref(v___x_1260_);
v___x_1345_ = lean_box(0);
lean_inc(v___x_1285_);
v___x_1346_ = lean_apply_6(v___f_1259_, v___x_1345_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_, lean_box(0));
v___y_1287_ = v___x_1346_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1343_);
v___x_1348_ = l_Lean_Expr_isApp(v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v___x_1347_);
lean_dec_ref(v_arg_1342_);
lean_dec(v_decl_1261_);
lean_dec_ref(v___x_1260_);
v___x_1349_ = lean_box(0);
lean_inc(v___x_1285_);
v___x_1350_ = lean_apply_6(v___f_1259_, v___x_1349_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_, lean_box(0));
v___y_1287_ = v___x_1350_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1347_);
v___x_1352_ = l_Lean_Expr_isApp(v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v___x_1351_);
lean_dec_ref(v_arg_1342_);
lean_dec(v_decl_1261_);
lean_dec_ref(v___x_1260_);
v___x_1353_ = lean_box(0);
lean_inc(v___x_1285_);
v___x_1354_ = lean_apply_6(v___f_1259_, v___x_1353_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_, lean_box(0));
v___y_1287_ = v___x_1354_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1351_);
v___x_1356_ = l_Lean_Expr_isApp(v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v___x_1355_);
lean_dec_ref(v_arg_1342_);
lean_dec(v_decl_1261_);
lean_dec_ref(v___x_1260_);
v___x_1357_ = lean_box(0);
lean_inc(v___x_1285_);
v___x_1358_ = lean_apply_6(v___f_1259_, v___x_1357_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_, lean_box(0));
v___y_1287_ = v___x_1358_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1355_);
v___x_1360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1362_ = l_Lean_Name_mkStr3(v___x_1260_, v___x_1360_, v___x_1361_);
v___x_1363_ = l_Lean_Expr_isConstOf(v___x_1359_, v___x_1362_);
lean_dec(v___x_1362_);
lean_dec_ref(v___x_1359_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref(v_arg_1342_);
lean_dec(v_decl_1261_);
v___x_1364_ = lean_box(0);
lean_inc(v___x_1285_);
v___x_1365_ = lean_apply_6(v___f_1259_, v___x_1364_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_, lean_box(0));
v___y_1287_ = v___x_1365_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1366_; lean_object* v___f_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
lean_dec_ref(v___f_1259_);
v___x_1366_ = lean_box(v_kind_1263_);
v___f_1367_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed), 9, 2);
lean_closure_set(v___f_1367_, 0, v_decl_1261_);
lean_closure_set(v___f_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_Expr_headBeta(v_arg_1342_);
v___x_1369_ = l_Lean_Expr_isLambda(v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___x_1285_);
lean_inc_ref(v___x_1280_);
v___x_1370_ = l_Lean_Meta_etaExpand(v___x_1368_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1372_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v___x_1370_);
lean_inc(v___x_1285_);
v___x_1372_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___f_1367_, v_a_1371_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_);
v___y_1287_ = v___x_1372_;
goto v___jp_1286_;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v___f_1367_);
lean_dec(v___x_1285_);
lean_dec_ref(v___x_1280_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
v_a_1373_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1370_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v___x_1381_; 
lean_inc(v___x_1285_);
v___x_1381_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___f_1367_, v___x_1368_, v___x_1280_, v___x_1285_, v___y_1264_, v___y_1265_);
v___y_1287_ = v___x_1381_;
goto v___jp_1286_;
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
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v___x_1285_);
lean_dec_ref(v___x_1280_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v_decl_1261_);
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___f_1259_);
v_a_1382_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1334_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1334_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v___x_1285_);
lean_dec_ref(v___x_1280_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v_decl_1261_);
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___f_1259_);
lean_dec(v___x_1258_);
lean_dec(v___x_1257_);
v_a_1392_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1297_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1297_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
v___jp_1286_:
{
if (lean_obj_tag(v___y_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1296_; 
v_a_1288_ = lean_ctor_get(v___y_1287_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___y_1287_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1290_ = v___y_1287_;
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___y_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_st_ref_get(v___x_1285_);
lean_dec(v___x_1285_);
lean_dec(v___x_1292_);
if (v_isShared_1291_ == 0)
{
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1288_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_dec(v___x_1285_);
return v___y_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___f_1402_, lean_object* v___x_1403_, lean_object* v_decl_1404_, lean_object* v_x_1405_, lean_object* v_kind_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_kind_boxed_1410_; lean_object* v_res_1411_; 
v_kind_boxed_1410_ = lean_unbox(v_kind_1406_);
v_res_1411_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___x_1400_, v___x_1401_, v___f_1402_, v___x_1403_, v_decl_1404_, v_x_1405_, v_kind_boxed_1410_, v___y_1407_, v___y_1408_);
lean_dec(v_x_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_msgData_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v_env_1417_; lean_object* v_options_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1416_ = lean_st_ref_get(v___y_1414_);
v_env_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_env_1417_);
lean_dec(v___x_1416_);
v_options_1418_ = lean_ctor_get(v___y_1413_, 2);
v___x_1419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1420_ = lean_unsigned_to_nat(32u);
v___x_1421_ = lean_mk_empty_array_with_capacity(v___x_1420_);
lean_dec_ref(v___x_1421_);
v___x_1422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_1418_);
v___x_1423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1423_, 0, v_env_1417_);
lean_ctor_set(v___x_1423_, 1, v___x_1419_);
lean_ctor_set(v___x_1423_, 2, v___x_1422_);
lean_ctor_set(v___x_1423_, 3, v_options_1418_);
v___x_1424_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_msgData_1412_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_msgData_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6(v_msgData_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(lean_object* v_msg_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_ref_1435_; lean_object* v___x_1436_; lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_ref_1435_ = lean_ctor_get(v___y_1432_, 5);
v___x_1436_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6(v_msg_1431_, v___y_1432_, v___y_1433_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_inc(v_ref_1435_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_ref_1435_);
lean_ctor_set(v___x_1441_, 1, v_a_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 1);
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(v_msg_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1450_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1453_ = l_Lean_stringToMessageData(v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1456_ = l_Lean_stringToMessageData(v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v___x_1457_, lean_object* v_decl_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1462_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1463_ = l_Lean_MessageData_ofName(v___x_1457_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(v___x_1466_, v___y_1459_, v___y_1460_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v___x_1468_, lean_object* v_decl_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___x_1468_, v_decl_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v_decl_1469_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__33_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1562_ = l_Lean_registerBuiltinAttribute(v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1565_, lean_object* v_msg_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v_msg_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0(v_00_u03b1_1573_, v_msg_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1581_, lean_object* v_msg_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(v_msg_1582_, v___y_1583_, v___y_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1587_, lean_object* v_msg_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4(v_00_u03b1_1587_, v_msg_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b1_1593_, lean_object* v_constName_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(v_constName_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b1_1601_, lean_object* v_constName_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b1_1601_, v_constName_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_00_u03b1_1609_, lean_object* v_ref_1610_, lean_object* v_constName_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ref_1610_, v_constName_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_ref_1619_, lean_object* v_constName_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_00_u03b1_1618_, v_ref_1619_, v_constName_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v_ref_1619_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1627_, lean_object* v_ref_1628_, lean_object* v_msg_1629_, lean_object* v_declHint_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(v_ref_1628_, v_msg_1629_, v_declHint_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1637_, lean_object* v_ref_1638_, lean_object* v_msg_1639_, lean_object* v_declHint_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8(v_00_u03b1_1637_, v_ref_1638_, v_msg_1639_, v_declHint_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v_ref_1638_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1647_, lean_object* v_declHint_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1647_, v_declHint_1648_, v___y_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1655_, lean_object* v_declHint_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1655_, v_declHint_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1663_, lean_object* v_ref_1664_, lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1664_, v_msg_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_ref_1673_, lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1672_, v_ref_1673_, v_msg_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v_ref_1673_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__27_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1685_ = l_Lean_addBuiltinDocString(v___x_1683_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_findMonoThms(lean_object* v_e_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1694_; lean_object* v_env_1695_; lean_object* v___x_1696_; lean_object* v_ext_1697_; lean_object* v_toEnvExtension_1698_; lean_object* v_asyncMode_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1694_ = lean_st_ref_get(v_a_1692_);
v_env_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc_ref(v_env_1695_);
lean_dec(v___x_1694_);
v___x_1696_ = l_Lean_Meta_Monotonicity_monotoneExt;
v_ext_1697_ = lean_ctor_get(v___x_1696_, 1);
lean_inc_ref(v_ext_1697_);
v_toEnvExtension_1698_ = lean_ctor_get(v_ext_1697_, 0);
lean_inc_ref(v_toEnvExtension_1698_);
lean_dec_ref(v_ext_1697_);
v_asyncMode_1699_ = lean_ctor_get(v_toEnvExtension_1698_, 2);
lean_inc(v_asyncMode_1699_);
lean_dec_ref(v_toEnvExtension_1698_);
v___x_1700_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0);
v___x_1701_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1700_, v___x_1696_, v_env_1695_, v_asyncMode_1699_);
lean_dec(v_asyncMode_1699_);
v___x_1702_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_1701_, v_e_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_findMonoThms___boxed(lean_object* v_e_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_Monotonicity_findMonoThms(v_e_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v_res_1709_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__0));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0(lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
if (lean_obj_tag(v_a_1713_) == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = l_List_reverse___redArg(v_a_1714_);
return v___x_1715_;
}
else
{
lean_object* v_head_1716_; lean_object* v_tail_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1729_; 
v_head_1716_ = lean_ctor_get(v_a_1713_, 0);
v_tail_1717_ = lean_ctor_get(v_a_1713_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_a_1713_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1719_ = v_a_1713_;
v_isShared_1720_ = v_isSharedCheck_1729_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_tail_1717_);
lean_inc(v_head_1716_);
lean_dec(v_a_1713_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1729_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1721_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1);
v___x_1722_ = l_Lean_MessageData_ofName(v_head_1716_);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1721_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v_a_1714_);
lean_ctor_set(v___x_1719_, 0, v___x_1724_);
v___x_1726_ = v___x_1719_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_a_1714_);
v___x_1726_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
v_a_1713_ = v_tail_1717_;
v_a_1714_ = v___x_1726_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__0));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__2));
v___x_1735_ = l_Lean_stringToMessageData(v___x_1734_);
return v___x_1735_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__4));
v___x_1738_ = l_Lean_stringToMessageData(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__6));
v___x_1741_ = l_Lean_stringToMessageData(v___x_1740_);
return v___x_1741_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__8));
v___x_1744_ = l_Lean_stringToMessageData(v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg(lean_object* v_f_1745_, lean_object* v_monoThms_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___y_1753_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = lean_array_get_size(v_monoThms_1746_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_nat_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1764_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5);
v___x_1765_ = lean_array_to_list(v_monoThms_1746_);
v___x_1766_ = lean_box(0);
v___x_1767_ = l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0(v___x_1765_, v___x_1766_);
v___x_1768_ = l_Lean_MessageData_andList(v___x_1767_);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1764_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___y_1753_ = v___x_1771_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1772_; 
lean_dec_ref(v_monoThms_1746_);
v___x_1772_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9);
v___y_1753_ = v___x_1772_;
goto v___jp_1752_;
}
v___jp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1754_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1);
v___x_1755_ = l_Lean_indentExpr(v_f_1745_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___y_1753_);
v___x_1760_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_1759_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___boxed(lean_object* v_f_1773_, lean_object* v_monoThms_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Meta_Monotonicity_defaultFailK___redArg(v_f_1773_, v_monoThms_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK(lean_object* v_00_u03b1_1781_, lean_object* v_f_1782_, lean_object* v_monoThms_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Meta_Monotonicity_defaultFailK___redArg(v_f_1782_, v_monoThms_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_f_1791_, lean_object* v_monoThms_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Meta_Monotonicity_defaultFailK(v_00_u03b1_1790_, v_f_1791_, v_monoThms_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___lam__0(lean_object* v___x_1799_, lean_object* v_e_1800_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = l_Lean_indentD(v_e_1800_);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1799_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
return v___x_1802_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__0));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__2));
v___x_1808_ = l_Lean_stringToMessageData(v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(lean_object* v_goal_1813_, lean_object* v_name_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v___x_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1820_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1_once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1);
v___x_1821_ = 0;
lean_inc(v_name_1814_);
v___x_1822_ = l_Lean_MessageData_ofConstName(v_name_1814_, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1820_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3_once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___f_1826_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___lam__0), 2, 1);
lean_closure_set(v___f_1826_, 0, v___x_1825_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__4));
v___x_1828_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyConst___boxed), 8, 3);
lean_closure_set(v___x_1828_, 0, v_goal_1813_);
lean_closure_set(v___x_1828_, 1, v_name_1814_);
lean_closure_set(v___x_1828_, 2, v___x_1827_);
v___x_1829_ = l_Lean_Meta_mapErrorImp___redArg(v___x_1828_, v___f_1826_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1829_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1829_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___boxed(lean_object* v_goal_1846_, lean_object* v_name_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_1846_, v_name_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__0(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = l_Lean_Expr_bvar___override(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__3));
v___x_1863_ = l_Lean_stringToMessageData(v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__6(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__5));
v___x_1866_ = l_Lean_stringToMessageData(v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__8(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__7));
v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__18(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__17));
v___x_1894_ = l_Lean_stringToMessageData(v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoCall(lean_object* v_00_u03b1_1905_, lean_object* v_inst___u03b1_1906_, lean_object* v_e_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; uint8_t v___y_2173_; uint8_t v___x_2300_; 
v___x_2300_ = l_Lean_Expr_isApp(v_e_1907_);
if (v___x_2300_ == 0)
{
v___y_2173_ = v___x_2300_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = l_Lean_Expr_appArg_x21(v_e_1907_);
v___x_2302_ = l_Lean_Expr_hasLooseBVars(v___x_2301_);
lean_dec_ref(v___x_2301_);
if (v___x_2302_ == 0)
{
v___y_2173_ = v___x_2300_;
goto v___jp_2172_;
}
else
{
v___y_2038_ = v_a_1908_;
v___y_2039_ = v_a_1909_;
v___y_2040_ = v_a_1910_;
v___y_2041_ = v_a_1911_;
goto v___jp_2037_;
}
}
v___jp_1913_:
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__0, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__0_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__0);
v___x_1919_ = lean_expr_eqv(v_e_1907_, v___x_1918_);
lean_dec_ref(v_e_1907_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__2));
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_00_u03b1_1905_);
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_inst___u03b1_1906_);
v___x_1925_ = lean_unsigned_to_nat(2u);
v___x_1926_ = lean_mk_empty_array_with_capacity(v___x_1925_);
v___x_1927_ = lean_array_push(v___x_1926_, v___x_1923_);
v___x_1928_ = lean_array_push(v___x_1927_, v___x_1924_);
v___x_1929_ = l_Lean_Meta_mkAppOptM(v___x_1922_, v___x_1928_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1938_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1930_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1934_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1929_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1929_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
v___jp_1947_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1953_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1907_);
v___x_1954_ = l_Lean_MessageData_ofExpr(v_e_1907_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__6, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__6_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__6);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_MessageData_ofExpr(v___y_1948_);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_1959_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_dec_ref(v___x_1960_);
v___y_1914_ = v___y_1949_;
v___y_1915_ = v___y_1950_;
v___y_1916_ = v___y_1951_;
v___y_1917_ = v___y_1952_;
goto v___jp_1913_;
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
v___jp_1969_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1975_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1907_);
v___x_1976_ = l_Lean_MessageData_ofExpr(v_e_1907_);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__8, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__8_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__8);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = l_Lean_indentExpr(v___y_1970_);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_1981_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_dec_ref(v___x_1982_);
v___y_1914_ = v___y_1971_;
v___y_1915_ = v___y_1972_;
v___y_1916_ = v___y_1973_;
v___y_1917_ = v___y_1974_;
goto v___jp_1913_;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
v___jp_1991_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___y_1995_);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___y_1996_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_00_u03b1_1905_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___y_1997_);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___y_1994_);
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_inst___u03b1_1906_);
v___x_2008_ = lean_box(0);
v___x_2009_ = lean_unsigned_to_nat(8u);
v___x_2010_ = lean_mk_empty_array_with_capacity(v___x_2009_);
v___x_2011_ = lean_array_push(v___x_2010_, v___x_2002_);
v___x_2012_ = lean_array_push(v___x_2011_, v___x_2003_);
v___x_2013_ = lean_array_push(v___x_2012_, v___x_2004_);
v___x_2014_ = lean_array_push(v___x_2013_, v___x_2005_);
v___x_2015_ = lean_array_push(v___x_2014_, v___x_2006_);
v___x_2016_ = lean_array_push(v___x_2015_, v___x_2007_);
v___x_2017_ = lean_array_push(v___x_2016_, v___x_2008_);
v___x_2018_ = lean_array_push(v___x_2017_, v___y_1998_);
v___x_2019_ = l_Lean_Meta_mkAppOptM(v___y_2001_, v___x_2018_, v___y_2000_, v___y_1992_, v___y_1993_, v___y_1999_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_a_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2019_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2019_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
v___jp_2037_:
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lean_Expr_isProj(v_e_1907_);
if (v___x_2042_ == 0)
{
v___y_1914_ = v___y_2038_;
v___y_1915_ = v___y_2039_;
v___y_1916_ = v___y_2040_;
v___y_1917_ = v___y_2041_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = l_Lean_Expr_projExpr_x21(v_e_1907_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2039_);
lean_inc_ref(v___y_2038_);
lean_inc_ref(v_inst___u03b1_1906_);
lean_inc_ref(v_00_u03b1_1905_);
v___x_2044_ = l_Lean_Meta_Monotonicity_solveMonoCall(v_00_u03b1_1905_, v_inst___u03b1_1906_, v___x_2043_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2127_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2127_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2127_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
if (lean_obj_tag(v_a_2045_) == 1)
{
lean_object* v_val_2049_; lean_object* v___x_2050_; 
lean_del_object(v___x_2047_);
v_val_2049_ = lean_ctor_get(v_a_2045_, 0);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2039_);
lean_inc_ref(v___y_2038_);
lean_inc(v_val_2049_);
v___x_2050_ = lean_infer_type(v_val_2049_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
lean_inc(v_a_2051_);
v___x_2052_ = l_Lean_Expr_cleanupAnnotations(v_a_2051_);
v___x_2053_ = l_Lean_Expr_isApp(v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec_ref(v___x_2052_);
lean_dec_ref(v_a_2045_);
v___y_1948_ = v_a_2051_;
v___y_1949_ = v___y_2038_;
v___y_1950_ = v___y_2039_;
v___y_1951_ = v___y_2040_;
v___y_1952_ = v___y_2041_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2052_);
v___x_2055_ = l_Lean_Expr_isApp(v___x_2054_);
if (v___x_2055_ == 0)
{
lean_dec_ref(v___x_2054_);
lean_dec_ref(v_a_2045_);
v___y_1948_ = v_a_2051_;
v___y_1949_ = v___y_2038_;
v___y_1950_ = v___y_2039_;
v___y_1951_ = v___y_2040_;
v___y_1952_ = v___y_2041_;
goto v___jp_1947_;
}
else
{
lean_object* v_arg_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_arg_2056_ = lean_ctor_get(v___x_2054_, 1);
lean_inc_ref(v_arg_2056_);
v___x_2057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2054_);
v___x_2058_ = l_Lean_Expr_isApp(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec_ref(v___x_2057_);
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_a_2045_);
v___y_1948_ = v_a_2051_;
v___y_1949_ = v___y_2038_;
v___y_1950_ = v___y_2039_;
v___y_1951_ = v___y_2040_;
v___y_1952_ = v___y_2041_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2057_);
v___x_2060_ = l_Lean_Expr_isApp(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_a_2045_);
v___y_1948_ = v_a_2051_;
v___y_1949_ = v___y_2038_;
v___y_1950_ = v___y_2039_;
v___y_1951_ = v___y_2040_;
v___y_1952_ = v___y_2041_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2059_);
v___x_2062_ = l_Lean_Expr_isApp(v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_a_2045_);
v___y_1948_ = v_a_2051_;
v___y_1949_ = v___y_2038_;
v___y_1950_ = v___y_2039_;
v___y_1951_ = v___y_2040_;
v___y_1952_ = v___y_2041_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2063_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2061_);
v___x_2064_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__9));
v___x_2065_ = l_Lean_Expr_isConstOf(v___x_2063_, v___x_2064_);
lean_dec_ref(v___x_2063_);
if (v___x_2065_ == 0)
{
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_a_2045_);
v___y_1948_ = v_a_2051_;
v___y_1949_ = v___y_2038_;
v___y_1950_ = v___y_2039_;
v___y_1951_ = v___y_2040_;
v___y_1952_ = v___y_2041_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_dec(v_a_2051_);
v___x_2066_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__11));
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2039_);
lean_inc_ref(v___y_2038_);
lean_inc_ref(v_arg_2056_);
v___x_2067_ = l_Lean_Meta_whnfUntil(v_arg_2056_, v___x_2066_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
if (lean_obj_tag(v_a_2068_) == 1)
{
lean_object* v_val_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v_arg_2056_);
v_val_2069_ = lean_ctor_get(v_a_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref(v_a_2068_);
lean_inc(v_val_2069_);
v___x_2070_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_2069_, v___y_2039_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2070_);
v___x_2072_ = l_Lean_Expr_cleanupAnnotations(v_a_2071_);
v___x_2073_ = l_Lean_Expr_isApp(v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v___x_2072_);
lean_dec_ref(v_a_2045_);
v___y_1970_ = v_val_2069_;
v___y_1971_ = v___y_2038_;
v___y_1972_ = v___y_2039_;
v___y_1973_ = v___y_2040_;
v___y_1974_ = v___y_2041_;
goto v___jp_1969_;
}
else
{
lean_object* v_arg_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_arg_2074_ = lean_ctor_get(v___x_2072_, 1);
lean_inc_ref(v_arg_2074_);
v___x_2075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2072_);
v___x_2076_ = l_Lean_Expr_isApp(v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_a_2045_);
v___y_1970_ = v_val_2069_;
v___y_1971_ = v___y_2038_;
v___y_1972_ = v___y_2039_;
v___y_1973_ = v___y_2040_;
v___y_1974_ = v___y_2041_;
goto v___jp_1969_;
}
else
{
lean_object* v_arg_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v_arg_2077_ = lean_ctor_get(v___x_2075_, 1);
lean_inc_ref(v_arg_2077_);
v___x_2078_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2075_);
v___x_2079_ = l_Lean_Expr_isApp(v___x_2078_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_a_2045_);
v___y_1970_ = v_val_2069_;
v___y_1971_ = v___y_2038_;
v___y_1972_ = v___y_2039_;
v___y_1973_ = v___y_2040_;
v___y_1974_ = v___y_2041_;
goto v___jp_1969_;
}
else
{
lean_object* v_arg_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_arg_2080_ = lean_ctor_get(v___x_2078_, 1);
lean_inc_ref(v_arg_2080_);
v___x_2081_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2078_);
v___x_2082_ = l_Lean_Expr_isApp(v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v___x_2081_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_a_2045_);
v___y_1970_ = v_val_2069_;
v___y_1971_ = v___y_2038_;
v___y_1972_ = v___y_2039_;
v___y_1973_ = v___y_2040_;
v___y_1974_ = v___y_2041_;
goto v___jp_1969_;
}
else
{
lean_object* v_arg_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_arg_2083_ = lean_ctor_get(v___x_2081_, 1);
lean_inc_ref(v_arg_2083_);
v___x_2084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2081_);
v___x_2085_ = l_Lean_Expr_isConstOf(v___x_2084_, v___x_2066_);
lean_dec_ref(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_a_2045_);
v___y_1970_ = v_val_2069_;
v___y_1971_ = v___y_2038_;
v___y_1972_ = v___y_2039_;
v___y_1973_ = v___y_2040_;
v___y_1974_ = v___y_2041_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
lean_dec(v_val_2069_);
v___x_2086_ = l_Lean_Expr_projIdx_x21(v_e_1907_);
lean_dec_ref(v_e_1907_);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_nat_dec_eq(v___x_2086_, v___x_2087_);
lean_dec(v___x_2086_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__14));
v___y_1992_ = v___y_2039_;
v___y_1993_ = v___y_2040_;
v___y_1994_ = v_arg_2074_;
v___y_1995_ = v_arg_2083_;
v___y_1996_ = v_arg_2080_;
v___y_1997_ = v_arg_2077_;
v___y_1998_ = v_a_2045_;
v___y_1999_ = v___y_2041_;
v___y_2000_ = v___y_2038_;
v___y_2001_ = v___x_2089_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__16));
v___y_1992_ = v___y_2039_;
v___y_1993_ = v___y_2040_;
v___y_1994_ = v_arg_2074_;
v___y_1995_ = v_arg_2083_;
v___y_1996_ = v_arg_2080_;
v___y_1997_ = v_arg_2077_;
v___y_1998_ = v_a_2045_;
v___y_1999_ = v___y_2041_;
v___y_2000_ = v___y_2038_;
v___y_2001_ = v___x_2090_;
goto v___jp_1991_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_val_2069_);
lean_dec_ref(v_a_2045_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2091_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2070_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2070_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2045_);
v___x_2099_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1907_);
v___x_2100_ = l_Lean_MessageData_ofExpr(v_e_1907_);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__18, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__18_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__18);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_MessageData_ofExpr(v_arg_2056_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2105_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_dec_ref(v___x_2106_);
v___y_1914_ = v___y_2038_;
v___y_1915_ = v___y_2039_;
v___y_1916_ = v___y_2040_;
v___y_1917_ = v___y_2041_;
goto v___jp_1913_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_a_2045_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
return v___x_2067_;
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
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_a_2045_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2115_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2050_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2050_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec(v_a_2045_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v___x_2123_ = lean_box(0);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2123_);
v___x_2125_ = v___x_2047_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
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
else
{
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
return v___x_2044_;
}
}
}
v___jp_2128_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2134_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1907_);
v___x_2135_ = l_Lean_MessageData_ofExpr(v_e_1907_);
v___x_2136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__6, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__6_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__6);
v___x_2138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l_Lean_MessageData_ofExpr(v___y_2129_);
v___x_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2140_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_dec_ref(v___x_2141_);
v___y_2038_ = v___y_2130_;
v___y_2039_ = v___y_2131_;
v___y_2040_ = v___y_2132_;
v___y_2041_ = v___y_2133_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
v___jp_2150_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2156_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1907_);
v___x_2157_ = l_Lean_MessageData_ofExpr(v_e_1907_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__8, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__8_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__8);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = l_Lean_indentExpr(v___y_2151_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2162_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec_ref(v___x_2163_);
v___y_2038_ = v___y_2152_;
v___y_2039_ = v___y_2153_;
v___y_2040_ = v___y_2154_;
v___y_2041_ = v___y_2155_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
v___jp_2172_:
{
if (v___y_2173_ == 0)
{
v___y_2038_ = v_a_1908_;
v___y_2039_ = v_a_1909_;
v___y_2040_ = v_a_1910_;
v___y_2041_ = v_a_1911_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = l_Lean_Expr_appFn_x21(v_e_1907_);
lean_inc(v_a_1911_);
lean_inc_ref(v_a_1910_);
lean_inc(v_a_1909_);
lean_inc_ref(v_a_1908_);
lean_inc_ref(v_inst___u03b1_1906_);
lean_inc_ref(v_00_u03b1_1905_);
v___x_2175_ = l_Lean_Meta_Monotonicity_solveMonoCall(v_00_u03b1_1905_, v_inst___u03b1_1906_, v___x_2174_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2299_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2299_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2299_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
if (lean_obj_tag(v_a_2176_) == 1)
{
lean_object* v_val_2180_; lean_object* v___x_2181_; 
lean_del_object(v___x_2178_);
v_val_2180_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_a_1911_);
lean_inc_ref(v_a_1910_);
lean_inc(v_a_1909_);
lean_inc_ref(v_a_1908_);
lean_inc(v_val_2180_);
v___x_2181_ = lean_infer_type(v_val_2180_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
lean_inc(v_a_2182_);
v___x_2183_ = l_Lean_Expr_cleanupAnnotations(v_a_2182_);
v___x_2184_ = l_Lean_Expr_isApp(v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec_ref(v___x_2183_);
lean_dec_ref(v_a_2176_);
v___y_2129_ = v_a_2182_;
v___y_2130_ = v_a_1908_;
v___y_2131_ = v_a_1909_;
v___y_2132_ = v_a_1910_;
v___y_2133_ = v_a_1911_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2183_);
v___x_2186_ = l_Lean_Expr_isApp(v___x_2185_);
if (v___x_2186_ == 0)
{
lean_dec_ref(v___x_2185_);
lean_dec_ref(v_a_2176_);
v___y_2129_ = v_a_2182_;
v___y_2130_ = v_a_1908_;
v___y_2131_ = v_a_1909_;
v___y_2132_ = v_a_1910_;
v___y_2133_ = v_a_1911_;
goto v___jp_2128_;
}
else
{
lean_object* v_arg_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_arg_2187_ = lean_ctor_get(v___x_2185_, 1);
lean_inc_ref(v_arg_2187_);
v___x_2188_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2185_);
v___x_2189_ = l_Lean_Expr_isApp(v___x_2188_);
if (v___x_2189_ == 0)
{
lean_dec_ref(v___x_2188_);
lean_dec_ref(v_arg_2187_);
lean_dec_ref(v_a_2176_);
v___y_2129_ = v_a_2182_;
v___y_2130_ = v_a_1908_;
v___y_2131_ = v_a_1909_;
v___y_2132_ = v_a_1910_;
v___y_2133_ = v_a_1911_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2188_);
v___x_2191_ = l_Lean_Expr_isApp(v___x_2190_);
if (v___x_2191_ == 0)
{
lean_dec_ref(v___x_2190_);
lean_dec_ref(v_arg_2187_);
lean_dec_ref(v_a_2176_);
v___y_2129_ = v_a_2182_;
v___y_2130_ = v_a_1908_;
v___y_2131_ = v_a_1909_;
v___y_2132_ = v_a_1910_;
v___y_2133_ = v_a_1911_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2190_);
v___x_2193_ = l_Lean_Expr_isApp(v___x_2192_);
if (v___x_2193_ == 0)
{
lean_dec_ref(v___x_2192_);
lean_dec_ref(v_arg_2187_);
lean_dec_ref(v_a_2176_);
v___y_2129_ = v_a_2182_;
v___y_2130_ = v_a_1908_;
v___y_2131_ = v_a_1909_;
v___y_2132_ = v_a_1910_;
v___y_2133_ = v_a_1911_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2192_);
v___x_2195_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__9));
v___x_2196_ = l_Lean_Expr_isConstOf(v___x_2194_, v___x_2195_);
lean_dec_ref(v___x_2194_);
if (v___x_2196_ == 0)
{
lean_dec_ref(v_arg_2187_);
lean_dec_ref(v_a_2176_);
v___y_2129_ = v_a_2182_;
v___y_2130_ = v_a_1908_;
v___y_2131_ = v_a_1909_;
v___y_2132_ = v_a_1910_;
v___y_2133_ = v_a_1911_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec(v_a_2182_);
v___x_2197_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__20));
lean_inc(v_a_1911_);
lean_inc_ref(v_a_1910_);
lean_inc(v_a_1909_);
lean_inc_ref(v_a_1908_);
lean_inc_ref(v_arg_2187_);
v___x_2198_ = l_Lean_Meta_whnfUntil(v_arg_2187_, v___x_2197_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2286_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2286_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2286_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
if (lean_obj_tag(v_a_2199_) == 1)
{
lean_object* v_val_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_arg_2187_);
v_val_2203_ = lean_ctor_get(v_a_2199_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_a_2199_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2205_ = v_a_2199_;
v_isShared_2206_ = v_isSharedCheck_2269_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_val_2203_);
lean_dec(v_a_2199_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2269_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; 
lean_inc(v_val_2203_);
v___x_2207_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_2203_, v_a_1909_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = l_Lean_Expr_cleanupAnnotations(v_a_2208_);
v___x_2210_ = l_Lean_Expr_isApp(v___x_2209_);
if (v___x_2210_ == 0)
{
lean_dec_ref(v___x_2209_);
lean_del_object(v___x_2205_);
lean_del_object(v___x_2201_);
lean_dec_ref(v_a_2176_);
v___y_2151_ = v_val_2203_;
v___y_2152_ = v_a_1908_;
v___y_2153_ = v_a_1909_;
v___y_2154_ = v_a_1910_;
v___y_2155_ = v_a_1911_;
goto v___jp_2150_;
}
else
{
lean_object* v_arg_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_arg_2211_ = lean_ctor_get(v___x_2209_, 1);
lean_inc_ref(v_arg_2211_);
v___x_2212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2209_);
v___x_2213_ = l_Lean_Expr_isApp(v___x_2212_);
if (v___x_2213_ == 0)
{
lean_dec_ref(v___x_2212_);
lean_dec_ref(v_arg_2211_);
lean_del_object(v___x_2205_);
lean_del_object(v___x_2201_);
lean_dec_ref(v_a_2176_);
v___y_2151_ = v_val_2203_;
v___y_2152_ = v_a_1908_;
v___y_2153_ = v_a_1909_;
v___y_2154_ = v_a_1910_;
v___y_2155_ = v_a_1911_;
goto v___jp_2150_;
}
else
{
lean_object* v_arg_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_arg_2214_ = lean_ctor_get(v___x_2212_, 1);
lean_inc_ref(v_arg_2214_);
v___x_2215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2212_);
v___x_2216_ = l_Lean_Expr_isApp(v___x_2215_);
if (v___x_2216_ == 0)
{
lean_dec_ref(v___x_2215_);
lean_dec_ref(v_arg_2214_);
lean_dec_ref(v_arg_2211_);
lean_del_object(v___x_2205_);
lean_del_object(v___x_2201_);
lean_dec_ref(v_a_2176_);
v___y_2151_ = v_val_2203_;
v___y_2152_ = v_a_1908_;
v___y_2153_ = v_a_1909_;
v___y_2154_ = v_a_1910_;
v___y_2155_ = v_a_1911_;
goto v___jp_2150_;
}
else
{
lean_object* v_arg_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v_arg_2217_ = lean_ctor_get(v___x_2215_, 1);
lean_inc_ref(v_arg_2217_);
v___x_2218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2215_);
v___x_2219_ = l_Lean_Expr_isConstOf(v___x_2218_, v___x_2197_);
lean_dec_ref(v___x_2218_);
if (v___x_2219_ == 0)
{
lean_dec_ref(v_arg_2217_);
lean_dec_ref(v_arg_2214_);
lean_dec_ref(v_arg_2211_);
lean_del_object(v___x_2205_);
lean_del_object(v___x_2201_);
lean_dec_ref(v_a_2176_);
v___y_2151_ = v_val_2203_;
v___y_2152_ = v_a_1908_;
v___y_2153_ = v_a_1909_;
v___y_2154_ = v_a_1910_;
v___y_2155_ = v_a_1911_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
lean_dec(v_val_2203_);
v___x_2220_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__22));
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_arg_2217_);
v___x_2222_ = v___x_2205_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_arg_2217_);
v___x_2222_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set_tag(v___x_2201_, 1);
lean_ctor_set(v___x_2201_, 0, v_arg_2214_);
v___x_2224_ = v___x_2201_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_arg_2214_);
v___x_2224_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_00_u03b1_1905_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_inst___u03b1_1906_);
v___x_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2227_, 0, v_arg_2211_);
v___x_2228_ = l_Lean_Expr_appArg_x21(v_e_1907_);
lean_dec_ref(v_e_1907_);
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_unsigned_to_nat(8u);
v___x_2232_ = lean_mk_empty_array_with_capacity(v___x_2231_);
v___x_2233_ = lean_array_push(v___x_2232_, v___x_2222_);
v___x_2234_ = lean_array_push(v___x_2233_, v___x_2224_);
v___x_2235_ = lean_array_push(v___x_2234_, v___x_2225_);
v___x_2236_ = lean_array_push(v___x_2235_, v___x_2226_);
v___x_2237_ = lean_array_push(v___x_2236_, v___x_2227_);
v___x_2238_ = lean_array_push(v___x_2237_, v___x_2229_);
v___x_2239_ = lean_array_push(v___x_2238_, v___x_2230_);
v___x_2240_ = lean_array_push(v___x_2239_, v_a_2176_);
v___x_2241_ = l_Lean_Meta_mkAppOptM(v___x_2220_, v___x_2240_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_a_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2241_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2241_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
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
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_del_object(v___x_2205_);
lean_dec(v_val_2203_);
lean_del_object(v___x_2201_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2261_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2207_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2207_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_del_object(v___x_2201_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2176_);
v___x_2270_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1907_);
v___x_2271_ = l_Lean_MessageData_ofExpr(v_e_1907_);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__18, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__18_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__18);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = l_Lean_MessageData_ofExpr(v_arg_2187_);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2276_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_dec_ref(v___x_2277_);
v___y_2038_ = v_a_1908_;
v___y_2039_ = v_a_1909_;
v___y_2040_ = v_a_1910_;
v___y_2041_ = v_a_1911_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2187_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
return v___x_2198_;
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
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v_a_2176_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v_a_2287_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2181_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2181_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
lean_dec(v_a_2176_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
v___x_2295_ = lean_box(0);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2295_);
v___x_2297_ = v___x_2178_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_inst___u03b1_1906_);
lean_dec_ref(v_00_u03b1_1905_);
return v___x_2175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___boxed(lean_object* v_00_u03b1_2303_, lean_object* v_inst___u03b1_2304_, lean_object* v_e_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_Meta_Monotonicity_solveMonoCall(v_00_u03b1_2303_, v_inst___u03b1_2304_, v_e_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(lean_object* v_e_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_Expr_hasMVar(v_e_2312_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_e_2312_);
return v___x_2316_;
}
else
{
lean_object* v___x_2317_; lean_object* v_mctx_2318_; lean_object* v___x_2319_; lean_object* v_fst_2320_; lean_object* v_snd_2321_; lean_object* v___x_2322_; lean_object* v_cache_2323_; lean_object* v_zetaDeltaFVarIds_2324_; lean_object* v_postponed_2325_; lean_object* v_diag_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
v___x_2317_ = lean_st_ref_get(v___y_2313_);
v_mctx_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc_ref(v_mctx_2318_);
lean_dec(v___x_2317_);
v___x_2319_ = l_Lean_instantiateMVarsCore(v_mctx_2318_, v_e_2312_);
v_fst_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_fst_2320_);
v_snd_2321_ = lean_ctor_get(v___x_2319_, 1);
lean_inc(v_snd_2321_);
lean_dec_ref(v___x_2319_);
v___x_2322_ = lean_st_ref_take(v___y_2313_);
v_cache_2323_ = lean_ctor_get(v___x_2322_, 1);
v_zetaDeltaFVarIds_2324_ = lean_ctor_get(v___x_2322_, 2);
v_postponed_2325_ = lean_ctor_get(v___x_2322_, 3);
v_diag_2326_ = lean_ctor_get(v___x_2322_, 4);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v___x_2322_, 0);
lean_dec(v_unused_2336_);
v___x_2328_ = v___x_2322_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_diag_2326_);
lean_inc(v_postponed_2325_);
lean_inc(v_zetaDeltaFVarIds_2324_);
lean_inc(v_cache_2323_);
lean_dec(v___x_2322_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v_snd_2321_);
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_snd_2321_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_cache_2323_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_zetaDeltaFVarIds_2324_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_postponed_2325_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_diag_2326_);
v___x_2331_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_st_ref_set(v___y_2313_, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_fst_2320_);
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg___boxed(lean_object* v_e_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(v_e_2337_, v___y_2338_);
lean_dec(v___y_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0(lean_object* v_e_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(v_e_2341_, v___y_2343_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___boxed(lean_object* v_e_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0(v_e_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(lean_object* v_cls_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_options_2361_; uint8_t v_hasTrace_2362_; 
v_options_2361_ = lean_ctor_get(v___y_2359_, 2);
v_hasTrace_2362_ = lean_ctor_get_uint8(v_options_2361_, sizeof(void*)*1);
if (v_hasTrace_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec(v_cls_2358_);
v___x_2363_ = lean_box(v_hasTrace_2362_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v_inheritedTraceOptions_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_inheritedTraceOptions_2365_ = lean_ctor_get(v___y_2359_, 13);
v___x_2366_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__1));
v___x_2367_ = l_Lean_Name_append(v___x_2366_, v_cls_2358_);
v___x_2368_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2365_, v_options_2361_, v___x_2367_);
lean_dec(v___x_2367_);
v___x_2369_ = lean_box(v___x_2368_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___boxed(lean_object* v_cls_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_2371_, v___y_2372_);
lean_dec_ref(v___y_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2(lean_object* v_cls_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_2375_, v___y_2378_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___boxed(lean_object* v_cls_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2(v_cls_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0(lean_object* v_k_2389_, lean_object* v_b_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_apply_6(v_k_2389_, v_b_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, lean_box(0));
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0___boxed(lean_object* v_k_2397_, lean_object* v_b_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0(v_k_2397_, v_b_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(lean_object* v_name_2405_, lean_object* v_type_2406_, lean_object* v_val_2407_, lean_object* v_k_2408_, uint8_t v_nondep_2409_, uint8_t v_kind_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___f_2416_; lean_object* v___x_2417_; 
v___f_2416_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2416_, 0, v_k_2408_);
v___x_2417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2405_, v_type_2406_, v_val_2407_, v___f_2416_, v_nondep_2409_, v_kind_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2417_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2417_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___boxed(lean_object* v_name_2434_, lean_object* v_type_2435_, lean_object* v_val_2436_, lean_object* v_k_2437_, lean_object* v_nondep_2438_, lean_object* v_kind_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v_nondep_boxed_2445_; uint8_t v_kind_boxed_2446_; lean_object* v_res_2447_; 
v_nondep_boxed_2445_ = lean_unbox(v_nondep_2438_);
v_kind_boxed_2446_ = lean_unbox(v_kind_2439_);
v_res_2447_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(v_name_2434_, v_type_2435_, v_val_2436_, v_k_2437_, v_nondep_boxed_2445_, v_kind_boxed_2446_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9(lean_object* v_00_u03b1_2448_, lean_object* v_name_2449_, lean_object* v_type_2450_, lean_object* v_val_2451_, lean_object* v_k_2452_, uint8_t v_nondep_2453_, uint8_t v_kind_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(v_name_2449_, v_type_2450_, v_val_2451_, v_k_2452_, v_nondep_2453_, v_kind_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_name_2462_, lean_object* v_type_2463_, lean_object* v_val_2464_, lean_object* v_k_2465_, lean_object* v_nondep_2466_, lean_object* v_kind_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
uint8_t v_nondep_boxed_2473_; uint8_t v_kind_boxed_2474_; lean_object* v_res_2475_; 
v_nondep_boxed_2473_ = lean_unbox(v_nondep_2466_);
v_kind_boxed_2474_ = lean_unbox(v_kind_2467_);
v_res_2475_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9(v_00_u03b1_2461_, v_name_2462_, v_type_2463_, v_val_2464_, v_k_2465_, v_nondep_boxed_2473_, v_kind_boxed_2474_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(lean_object* v_mvarId_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2476_, v_x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
v_a_2492_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2483_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2483_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg___boxed(lean_object* v_mvarId_2500_, lean_object* v_x_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(v_mvarId_2500_, v_x_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10(lean_object* v_00_u03b1_2508_, lean_object* v_mvarId_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(v_mvarId_2509_, v_x_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___boxed(lean_object* v_00_u03b1_2517_, lean_object* v_mvarId_2518_, lean_object* v_x_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10(v_00_u03b1_2517_, v_mvarId_2518_, v_x_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14___redArg(lean_object* v_x_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v_ks_2530_; lean_object* v_vs_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2555_; 
v_ks_2530_ = lean_ctor_get(v_x_2526_, 0);
v_vs_2531_ = lean_ctor_get(v_x_2526_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_x_2526_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2533_ = v_x_2526_;
v_isShared_2534_ = v_isSharedCheck_2555_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_vs_2531_);
lean_inc(v_ks_2530_);
lean_dec(v_x_2526_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2555_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = lean_array_get_size(v_ks_2530_);
v___x_2536_ = lean_nat_dec_lt(v_x_2527_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_dec(v_x_2527_);
v___x_2537_ = lean_array_push(v_ks_2530_, v_x_2528_);
v___x_2538_ = lean_array_push(v_vs_2531_, v_x_2529_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2538_);
lean_ctor_set(v___x_2533_, 0, v___x_2537_);
v___x_2540_ = v___x_2533_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
else
{
lean_object* v_k_x27_2542_; uint8_t v___x_2543_; 
v_k_x27_2542_ = lean_array_fget_borrowed(v_ks_2530_, v_x_2527_);
v___x_2543_ = l_Lean_instBEqMVarId_beq(v_x_2528_, v_k_x27_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2545_; 
if (v_isShared_2534_ == 0)
{
v___x_2545_ = v___x_2533_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_ks_2530_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_vs_2531_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v_x_2527_, v___x_2546_);
lean_dec(v_x_2527_);
v_x_2526_ = v___x_2545_;
v_x_2527_ = v___x_2547_;
goto _start;
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2550_ = lean_array_fset(v_ks_2530_, v_x_2527_, v_x_2528_);
v___x_2551_ = lean_array_fset(v_vs_2531_, v_x_2527_, v_x_2529_);
lean_dec(v_x_2527_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2551_);
lean_ctor_set(v___x_2533_, 0, v___x_2550_);
v___x_2553_ = v___x_2533_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13___redArg(lean_object* v_n_2556_, lean_object* v_k_2557_, lean_object* v_v_2558_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14___redArg(v_n_2556_, v___x_2559_, v_k_2557_, v_v_2558_);
return v___x_2560_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(lean_object* v_x_2562_, size_t v_x_2563_, size_t v_x_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_){
_start:
{
if (lean_obj_tag(v_x_2562_) == 0)
{
lean_object* v_es_2567_; size_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; lean_object* v_j_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v_es_2567_ = lean_ctor_get(v_x_2562_, 0);
v___x_2568_ = ((size_t)5ULL);
v___x_2569_ = ((size_t)1ULL);
v___x_2570_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2571_ = lean_usize_land(v_x_2563_, v___x_2570_);
v_j_2572_ = lean_usize_to_nat(v___x_2571_);
v___x_2573_ = lean_array_get_size(v_es_2567_);
v___x_2574_ = lean_nat_dec_lt(v_j_2572_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_dec(v_j_2572_);
lean_dec(v_x_2566_);
lean_dec(v_x_2565_);
return v_x_2562_;
}
else
{
lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2611_; 
lean_inc_ref(v_es_2567_);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_x_2562_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v_x_2562_, 0);
lean_dec(v_unused_2612_);
v___x_2576_ = v_x_2562_;
v_isShared_2577_ = v_isSharedCheck_2611_;
goto v_resetjp_2575_;
}
else
{
lean_dec(v_x_2562_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2611_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_v_2578_; lean_object* v___x_2579_; lean_object* v_xs_x27_2580_; lean_object* v___y_2582_; 
v_v_2578_ = lean_array_fget(v_es_2567_, v_j_2572_);
v___x_2579_ = lean_box(0);
v_xs_x27_2580_ = lean_array_fset(v_es_2567_, v_j_2572_, v___x_2579_);
switch(lean_obj_tag(v_v_2578_))
{
case 0:
{
lean_object* v_key_2587_; lean_object* v_val_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2598_; 
v_key_2587_ = lean_ctor_get(v_v_2578_, 0);
v_val_2588_ = lean_ctor_get(v_v_2578_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_v_2578_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2590_ = v_v_2578_;
v_isShared_2591_ = v_isSharedCheck_2598_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_val_2588_);
lean_inc(v_key_2587_);
lean_dec(v_v_2578_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2598_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint8_t v___x_2592_; 
v___x_2592_ = l_Lean_instBEqMVarId_beq(v_x_2565_, v_key_2587_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_del_object(v___x_2590_);
v___x_2593_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2587_, v_val_2588_, v_x_2565_, v_x_2566_);
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
v___y_2582_ = v___x_2594_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2596_; 
lean_dec(v_val_2588_);
lean_dec(v_key_2587_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 1, v_x_2566_);
lean_ctor_set(v___x_2590_, 0, v_x_2565_);
v___x_2596_ = v___x_2590_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_x_2565_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_x_2566_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
v___y_2582_ = v___x_2596_;
goto v___jp_2581_;
}
}
}
}
case 1:
{
lean_object* v_node_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2609_; 
v_node_2599_ = lean_ctor_get(v_v_2578_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_v_2578_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2601_ = v_v_2578_;
v_isShared_2602_ = v_isSharedCheck_2609_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_node_2599_);
lean_dec(v_v_2578_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2609_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2603_ = lean_usize_shift_right(v_x_2563_, v___x_2568_);
v___x_2604_ = lean_usize_add(v_x_2564_, v___x_2569_);
v___x_2605_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_node_2599_, v___x_2603_, v___x_2604_, v_x_2565_, v_x_2566_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2605_);
v___x_2607_ = v___x_2601_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
v___y_2582_ = v___x_2607_;
goto v___jp_2581_;
}
}
}
default: 
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v_x_2565_);
lean_ctor_set(v___x_2610_, 1, v_x_2566_);
v___y_2582_ = v___x_2610_;
goto v___jp_2581_;
}
}
v___jp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = lean_array_fset(v_xs_x27_2580_, v_j_2572_, v___y_2582_);
lean_dec(v_j_2572_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2583_);
v___x_2585_ = v___x_2576_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v_ks_2613_; lean_object* v_vs_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2634_; 
v_ks_2613_ = lean_ctor_get(v_x_2562_, 0);
v_vs_2614_ = lean_ctor_get(v_x_2562_, 1);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_x_2562_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2616_ = v_x_2562_;
v_isShared_2617_ = v_isSharedCheck_2634_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_vs_2614_);
lean_inc(v_ks_2613_);
lean_dec(v_x_2562_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2634_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_ks_2613_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_vs_2614_);
v___x_2619_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v_newNode_2620_; uint8_t v___y_2622_; size_t v___x_2628_; uint8_t v___x_2629_; 
v_newNode_2620_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13___redArg(v___x_2619_, v_x_2565_, v_x_2566_);
v___x_2628_ = ((size_t)7ULL);
v___x_2629_ = lean_usize_dec_le(v___x_2628_, v_x_2564_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2630_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2620_);
v___x_2631_ = lean_unsigned_to_nat(4u);
v___x_2632_ = lean_nat_dec_lt(v___x_2630_, v___x_2631_);
lean_dec(v___x_2630_);
v___y_2622_ = v___x_2632_;
goto v___jp_2621_;
}
else
{
v___y_2622_ = v___x_2629_;
goto v___jp_2621_;
}
v___jp_2621_:
{
if (v___y_2622_ == 0)
{
lean_object* v_ks_2623_; lean_object* v_vs_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_ks_2623_ = lean_ctor_get(v_newNode_2620_, 0);
lean_inc_ref(v_ks_2623_);
v_vs_2624_ = lean_ctor_get(v_newNode_2620_, 1);
lean_inc_ref(v_vs_2624_);
lean_dec_ref(v_newNode_2620_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0);
v___x_2627_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(v_x_2564_, v_ks_2623_, v_vs_2624_, v___x_2625_, v___x_2626_);
lean_dec_ref(v_vs_2624_);
lean_dec_ref(v_ks_2623_);
return v___x_2627_;
}
else
{
return v_newNode_2620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(size_t v_depth_2635_, lean_object* v_keys_2636_, lean_object* v_vals_2637_, lean_object* v_i_2638_, lean_object* v_entries_2639_){
_start:
{
lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2640_ = lean_array_get_size(v_keys_2636_);
v___x_2641_ = lean_nat_dec_lt(v_i_2638_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_dec(v_i_2638_);
return v_entries_2639_;
}
else
{
lean_object* v_k_2642_; lean_object* v_v_2643_; uint64_t v___x_2644_; size_t v_h_2645_; size_t v___x_2646_; lean_object* v___x_2647_; size_t v___x_2648_; size_t v___x_2649_; size_t v___x_2650_; size_t v_h_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_k_2642_ = lean_array_fget_borrowed(v_keys_2636_, v_i_2638_);
v_v_2643_ = lean_array_fget_borrowed(v_vals_2637_, v_i_2638_);
v___x_2644_ = l_Lean_instHashableMVarId_hash(v_k_2642_);
v_h_2645_ = lean_uint64_to_usize(v___x_2644_);
v___x_2646_ = ((size_t)5ULL);
v___x_2647_ = lean_unsigned_to_nat(1u);
v___x_2648_ = ((size_t)1ULL);
v___x_2649_ = lean_usize_sub(v_depth_2635_, v___x_2648_);
v___x_2650_ = lean_usize_mul(v___x_2646_, v___x_2649_);
v_h_2651_ = lean_usize_shift_right(v_h_2645_, v___x_2650_);
v___x_2652_ = lean_nat_add(v_i_2638_, v___x_2647_);
lean_dec(v_i_2638_);
lean_inc(v_v_2643_);
lean_inc(v_k_2642_);
v___x_2653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_entries_2639_, v_h_2651_, v_depth_2635_, v_k_2642_, v_v_2643_);
v_i_2638_ = v___x_2652_;
v_entries_2639_ = v___x_2653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg___boxed(lean_object* v_depth_2655_, lean_object* v_keys_2656_, lean_object* v_vals_2657_, lean_object* v_i_2658_, lean_object* v_entries_2659_){
_start:
{
size_t v_depth_boxed_2660_; lean_object* v_res_2661_; 
v_depth_boxed_2660_ = lean_unbox_usize(v_depth_2655_);
lean_dec(v_depth_2655_);
v_res_2661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(v_depth_boxed_2660_, v_keys_2656_, v_vals_2657_, v_i_2658_, v_entries_2659_);
lean_dec_ref(v_vals_2657_);
lean_dec_ref(v_keys_2656_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
size_t v_x_41692__boxed_2667_; size_t v_x_41693__boxed_2668_; lean_object* v_res_2669_; 
v_x_41692__boxed_2667_ = lean_unbox_usize(v_x_2663_);
lean_dec(v_x_2663_);
v_x_41693__boxed_2668_ = lean_unbox_usize(v_x_2664_);
lean_dec(v_x_2664_);
v_res_2669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_x_2662_, v_x_41692__boxed_2667_, v_x_41693__boxed_2668_, v_x_2665_, v_x_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1___redArg(lean_object* v_x_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_){
_start:
{
uint64_t v___x_2673_; size_t v___x_2674_; size_t v___x_2675_; lean_object* v___x_2676_; 
v___x_2673_ = l_Lean_instHashableMVarId_hash(v_x_2671_);
v___x_2674_ = lean_uint64_to_usize(v___x_2673_);
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_x_2670_, v___x_2674_, v___x_2675_, v_x_2671_, v_x_2672_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(lean_object* v_mvarId_2677_, lean_object* v_val_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; lean_object* v_mctx_2682_; lean_object* v_cache_2683_; lean_object* v_zetaDeltaFVarIds_2684_; lean_object* v_postponed_2685_; lean_object* v_diag_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2713_; 
v___x_2681_ = lean_st_ref_take(v___y_2679_);
v_mctx_2682_ = lean_ctor_get(v___x_2681_, 0);
v_cache_2683_ = lean_ctor_get(v___x_2681_, 1);
v_zetaDeltaFVarIds_2684_ = lean_ctor_get(v___x_2681_, 2);
v_postponed_2685_ = lean_ctor_get(v___x_2681_, 3);
v_diag_2686_ = lean_ctor_get(v___x_2681_, 4);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2688_ = v___x_2681_;
v_isShared_2689_ = v_isSharedCheck_2713_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_diag_2686_);
lean_inc(v_postponed_2685_);
lean_inc(v_zetaDeltaFVarIds_2684_);
lean_inc(v_cache_2683_);
lean_inc(v_mctx_2682_);
lean_dec(v___x_2681_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2713_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_depth_2690_; lean_object* v_levelAssignDepth_2691_; lean_object* v_mvarCounter_2692_; lean_object* v_lDepth_2693_; lean_object* v_decls_2694_; lean_object* v_userNames_2695_; lean_object* v_lAssignment_2696_; lean_object* v_eAssignment_2697_; lean_object* v_dAssignment_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2712_; 
v_depth_2690_ = lean_ctor_get(v_mctx_2682_, 0);
v_levelAssignDepth_2691_ = lean_ctor_get(v_mctx_2682_, 1);
v_mvarCounter_2692_ = lean_ctor_get(v_mctx_2682_, 2);
v_lDepth_2693_ = lean_ctor_get(v_mctx_2682_, 3);
v_decls_2694_ = lean_ctor_get(v_mctx_2682_, 4);
v_userNames_2695_ = lean_ctor_get(v_mctx_2682_, 5);
v_lAssignment_2696_ = lean_ctor_get(v_mctx_2682_, 6);
v_eAssignment_2697_ = lean_ctor_get(v_mctx_2682_, 7);
v_dAssignment_2698_ = lean_ctor_get(v_mctx_2682_, 8);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_mctx_2682_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2700_ = v_mctx_2682_;
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_dAssignment_2698_);
lean_inc(v_eAssignment_2697_);
lean_inc(v_lAssignment_2696_);
lean_inc(v_userNames_2695_);
lean_inc(v_decls_2694_);
lean_inc(v_lDepth_2693_);
lean_inc(v_mvarCounter_2692_);
lean_inc(v_levelAssignDepth_2691_);
lean_inc(v_depth_2690_);
lean_dec(v_mctx_2682_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1___redArg(v_eAssignment_2697_, v_mvarId_2677_, v_val_2678_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 7, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_depth_2690_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_levelAssignDepth_2691_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_mvarCounter_2692_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_lDepth_2693_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_decls_2694_);
lean_ctor_set(v_reuseFailAlloc_2711_, 5, v_userNames_2695_);
lean_ctor_set(v_reuseFailAlloc_2711_, 6, v_lAssignment_2696_);
lean_ctor_set(v_reuseFailAlloc_2711_, 7, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2711_, 8, v_dAssignment_2698_);
v___x_2704_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2704_);
v___x_2706_ = v___x_2688_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_cache_2683_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_zetaDeltaFVarIds_2684_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v_postponed_2685_);
lean_ctor_set(v_reuseFailAlloc_2710_, 4, v_diag_2686_);
v___x_2706_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_st_ref_set(v___y_2679_, v___x_2706_);
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg___boxed(lean_object* v_mvarId_2714_, lean_object* v_val_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_mvarId_2714_, v_val_2715_, v___y_2716_);
lean_dec(v___y_2716_);
return v_res_2718_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2720_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__2));
v___x_2721_ = lean_unsigned_to_nat(20u);
v___x_2722_ = lean_unsigned_to_nat(1918u);
v___x_2723_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__0));
v___x_2724_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__0));
v___x_2725_ = l_mkPanicMessageWithDecl(v___x_2724_, v___x_2723_, v___x_2722_, v___x_2721_, v___x_2720_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0(lean_object* v_a_2726_, uint8_t v___x_2727_, uint8_t v___x_2728_, lean_object* v_goal_2729_, lean_object* v___x_2730_, lean_object* v_body_2731_, lean_object* v_x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___y_2739_; 
if (lean_obj_tag(v___x_2730_) == 6)
{
lean_object* v_binderName_2760_; lean_object* v_binderType_2761_; lean_object* v_body_2762_; uint8_t v_binderInfo_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___y_2767_; size_t v___x_2771_; size_t v___x_2772_; uint8_t v___x_2773_; 
v_binderName_2760_ = lean_ctor_get(v___x_2730_, 0);
v_binderType_2761_ = lean_ctor_get(v___x_2730_, 1);
v_body_2762_ = lean_ctor_get(v___x_2730_, 2);
v_binderInfo_2763_ = lean_ctor_get_uint8(v___x_2730_, sizeof(void*)*3 + 8);
v___x_2764_ = l_Lean_Expr_bindingDomain_x21(v___x_2730_);
v___x_2765_ = lean_expr_instantiate1(v_body_2731_, v_x_2732_);
v___x_2771_ = lean_ptr_addr(v_binderType_2761_);
v___x_2772_ = lean_ptr_addr(v___x_2764_);
v___x_2773_ = lean_usize_dec_eq(v___x_2771_, v___x_2772_);
if (v___x_2773_ == 0)
{
v___y_2767_ = v___x_2773_;
goto v___jp_2766_;
}
else
{
size_t v___x_2774_; size_t v___x_2775_; uint8_t v___x_2776_; 
v___x_2774_ = lean_ptr_addr(v_body_2762_);
v___x_2775_ = lean_ptr_addr(v___x_2765_);
v___x_2776_ = lean_usize_dec_eq(v___x_2774_, v___x_2775_);
v___y_2767_ = v___x_2776_;
goto v___jp_2766_;
}
v___jp_2766_:
{
if (v___y_2767_ == 0)
{
lean_object* v___x_2768_; 
lean_inc(v_binderName_2760_);
lean_dec_ref(v___x_2730_);
v___x_2768_ = l_Lean_Expr_lam___override(v_binderName_2760_, v___x_2764_, v___x_2765_, v_binderInfo_2763_);
v___y_2739_ = v___x_2768_;
goto v___jp_2738_;
}
else
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2763_, v_binderInfo_2763_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_inc(v_binderName_2760_);
lean_dec_ref(v___x_2730_);
v___x_2770_ = l_Lean_Expr_lam___override(v_binderName_2760_, v___x_2764_, v___x_2765_, v_binderInfo_2763_);
v___y_2739_ = v___x_2770_;
goto v___jp_2738_;
}
else
{
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2764_);
v___y_2739_ = v___x_2730_;
goto v___jp_2738_;
}
}
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_dec_ref(v___x_2730_);
v___x_2777_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1);
v___x_2778_ = l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(v___x_2777_);
v___y_2739_ = v___x_2778_;
goto v___jp_2738_;
}
v___jp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2740_ = l_Lean_Expr_appFn_x21(v_a_2726_);
v___x_2741_ = l_Lean_Expr_app___override(v___x_2740_, v___y_2739_);
v___x_2742_ = lean_box(0);
lean_inc_ref(v___y_2733_);
v___x_2743_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2741_, v___x_2742_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2743_);
v___x_2745_ = lean_unsigned_to_nat(1u);
v___x_2746_ = lean_mk_empty_array_with_capacity(v___x_2745_);
v___x_2747_ = lean_array_push(v___x_2746_, v_x_2732_);
v___x_2748_ = 1;
lean_inc(v_a_2744_);
v___x_2749_ = l_Lean_Meta_mkLetFVars(v___x_2747_, v_a_2744_, v___x_2727_, v___x_2728_, v___x_2748_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v___x_2747_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
v___x_2751_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_2729_, v_a_2750_, v___y_2734_);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; 
v_unused_2759_ = lean_ctor_get(v___x_2751_, 0);
lean_dec(v_unused_2759_);
v___x_2753_ = v___x_2751_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_dec(v___x_2751_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v_a_2744_);
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2744_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_dec(v_a_2744_);
lean_dec(v_goal_2729_);
return v___x_2749_;
}
}
else
{
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_x_2732_);
lean_dec(v_goal_2729_);
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___boxed(lean_object* v_a_2779_, lean_object* v___x_2780_, lean_object* v___x_2781_, lean_object* v_goal_2782_, lean_object* v___x_2783_, lean_object* v_body_2784_, lean_object* v_x_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
uint8_t v___x_41922__boxed_2791_; uint8_t v___x_41923__boxed_2792_; lean_object* v_res_2793_; 
v___x_41922__boxed_2791_ = lean_unbox(v___x_2780_);
v___x_41923__boxed_2792_ = lean_unbox(v___x_2781_);
v_res_2793_ = l_Lean_Meta_Monotonicity_solveMonoStep___lam__0(v_a_2779_, v___x_41922__boxed_2791_, v___x_41923__boxed_2792_, v_goal_2782_, v___x_2783_, v_body_2784_, v_x_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v_body_2784_);
lean_dec_ref(v_a_2779_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__1(lean_object* v___x_2794_, lean_object* v_f_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_expr_instantiate1(v___x_2794_, v_f_2795_);
v___x_2802_ = l_Lean_Meta_Monotonicity_findMonoThms(v___x_2801_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__1___boxed(lean_object* v___x_2803_, lean_object* v_f_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_Meta_Monotonicity_solveMonoStep___lam__1(v___x_2803_, v_f_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec_ref(v_f_2804_);
lean_dec_ref(v___x_2803_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7(uint8_t v___x_2811_, size_t v_sz_2812_, size_t v_i_2813_, lean_object* v_bs_2814_){
_start:
{
uint8_t v___x_2815_; 
v___x_2815_ = lean_usize_dec_lt(v_i_2813_, v_sz_2812_);
if (v___x_2815_ == 0)
{
return v_bs_2814_;
}
else
{
lean_object* v_v_2816_; lean_object* v___x_2817_; lean_object* v_bs_x27_2818_; lean_object* v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
v_v_2816_ = lean_array_uget(v_bs_2814_, v_i_2813_);
v___x_2817_ = lean_unsigned_to_nat(0u);
v_bs_x27_2818_ = lean_array_uset(v_bs_2814_, v_i_2813_, v___x_2817_);
v___x_2819_ = l_Lean_MessageData_ofConstName(v_v_2816_, v___x_2811_);
v___x_2820_ = ((size_t)1ULL);
v___x_2821_ = lean_usize_add(v_i_2813_, v___x_2820_);
v___x_2822_ = lean_array_uset(v_bs_x27_2818_, v_i_2813_, v___x_2819_);
v_i_2813_ = v___x_2821_;
v_bs_2814_ = v___x_2822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7___boxed(lean_object* v___x_2824_, lean_object* v_sz_2825_, lean_object* v_i_2826_, lean_object* v_bs_2827_){
_start:
{
uint8_t v___x_42066__boxed_2828_; size_t v_sz_boxed_2829_; size_t v_i_boxed_2830_; lean_object* v_res_2831_; 
v___x_42066__boxed_2828_ = lean_unbox(v___x_2824_);
v_sz_boxed_2829_ = lean_unbox_usize(v_sz_2825_);
lean_dec(v_sz_2825_);
v_i_boxed_2830_ = lean_unbox_usize(v_i_2826_);
lean_dec(v_i_2826_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7(v___x_42066__boxed_2828_, v_sz_boxed_2829_, v_i_boxed_2830_, v_bs_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(lean_object* v_upperBound_2835_, lean_object* v___x_2836_, uint8_t v___x_2837_, lean_object* v_a_2838_, lean_object* v_b_2839_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_nat_dec_lt(v_a_2838_, v_upperBound_2835_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
lean_dec(v_a_2838_);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_b_2839_);
return v___x_2842_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
lean_dec_ref(v_b_2839_);
v___x_2843_ = lean_box(0);
v___x_2844_ = l_Lean_instInhabitedExpr;
v___x_2845_ = lean_array_get_borrowed(v___x_2844_, v___x_2836_, v_a_2838_);
v___x_2846_ = l_Lean_Expr_hasLooseBVars(v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___closed__0));
v___x_2848_ = lean_unsigned_to_nat(1u);
v___x_2849_ = lean_nat_add(v_a_2838_, v___x_2848_);
lean_dec(v_a_2838_);
v_a_2838_ = v___x_2849_;
v_b_2839_ = v___x_2847_;
goto _start;
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec(v_a_2838_);
v___x_2851_ = lean_box(v___x_2837_);
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___x_2843_);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___boxed(lean_object* v_upperBound_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v_a_2858_, lean_object* v_b_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v___x_42091__boxed_2861_; lean_object* v_res_2862_; 
v___x_42091__boxed_2861_ = lean_unbox(v___x_2857_);
v_res_2862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(v_upperBound_2855_, v___x_2856_, v___x_42091__boxed_2861_, v_a_2858_, v_b_2859_);
lean_dec_ref(v___x_2856_);
lean_dec(v_upperBound_2855_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(lean_object* v_name_2863_, uint8_t v_bi_2864_, lean_object* v_type_2865_, lean_object* v_k_2866_, uint8_t v_kind_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___f_2873_; lean_object* v___x_2874_; 
v___f_2873_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2873_, 0, v_k_2866_);
v___x_2874_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2863_, v_bi_2864_, v_type_2865_, v___f_2873_, v_kind_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2883_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2874_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2874_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg___boxed(lean_object* v_name_2891_, lean_object* v_bi_2892_, lean_object* v_type_2893_, lean_object* v_k_2894_, lean_object* v_kind_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
uint8_t v_bi_boxed_2901_; uint8_t v_kind_boxed_2902_; lean_object* v_res_2903_; 
v_bi_boxed_2901_ = lean_unbox(v_bi_2892_);
v_kind_boxed_2902_ = lean_unbox(v_kind_2895_);
v_res_2903_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(v_name_2891_, v_bi_boxed_2901_, v_type_2893_, v_k_2894_, v_kind_boxed_2902_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(lean_object* v_name_2904_, lean_object* v_type_2905_, lean_object* v_k_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v___x_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = 0;
v___x_2913_ = 0;
v___x_2914_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(v_name_2904_, v___x_2912_, v_type_2905_, v_k_2906_, v___x_2913_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg___boxed(lean_object* v_name_2915_, lean_object* v_type_2916_, lean_object* v_k_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(v_name_2915_, v_type_2916_, v_k_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
return v_res_2923_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2924_; double v___x_2925_; 
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = lean_float_of_nat(v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(lean_object* v_cls_2928_, lean_object* v_msg_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_ref_2935_; lean_object* v___x_2936_; lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2981_; 
v_ref_2935_ = lean_ctor_get(v___y_2932_, 5);
v___x_2936_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0(v_msg_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2981_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2981_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v_traceState_2942_; lean_object* v_env_2943_; lean_object* v_nextMacroScope_2944_; lean_object* v_ngen_2945_; lean_object* v_auxDeclNGen_2946_; lean_object* v_cache_2947_; lean_object* v_messages_2948_; lean_object* v_infoState_2949_; lean_object* v_snapshotTasks_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2980_; 
v___x_2941_ = lean_st_ref_take(v___y_2933_);
v_traceState_2942_ = lean_ctor_get(v___x_2941_, 4);
v_env_2943_ = lean_ctor_get(v___x_2941_, 0);
v_nextMacroScope_2944_ = lean_ctor_get(v___x_2941_, 1);
v_ngen_2945_ = lean_ctor_get(v___x_2941_, 2);
v_auxDeclNGen_2946_ = lean_ctor_get(v___x_2941_, 3);
v_cache_2947_ = lean_ctor_get(v___x_2941_, 5);
v_messages_2948_ = lean_ctor_get(v___x_2941_, 6);
v_infoState_2949_ = lean_ctor_get(v___x_2941_, 7);
v_snapshotTasks_2950_ = lean_ctor_get(v___x_2941_, 8);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2952_ = v___x_2941_;
v_isShared_2953_ = v_isSharedCheck_2980_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_snapshotTasks_2950_);
lean_inc(v_infoState_2949_);
lean_inc(v_messages_2948_);
lean_inc(v_cache_2947_);
lean_inc(v_traceState_2942_);
lean_inc(v_auxDeclNGen_2946_);
lean_inc(v_ngen_2945_);
lean_inc(v_nextMacroScope_2944_);
lean_inc(v_env_2943_);
lean_dec(v___x_2941_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2980_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
uint64_t v_tid_2954_; lean_object* v_traces_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2979_; 
v_tid_2954_ = lean_ctor_get_uint64(v_traceState_2942_, sizeof(void*)*1);
v_traces_2955_ = lean_ctor_get(v_traceState_2942_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_traceState_2942_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2957_ = v_traceState_2942_;
v_isShared_2958_ = v_isSharedCheck_2979_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_traces_2955_);
lean_dec(v_traceState_2942_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2979_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; double v___x_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0);
v___x_2961_ = 0;
v___x_2962_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__8));
v___x_2963_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2963_, 0, v_cls_2928_);
lean_ctor_set(v___x_2963_, 1, v___x_2959_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
lean_ctor_set_float(v___x_2963_, sizeof(void*)*3, v___x_2960_);
lean_ctor_set_float(v___x_2963_, sizeof(void*)*3 + 8, v___x_2960_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*3 + 16, v___x_2961_);
v___x_2964_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__1));
v___x_2965_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v_a_2937_);
lean_ctor_set(v___x_2965_, 2, v___x_2964_);
lean_inc(v_ref_2935_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_ref_2935_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = l_Lean_PersistentArray_push___redArg(v_traces_2955_, v___x_2966_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___x_2967_);
v___x_2969_ = v___x_2957_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2967_);
lean_ctor_set_uint64(v_reuseFailAlloc_2978_, sizeof(void*)*1, v_tid_2954_);
v___x_2969_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2971_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 4, v___x_2969_);
v___x_2971_ = v___x_2952_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_env_2943_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_nextMacroScope_2944_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_ngen_2945_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_auxDeclNGen_2946_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2977_, 5, v_cache_2947_);
lean_ctor_set(v_reuseFailAlloc_2977_, 6, v_messages_2948_);
lean_ctor_set(v_reuseFailAlloc_2977_, 7, v_infoState_2949_);
lean_ctor_set(v_reuseFailAlloc_2977_, 8, v_snapshotTasks_2950_);
v___x_2971_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2972_ = lean_st_ref_set(v___y_2933_, v___x_2971_);
v___x_2973_ = lean_box(0);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2973_);
v___x_2975_ = v___x_2939_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___boxed(lean_object* v_cls_2982_, lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_2982_, v_msg_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(lean_object* v_a_2990_, lean_object* v_____r_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2990_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0___boxed(lean_object* v_a_2999_, lean_object* v_____r_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(v_a_2999_, v_____r_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3006_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__3));
v___x_3017_ = l_Lean_stringToMessageData(v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5(lean_object* v_goal_3018_, uint8_t v___x_3019_, lean_object* v_as_3020_, size_t v_sz_3021_, size_t v_i_3022_, lean_object* v_b_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_a_3030_; uint8_t v___x_3034_; 
v___x_3034_ = lean_usize_dec_lt(v_i_3022_, v_sz_3021_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v_goal_3018_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_b_3023_);
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_cls_3038_; lean_object* v___y_3040_; uint8_t v___y_3041_; lean_object* v_a_3065_; lean_object* v___y_3069_; lean_object* v_a_3080_; lean_object* v___x_3081_; 
lean_dec_ref(v_b_3023_);
v___x_3036_ = lean_box(0);
v___x_3037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__0));
v_cls_3038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2));
v_a_3080_ = lean_array_uget_borrowed(v_as_3020_, v_i_3022_);
lean_inc(v___y_3027_);
lean_inc_ref(v___y_3026_);
lean_inc(v___y_3025_);
lean_inc_ref(v___y_3024_);
lean_inc(v_a_3080_);
lean_inc(v_goal_3018_);
v___x_3081_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3018_, v_a_3080_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3083_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3081_);
v___x_3083_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3038_, v___y_3026_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; uint8_t v___x_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = lean_unbox(v_a_3084_);
lean_dec(v_a_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(v_a_3082_, v___x_3036_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
v___y_3069_ = v___x_3086_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3087_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4);
lean_inc(v_a_3080_);
v___x_3088_ = l_Lean_MessageData_ofConstName(v_a_3080_, v___x_3019_);
v___x_3089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3087_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3038_, v___x_3089_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(v_a_3082_, v_a_3091_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
v___y_3069_ = v___x_3092_;
goto v___jp_3068_;
}
else
{
lean_object* v_a_3093_; 
lean_dec(v_a_3082_);
v_a_3093_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3093_);
lean_dec_ref(v___x_3090_);
v_a_3065_ = v_a_3093_;
goto v___jp_3064_;
}
}
}
else
{
lean_object* v_a_3094_; 
lean_dec(v_a_3082_);
v_a_3094_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3094_);
lean_dec_ref(v___x_3083_);
v_a_3065_ = v_a_3094_;
goto v___jp_3064_;
}
}
else
{
lean_object* v_a_3095_; 
v_a_3095_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3095_);
lean_dec_ref(v___x_3081_);
v_a_3065_ = v_a_3095_;
goto v___jp_3064_;
}
v___jp_3039_:
{
if (v___y_3041_ == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3038_, v___y_3026_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; uint8_t v___x_3044_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = lean_unbox(v_a_3043_);
lean_dec(v_a_3043_);
if (v___x_3044_ == 0)
{
lean_dec_ref(v___y_3040_);
v_a_3030_ = v___x_3037_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = l_Lean_Exception_toMessageData(v___y_3040_);
v___x_3046_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3038_, v___x_3045_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_dec_ref(v___x_3046_);
v_a_3030_ = v___x_3037_;
goto v___jp_3029_;
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v_goal_3018_);
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v_goal_3018_);
v_a_3055_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3042_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3042_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v___x_3063_; 
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v_goal_3018_);
v___x_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___y_3040_);
return v___x_3063_;
}
}
v___jp_3064_:
{
uint8_t v___x_3066_; 
v___x_3066_ = l_Lean_Exception_isInterrupt(v_a_3065_);
if (v___x_3066_ == 0)
{
uint8_t v___x_3067_; 
lean_inc_ref(v_a_3065_);
v___x_3067_ = l_Lean_Exception_isRuntime(v_a_3065_);
v___y_3040_ = v_a_3065_;
v___y_3041_ = v___x_3067_;
goto v___jp_3039_;
}
else
{
v___y_3040_ = v_a_3065_;
v___y_3041_ = v___x_3066_;
goto v___jp_3039_;
}
}
v___jp_3068_:
{
if (lean_obj_tag(v___y_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3078_; 
v_a_3070_ = lean_ctor_get(v___y_3069_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___y_3069_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3072_ = v___y_3069_;
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___y_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
if (lean_obj_tag(v_a_3070_) == 1)
{
lean_object* v___x_3074_; lean_object* v___x_3076_; 
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v_goal_3018_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_a_3070_);
lean_ctor_set(v___x_3074_, 1, v___x_3036_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3074_);
v___x_3076_ = v___x_3072_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
else
{
lean_del_object(v___x_3072_);
lean_dec(v_a_3070_);
v_a_3030_ = v___x_3037_;
goto v___jp_3029_;
}
}
}
else
{
lean_object* v_a_3079_; 
v_a_3079_ = lean_ctor_get(v___y_3069_, 0);
lean_inc(v_a_3079_);
lean_dec_ref(v___y_3069_);
v_a_3065_ = v_a_3079_;
goto v___jp_3064_;
}
}
}
v___jp_3029_:
{
size_t v___x_3031_; size_t v___x_3032_; 
v___x_3031_ = ((size_t)1ULL);
v___x_3032_ = lean_usize_add(v_i_3022_, v___x_3031_);
v_i_3022_ = v___x_3032_;
v_b_3023_ = v_a_3030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___boxed(lean_object* v_goal_3096_, lean_object* v___x_3097_, lean_object* v_as_3098_, lean_object* v_sz_3099_, lean_object* v_i_3100_, lean_object* v_b_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
uint8_t v___x_42352__boxed_3107_; size_t v_sz_boxed_3108_; size_t v_i_boxed_3109_; lean_object* v_res_3110_; 
v___x_42352__boxed_3107_ = lean_unbox(v___x_3097_);
v_sz_boxed_3108_ = lean_unbox_usize(v_sz_3099_);
lean_dec(v_sz_3099_);
v_i_boxed_3109_ = lean_unbox_usize(v_i_3100_);
lean_dec(v_i_3100_);
v_res_3110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5(v_goal_3096_, v___x_42352__boxed_3107_, v_as_3098_, v_sz_boxed_3108_, v_i_boxed_3109_, v_b_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec_ref(v_as_3098_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__8(lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
if (lean_obj_tag(v_a_3111_) == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = l_List_reverse___redArg(v_a_3112_);
return v___x_3113_;
}
else
{
lean_object* v_head_3114_; lean_object* v_tail_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3123_; 
v_head_3114_ = lean_ctor_get(v_a_3111_, 0);
v_tail_3115_ = lean_ctor_get(v_a_3111_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_a_3111_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3117_ = v_a_3111_;
v_isShared_3118_ = v_isSharedCheck_3123_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_tail_3115_);
lean_inc(v_head_3114_);
lean_dec(v_a_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3123_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v_a_3112_);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_head_3114_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_a_3112_);
v___x_3120_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
v_a_3111_ = v_tail_3115_;
v_a_3112_ = v___x_3120_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__0));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2(void){
_start:
{
lean_object* v___x_3127_; lean_object* v_dummy_3128_; 
v___x_3127_ = lean_box(0);
v_dummy_3128_ = l_Lean_Expr_sort___override(v___x_3127_);
return v_dummy_3128_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__3));
v___x_3131_ = l_Lean_stringToMessageData(v___x_3130_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__5));
v___x_3134_ = l_Lean_stringToMessageData(v___x_3133_);
return v___x_3134_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__7));
v___x_3137_ = l_Lean_stringToMessageData(v___x_3136_);
return v___x_3137_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__9));
v___x_3140_ = l_Lean_stringToMessageData(v___x_3139_);
return v___x_3140_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__13));
v___x_3146_ = l_Lean_stringToMessageData(v___x_3145_);
return v___x_3146_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__15));
v___x_3149_ = l_Lean_stringToMessageData(v___x_3148_);
return v___x_3149_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__19));
v___x_3154_ = l_Lean_stringToMessageData(v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2(lean_object* v_cls_3155_, lean_object* v_goal_3156_, lean_object* v_failK_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; uint8_t v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; uint8_t v___y_3477_; uint8_t v___y_3478_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; uint8_t v___y_3567_; uint8_t v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; uint8_t v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; uint8_t v___y_3660_; lean_object* v_f_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___x_3755_; lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3775_; 
lean_inc(v_cls_3155_);
v___x_3755_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3155_, v___y_3160_);
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3775_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3775_;
goto v_resetjp_3757_;
}
v___jp_3163_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3168_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1);
v___x_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_goal_3156_);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_3170_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v___x_3171_;
}
v___jp_3172_:
{
lean_object* v___x_3181_; size_t v_sz_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v___x_3181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__0));
v_sz_3182_ = lean_array_size(v___y_3175_);
v___x_3183_ = ((size_t)0ULL);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v_goal_3156_);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5(v_goal_3156_, v___y_3173_, v___y_3175_, v_sz_3182_, v___x_3183_, v___x_3181_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3224_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3224_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3224_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v_fst_3189_; 
v_fst_3189_ = lean_ctor_get(v_a_3185_, 0);
lean_inc(v_fst_3189_);
lean_dec(v_a_3185_);
if (lean_obj_tag(v_fst_3189_) == 0)
{
lean_object* v___x_3190_; lean_object* v_env_3191_; lean_object* v___x_3192_; 
lean_del_object(v___x_3187_);
v___x_3190_ = lean_st_ref_get(v___y_3180_);
v_env_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc_ref(v_env_3191_);
lean_dec(v___x_3190_);
v___x_3192_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_3191_, v___y_3176_);
if (lean_obj_tag(v___x_3192_) == 1)
{
lean_object* v_val_3193_; lean_object* v_numDiscrs_3194_; lean_object* v_nargs_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_dummy_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_val_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_val_3193_);
lean_dec_ref(v___x_3192_);
v_numDiscrs_3194_ = lean_ctor_get(v_val_3193_, 1);
lean_inc(v_numDiscrs_3194_);
v_nargs_3195_ = l_Lean_Expr_getAppNumArgs(v___y_3176_);
v___x_3196_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_3193_);
lean_dec(v_val_3193_);
v___x_3197_ = lean_nat_add(v___x_3196_, v_numDiscrs_3194_);
lean_dec(v_numDiscrs_3194_);
v_dummy_3198_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2);
lean_inc(v_nargs_3195_);
v___x_3199_ = lean_mk_array(v_nargs_3195_, v_dummy_3198_);
v___x_3200_ = lean_unsigned_to_nat(1u);
v___x_3201_ = lean_nat_sub(v_nargs_3195_, v___x_3200_);
lean_dec(v_nargs_3195_);
lean_inc_ref(v___y_3176_);
v___x_3202_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3176_, v___x_3199_, v___x_3201_);
v___x_3203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(v___x_3197_, v___x_3202_, v___y_3173_, v___x_3196_, v___x_3181_);
lean_dec_ref(v___x_3202_);
lean_dec(v___x_3197_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v_fst_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3203_);
v_fst_3205_ = lean_ctor_get(v_a_3204_, 0);
lean_inc(v_fst_3205_);
lean_dec(v_a_3204_);
if (lean_obj_tag(v_fst_3205_) == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_failK_3157_);
v___x_3206_ = l_Lean_Meta_Split_splitMatch(v_goal_3156_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
return v___x_3206_;
}
else
{
lean_object* v_val_3207_; uint8_t v___x_3208_; 
v_val_3207_ = lean_ctor_get(v_fst_3205_, 0);
lean_inc(v_val_3207_);
lean_dec_ref(v_fst_3205_);
v___x_3208_ = lean_unbox(v_val_3207_);
lean_dec(v_val_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; 
lean_dec_ref(v___y_3176_);
lean_dec(v_goal_3156_);
v___x_3209_ = lean_apply_8(v_failK_3157_, lean_box(0), v___y_3174_, v___y_3175_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, lean_box(0));
return v___x_3209_;
}
else
{
lean_object* v___x_3210_; 
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_failK_3157_);
v___x_3210_ = l_Lean_Meta_Split_splitMatch(v_goal_3156_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
return v___x_3210_;
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
v_a_3211_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3203_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3203_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v___x_3219_; 
lean_dec(v___x_3192_);
lean_dec_ref(v___y_3176_);
lean_dec(v_goal_3156_);
v___x_3219_ = lean_apply_8(v_failK_3157_, lean_box(0), v___y_3174_, v___y_3175_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, lean_box(0));
return v___x_3219_;
}
}
else
{
lean_object* v_val_3220_; lean_object* v___x_3222_; 
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
v_val_3220_ = lean_ctor_get(v_fst_3189_, 0);
lean_inc(v_val_3220_);
lean_dec_ref(v_fst_3189_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v_val_3220_);
v___x_3222_ = v___x_3187_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_val_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
v_a_3225_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3184_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3184_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
v___jp_3233_:
{
lean_object* v___x_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3235_);
v___x_3239_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_3156_, v___y_3234_, v___y_3236_);
lean_dec(v___y_3236_);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3239_, 0);
lean_dec(v_unused_3248_);
v___x_3241_ = v___x_3239_;
v_isShared_3242_ = v_isSharedCheck_3247_;
goto v_resetjp_3240_;
}
else
{
lean_dec(v___x_3239_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3247_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = lean_box(0);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3243_);
v___x_3245_ = v___x_3241_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
v___jp_3249_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__0));
lean_inc(v___y_3255_);
lean_inc_ref(v___y_3254_);
lean_inc(v___y_3253_);
lean_inc_ref(v___y_3252_);
v___x_3257_ = lean_apply_8(v_failK_3157_, lean_box(0), v___y_3250_, v___x_3256_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, lean_box(0));
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_dec_ref(v___x_3257_);
v___y_3234_ = v___y_3251_;
v___y_3235_ = v___y_3252_;
v___y_3236_ = v___y_3253_;
v___y_3237_ = v___y_3254_;
v___y_3238_ = v___y_3255_;
goto v___jp_3233_;
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v_goal_3156_);
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
v___jp_3266_:
{
lean_object* v___x_3274_; 
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc_ref(v___y_3269_);
v___x_3274_ = lean_infer_type(v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
v___x_3276_ = l_Lean_Meta_isExprDefEq(v_a_3275_, v___y_3268_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; uint8_t v___x_3278_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
v___x_3278_ = lean_unbox(v_a_3277_);
lean_dec(v_a_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v_a_3280_; uint8_t v___x_3281_; 
lean_inc(v_cls_3155_);
v___x_3279_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3155_, v___y_3272_);
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref(v___x_3279_);
v___x_3281_ = lean_unbox(v_a_3280_);
lean_dec(v_a_3280_);
if (v___x_3281_ == 0)
{
lean_dec(v_cls_3155_);
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___y_3269_;
v___y_3252_ = v___y_3270_;
v___y_3253_ = v___y_3271_;
v___y_3254_ = v___y_3272_;
v___y_3255_ = v___y_3273_;
goto v___jp_3249_;
}
else
{
lean_object* v___x_3282_; 
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc_ref(v___y_3269_);
v___x_3282_ = lean_infer_type(v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref(v___x_3282_);
v___x_3284_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4);
lean_inc_ref(v___y_3269_);
v___x_3285_ = l_Lean_MessageData_ofExpr(v___y_3269_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = l_Lean_MessageData_ofExpr(v_a_3283_);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3155_, v___x_3292_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_dec_ref(v___x_3293_);
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___y_3269_;
v___y_3252_ = v___y_3270_;
v___y_3253_ = v___y_3271_;
v___y_3254_ = v___y_3272_;
v___y_3255_ = v___y_3273_;
goto v___jp_3249_;
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3302_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3282_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3282_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___y_3234_ = v___y_3269_;
v___y_3235_ = v___y_3270_;
v___y_3236_ = v___y_3271_;
v___y_3237_ = v___y_3272_;
v___y_3238_ = v___y_3273_;
goto v___jp_3233_;
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3310_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3276_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3276_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3318_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3274_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3274_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
v___jp_3326_:
{
uint8_t v___x_3339_; 
v___x_3339_ = l_Lean_Expr_isBVar(v___y_3331_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; 
lean_dec_ref(v___y_3333_);
lean_dec_ref(v___y_3327_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc_ref(v___y_3331_);
v___x_3340_ = l_Lean_Meta_Monotonicity_solveMonoCall(v___y_3334_, v___y_3330_, v___y_3331_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3340_);
if (lean_obj_tag(v_a_3341_) == 1)
{
lean_object* v_val_3342_; lean_object* v___x_3343_; lean_object* v_a_3344_; uint8_t v___x_3345_; 
lean_dec_ref(v___y_3328_);
v_val_3342_ = lean_ctor_get(v_a_3341_, 0);
lean_inc(v_val_3342_);
lean_dec_ref(v_a_3341_);
lean_inc(v_cls_3155_);
v___x_3343_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3155_, v___y_3337_);
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = lean_unbox(v_a_3344_);
lean_dec(v_a_3344_);
if (v___x_3345_ == 0)
{
lean_dec_ref(v___y_3331_);
v___y_3267_ = v___y_3329_;
v___y_3268_ = v___y_3332_;
v___y_3269_ = v_val_3342_;
v___y_3270_ = v___y_3335_;
v___y_3271_ = v___y_3336_;
v___y_3272_ = v___y_3337_;
v___y_3273_ = v___y_3338_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3346_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10);
v___x_3347_ = l_Lean_MessageData_ofExpr(v___y_3331_);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3_once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
lean_inc(v_val_3342_);
v___x_3351_ = l_Lean_indentExpr(v_val_3342_);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
lean_inc(v_cls_3155_);
v___x_3353_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3155_, v___x_3352_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_dec_ref(v___x_3353_);
v___y_3267_ = v___y_3329_;
v___y_3268_ = v___y_3332_;
v___y_3269_ = v_val_3342_;
v___y_3270_ = v___y_3335_;
v___y_3271_ = v___y_3336_;
v___y_3272_ = v___y_3337_;
v___y_3273_ = v___y_3338_;
goto v___jp_3266_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_val_3342_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v_a_3341_);
lean_dec_ref(v___y_3332_);
v___x_3362_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__12));
v___x_3363_ = l_Lean_Expr_bindingDomain_x21(v___y_3329_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
v___x_3364_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(v___x_3362_, v___x_3363_, v___y_3328_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v_a_3367_; uint8_t v___x_3368_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3364_);
lean_inc(v_cls_3155_);
v___x_3366_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3155_, v___y_3337_);
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref(v___x_3366_);
v___x_3368_ = lean_unbox(v_a_3367_);
lean_dec(v_a_3367_);
if (v___x_3368_ == 0)
{
lean_dec(v_cls_3155_);
v___y_3173_ = v___x_3339_;
v___y_3174_ = v___y_3329_;
v___y_3175_ = v_a_3365_;
v___y_3176_ = v___y_3331_;
v___y_3177_ = v___y_3335_;
v___y_3178_ = v___y_3336_;
v___y_3179_ = v___y_3337_;
v___y_3180_ = v___y_3338_;
goto v___jp_3172_;
}
else
{
lean_object* v___x_3369_; size_t v_sz_3370_; size_t v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3369_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14);
v_sz_3370_ = lean_array_size(v_a_3365_);
v___x_3371_ = ((size_t)0ULL);
lean_inc(v_a_3365_);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7(v___x_3339_, v_sz_3370_, v___x_3371_, v_a_3365_);
v___x_3373_ = lean_array_to_list(v___x_3372_);
v___x_3374_ = lean_box(0);
v___x_3375_ = l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__8(v___x_3373_, v___x_3374_);
v___x_3376_ = l_Lean_MessageData_ofList(v___x_3375_);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3369_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3155_, v___x_3377_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_dec_ref(v___x_3378_);
v___y_3173_ = v___x_3339_;
v___y_3174_ = v___y_3329_;
v___y_3175_ = v_a_3365_;
v___y_3176_ = v___y_3331_;
v___y_3177_ = v___y_3335_;
v___y_3178_ = v___y_3336_;
v___y_3179_ = v___y_3337_;
v___y_3180_ = v___y_3338_;
goto v___jp_3172_;
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_a_3365_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3331_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3331_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3387_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3364_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3364_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3395_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3340_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3340_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
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
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref(v___y_3334_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___x_3403_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__1));
v___x_3404_ = l_Lean_Name_mkStr3(v___y_3327_, v___y_3333_, v___x_3403_);
v___x_3405_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3156_, v___x_3404_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
return v___x_3405_;
}
}
v___jp_3406_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v___y_3407_);
v___x_3421_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16);
v___x_3422_ = l_Lean_MessageData_ofConstName(v___y_3413_, v___y_3416_);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_3425_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
v___jp_3435_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3442_ = l_Lean_Expr_appFn_x21(v___y_3439_);
lean_dec_ref(v___y_3439_);
v___x_3443_ = l_Lean_Expr_app___override(v___x_3442_, v___y_3441_);
v___x_3444_ = lean_box(0);
v___x_3445_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_3443_, v___x_3444_, v___y_3438_, v___y_3437_, v___y_3440_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3440_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3457_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v___x_3445_);
lean_inc(v_a_3446_);
v___x_3447_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_3156_, v_a_3446_, v___y_3437_);
lean_dec(v___y_3437_);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; 
v_unused_3458_ = lean_ctor_get(v___x_3447_, 0);
lean_dec(v_unused_3458_);
v___x_3449_ = v___x_3447_;
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v___x_3447_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3455_; 
v___x_3451_ = l_Lean_Expr_mvarId_x21(v_a_3446_);
lean_dec(v_a_3446_);
v___x_3452_ = lean_box(0);
v___x_3453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3453_);
v___x_3455_ = v___x_3449_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v___y_3437_);
lean_dec(v_goal_3156_);
v_a_3459_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3445_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3445_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
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
v___jp_3467_:
{
if (v___y_3478_ == 0)
{
lean_object* v___x_3479_; 
lean_dec_ref(v___y_3470_);
v___x_3479_ = l_Lean_Expr_lam___override(v___y_3475_, v___y_3472_, v___y_3474_, v___y_3477_);
v___y_3436_ = v___y_3469_;
v___y_3437_ = v___y_3468_;
v___y_3438_ = v___y_3471_;
v___y_3439_ = v___y_3473_;
v___y_3440_ = v___y_3476_;
v___y_3441_ = v___x_3479_;
goto v___jp_3435_;
}
else
{
uint8_t v___x_3480_; 
v___x_3480_ = l_Lean_instBEqBinderInfo_beq(v___y_3477_, v___y_3477_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec_ref(v___y_3470_);
v___x_3481_ = l_Lean_Expr_lam___override(v___y_3475_, v___y_3472_, v___y_3474_, v___y_3477_);
v___y_3436_ = v___y_3469_;
v___y_3437_ = v___y_3468_;
v___y_3438_ = v___y_3471_;
v___y_3439_ = v___y_3473_;
v___y_3440_ = v___y_3476_;
v___y_3441_ = v___x_3481_;
goto v___jp_3435_;
}
else
{
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec_ref(v___y_3472_);
v___y_3436_ = v___y_3469_;
v___y_3437_ = v___y_3468_;
v___y_3438_ = v___y_3471_;
v___y_3439_ = v___y_3473_;
v___y_3440_ = v___y_3476_;
v___y_3441_ = v___y_3470_;
goto v___jp_3435_;
}
}
}
v___jp_3482_:
{
if (lean_obj_tag(v___y_3486_) == 6)
{
lean_object* v_binderName_3491_; lean_object* v_binderType_3492_; lean_object* v_body_3493_; uint8_t v_binderInfo_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; size_t v___x_3497_; size_t v___x_3498_; uint8_t v___x_3499_; 
v_binderName_3491_ = lean_ctor_get(v___y_3486_, 0);
lean_inc(v_binderName_3491_);
v_binderType_3492_ = lean_ctor_get(v___y_3486_, 1);
v_body_3493_ = lean_ctor_get(v___y_3486_, 2);
v_binderInfo_3494_ = lean_ctor_get_uint8(v___y_3486_, sizeof(void*)*3 + 8);
v___x_3495_ = l_Lean_Expr_bindingDomain_x21(v___y_3486_);
v___x_3496_ = lean_expr_instantiate1(v___y_3485_, v___y_3489_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v___y_3485_);
v___x_3497_ = lean_ptr_addr(v_binderType_3492_);
v___x_3498_ = lean_ptr_addr(v___x_3495_);
v___x_3499_ = lean_usize_dec_eq(v___x_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
v___y_3468_ = v___y_3484_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3486_;
v___y_3471_ = v___y_3487_;
v___y_3472_ = v___x_3495_;
v___y_3473_ = v___y_3488_;
v___y_3474_ = v___x_3496_;
v___y_3475_ = v_binderName_3491_;
v___y_3476_ = v___y_3490_;
v___y_3477_ = v_binderInfo_3494_;
v___y_3478_ = v___x_3499_;
goto v___jp_3467_;
}
else
{
size_t v___x_3500_; size_t v___x_3501_; uint8_t v___x_3502_; 
v___x_3500_ = lean_ptr_addr(v_body_3493_);
v___x_3501_ = lean_ptr_addr(v___x_3496_);
v___x_3502_ = lean_usize_dec_eq(v___x_3500_, v___x_3501_);
v___y_3468_ = v___y_3484_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3486_;
v___y_3471_ = v___y_3487_;
v___y_3472_ = v___x_3495_;
v___y_3473_ = v___y_3488_;
v___y_3474_ = v___x_3496_;
v___y_3475_ = v_binderName_3491_;
v___y_3476_ = v___y_3490_;
v___y_3477_ = v_binderInfo_3494_;
v___y_3478_ = v___x_3502_;
goto v___jp_3467_;
}
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_dec_ref(v___y_3489_);
lean_dec_ref(v___y_3486_);
lean_dec_ref(v___y_3485_);
v___x_3503_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1);
v___x_3504_ = l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(v___x_3503_);
v___y_3436_ = v___y_3483_;
v___y_3437_ = v___y_3484_;
v___y_3438_ = v___y_3487_;
v___y_3439_ = v___y_3488_;
v___y_3440_ = v___y_3490_;
v___y_3441_ = v___x_3504_;
goto v___jp_3435_;
}
}
v___jp_3505_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3512_ = l_Lean_Expr_appFn_x21(v___y_3509_);
lean_dec_ref(v___y_3509_);
v___x_3513_ = l_Lean_Expr_app___override(v___x_3512_, v___y_3511_);
v___x_3514_ = lean_box(0);
v___x_3515_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_3513_, v___x_3514_, v___y_3508_, v___y_3507_, v___y_3510_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3510_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3527_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref(v___x_3515_);
lean_inc(v_a_3516_);
v___x_3517_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_3156_, v_a_3516_, v___y_3507_);
lean_dec(v___y_3507_);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; 
v_unused_3528_ = lean_ctor_get(v___x_3517_, 0);
lean_dec(v_unused_3528_);
v___x_3519_ = v___x_3517_;
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v___x_3517_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3521_ = l_Lean_Expr_mvarId_x21(v_a_3516_);
lean_dec(v_a_3516_);
v___x_3522_ = lean_box(0);
v___x_3523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3521_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3523_);
v___x_3525_ = v___x_3519_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec(v___y_3507_);
lean_dec(v_goal_3156_);
v_a_3529_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3515_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3515_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
v___jp_3537_:
{
if (v___y_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec_ref(v___y_3540_);
v___x_3549_ = l_Lean_Expr_lam___override(v___y_3542_, v___y_3544_, v___y_3546_, v___y_3545_);
v___y_3506_ = v___y_3539_;
v___y_3507_ = v___y_3538_;
v___y_3508_ = v___y_3541_;
v___y_3509_ = v___y_3543_;
v___y_3510_ = v___y_3547_;
v___y_3511_ = v___x_3549_;
goto v___jp_3505_;
}
else
{
uint8_t v___x_3550_; 
v___x_3550_ = l_Lean_instBEqBinderInfo_beq(v___y_3545_, v___y_3545_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref(v___y_3540_);
v___x_3551_ = l_Lean_Expr_lam___override(v___y_3542_, v___y_3544_, v___y_3546_, v___y_3545_);
v___y_3506_ = v___y_3539_;
v___y_3507_ = v___y_3538_;
v___y_3508_ = v___y_3541_;
v___y_3509_ = v___y_3543_;
v___y_3510_ = v___y_3547_;
v___y_3511_ = v___x_3551_;
goto v___jp_3505_;
}
else
{
lean_dec_ref(v___y_3546_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3542_);
v___y_3506_ = v___y_3539_;
v___y_3507_ = v___y_3538_;
v___y_3508_ = v___y_3541_;
v___y_3509_ = v___y_3543_;
v___y_3510_ = v___y_3547_;
v___y_3511_ = v___y_3540_;
goto v___jp_3505_;
}
}
}
v___jp_3552_:
{
if (v___y_3567_ == 0)
{
uint8_t v___x_3568_; 
v___x_3568_ = l_Lean_Expr_isMData(v___y_3566_);
if (v___x_3568_ == 0)
{
if (lean_obj_tag(v___y_3566_) == 8)
{
lean_object* v_declName_3569_; lean_object* v_type_3570_; lean_object* v_value_3571_; lean_object* v_body_3572_; uint8_t v_nondep_3573_; uint8_t v___x_3574_; 
lean_dec_ref(v___y_3565_);
lean_dec_ref(v___y_3563_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v_declName_3569_ = lean_ctor_get(v___y_3566_, 0);
lean_inc(v_declName_3569_);
v_type_3570_ = lean_ctor_get(v___y_3566_, 1);
lean_inc_ref(v_type_3570_);
v_value_3571_ = lean_ctor_get(v___y_3566_, 2);
lean_inc_ref(v_value_3571_);
v_body_3572_ = lean_ctor_get(v___y_3566_, 3);
lean_inc_ref(v_body_3572_);
v_nondep_3573_ = lean_ctor_get_uint8(v___y_3566_, sizeof(void*)*4 + 8);
lean_dec_ref(v___y_3566_);
v___x_3574_ = l_Lean_Expr_hasLooseBVars(v_type_3570_);
if (v___x_3574_ == 0)
{
uint8_t v___x_3575_; 
v___x_3575_ = l_Lean_Expr_hasLooseBVars(v_value_3571_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___f_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref(v___y_3557_);
v___x_3576_ = lean_box(v___y_3561_);
v___x_3577_ = lean_box(v___x_3575_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3578_, 0, v___y_3553_);
lean_closure_set(v___f_3578_, 1, v___x_3576_);
lean_closure_set(v___f_3578_, 2, v___x_3577_);
lean_closure_set(v___f_3578_, 3, v_goal_3156_);
lean_closure_set(v___f_3578_, 4, v___y_3554_);
lean_closure_set(v___f_3578_, 5, v_body_3572_);
v___x_3579_ = 0;
v___x_3580_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(v_declName_3569_, v_type_3570_, v_value_3571_, v___f_3578_, v_nondep_3573_, v___x_3579_, v___y_3559_, v___y_3556_, v___y_3564_, v___y_3562_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3591_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3585_ = l_Lean_Expr_mvarId_x21(v_a_3581_);
lean_dec(v_a_3581_);
v___x_3586_ = lean_box(0);
v___x_3587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3587_);
v___x_3589_ = v___x_3583_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
v_a_3592_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3580_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3580_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
else
{
lean_dec_ref(v_type_3570_);
lean_dec(v_declName_3569_);
lean_dec_ref(v___y_3553_);
v___y_3483_ = v___y_3562_;
v___y_3484_ = v___y_3556_;
v___y_3485_ = v_body_3572_;
v___y_3486_ = v___y_3554_;
v___y_3487_ = v___y_3559_;
v___y_3488_ = v___y_3557_;
v___y_3489_ = v_value_3571_;
v___y_3490_ = v___y_3564_;
goto v___jp_3482_;
}
}
else
{
lean_dec_ref(v_type_3570_);
lean_dec(v_declName_3569_);
lean_dec_ref(v___y_3553_);
v___y_3483_ = v___y_3562_;
v___y_3484_ = v___y_3556_;
v___y_3485_ = v_body_3572_;
v___y_3486_ = v___y_3554_;
v___y_3487_ = v___y_3559_;
v___y_3488_ = v___y_3557_;
v___y_3489_ = v_value_3571_;
v___y_3490_ = v___y_3564_;
goto v___jp_3482_;
}
}
else
{
uint8_t v___x_3600_; 
lean_dec_ref(v___y_3553_);
v___x_3600_ = l_Lean_Expr_isLambda(v___y_3566_);
if (v___x_3600_ == 0)
{
v___y_3327_ = v___y_3563_;
v___y_3328_ = v___y_3565_;
v___y_3329_ = v___y_3554_;
v___y_3330_ = v___y_3555_;
v___y_3331_ = v___y_3566_;
v___y_3332_ = v___y_3557_;
v___y_3333_ = v___y_3560_;
v___y_3334_ = v___y_3558_;
v___y_3335_ = v___y_3559_;
v___y_3336_ = v___y_3556_;
v___y_3337_ = v___y_3564_;
v___y_3338_ = v___y_3562_;
goto v___jp_3326_;
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___x_3601_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__17));
lean_inc_ref(v___y_3560_);
lean_inc_ref(v___y_3563_);
v___x_3602_ = l_Lean_Name_mkStr3(v___y_3563_, v___y_3560_, v___x_3601_);
lean_inc(v___y_3562_);
lean_inc_ref(v___y_3564_);
lean_inc(v___y_3556_);
lean_inc_ref(v___y_3559_);
lean_inc(v___x_3602_);
v___x_3603_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3156_, v___x_3602_, v___y_3559_, v___y_3556_, v___y_3564_, v___y_3562_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
if (lean_obj_tag(v_a_3604_) == 1)
{
lean_object* v_tail_3605_; 
v_tail_3605_ = lean_ctor_get(v_a_3604_, 1);
lean_inc(v_tail_3605_);
if (lean_obj_tag(v_tail_3605_) == 0)
{
lean_object* v_head_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v___x_3602_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v___y_3563_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3554_);
v_head_3606_ = lean_ctor_get(v_a_3604_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_a_3604_);
if (v_isSharedCheck_3632_ == 0)
{
lean_object* v_unused_3633_; 
v_unused_3633_ = lean_ctor_get(v_a_3604_, 1);
lean_dec(v_unused_3633_);
v___x_3608_ = v_a_3604_;
v_isShared_3609_ = v_isSharedCheck_3632_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_head_3606_);
lean_dec(v_a_3604_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3632_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = l_Lean_Expr_bindingName_x21(v___y_3566_);
lean_dec_ref(v___y_3566_);
v___x_3611_ = l_Lean_MVarId_intro(v_head_3606_, v___x_3610_, v___y_3559_, v___y_3556_, v___y_3564_, v___y_3562_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3623_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3623_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3623_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_snd_3616_; lean_object* v___x_3618_; 
v_snd_3616_ = lean_ctor_get(v_a_3612_, 1);
lean_inc(v_snd_3616_);
lean_dec(v_a_3612_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v_snd_3616_);
v___x_3618_ = v___x_3608_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_snd_3616_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_tail_3605_);
v___x_3618_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3620_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3618_);
v___x_3620_ = v___x_3614_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_del_object(v___x_3608_);
v_a_3624_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3611_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3611_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
else
{
lean_dec(v_tail_3605_);
lean_dec_ref(v_a_3604_);
v___y_3407_ = v___y_3563_;
v___y_3408_ = v___y_3555_;
v___y_3409_ = v___y_3554_;
v___y_3410_ = v___y_3565_;
v___y_3411_ = v___y_3566_;
v___y_3412_ = v___y_3557_;
v___y_3413_ = v___x_3602_;
v___y_3414_ = v___y_3558_;
v___y_3415_ = v___y_3560_;
v___y_3416_ = v___x_3568_;
v___y_3417_ = v___y_3559_;
v___y_3418_ = v___y_3556_;
v___y_3419_ = v___y_3564_;
v___y_3420_ = v___y_3562_;
goto v___jp_3406_;
}
}
else
{
lean_dec(v_a_3604_);
v___y_3407_ = v___y_3563_;
v___y_3408_ = v___y_3555_;
v___y_3409_ = v___y_3554_;
v___y_3410_ = v___y_3565_;
v___y_3411_ = v___y_3566_;
v___y_3412_ = v___y_3557_;
v___y_3413_ = v___x_3602_;
v___y_3414_ = v___y_3558_;
v___y_3415_ = v___y_3560_;
v___y_3416_ = v___x_3568_;
v___y_3417_ = v___y_3559_;
v___y_3418_ = v___y_3556_;
v___y_3419_ = v___y_3564_;
v___y_3420_ = v___y_3562_;
goto v___jp_3406_;
}
}
else
{
lean_dec(v___x_3602_);
lean_dec_ref(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v___x_3603_;
}
}
}
}
else
{
lean_dec_ref(v___y_3565_);
lean_dec_ref(v___y_3563_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3553_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
if (lean_obj_tag(v___y_3554_) == 6)
{
lean_object* v_binderName_3634_; lean_object* v_binderType_3635_; lean_object* v_body_3636_; uint8_t v_binderInfo_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; uint8_t v___x_3642_; 
v_binderName_3634_ = lean_ctor_get(v___y_3554_, 0);
lean_inc(v_binderName_3634_);
v_binderType_3635_ = lean_ctor_get(v___y_3554_, 1);
v_body_3636_ = lean_ctor_get(v___y_3554_, 2);
v_binderInfo_3637_ = lean_ctor_get_uint8(v___y_3554_, sizeof(void*)*3 + 8);
v___x_3638_ = l_Lean_Expr_bindingDomain_x21(v___y_3554_);
v___x_3639_ = l_Lean_Expr_mdataExpr_x21(v___y_3566_);
lean_dec_ref(v___y_3566_);
v___x_3640_ = lean_ptr_addr(v_binderType_3635_);
v___x_3641_ = lean_ptr_addr(v___x_3638_);
v___x_3642_ = lean_usize_dec_eq(v___x_3640_, v___x_3641_);
if (v___x_3642_ == 0)
{
v___y_3538_ = v___y_3556_;
v___y_3539_ = v___y_3562_;
v___y_3540_ = v___y_3554_;
v___y_3541_ = v___y_3559_;
v___y_3542_ = v_binderName_3634_;
v___y_3543_ = v___y_3557_;
v___y_3544_ = v___x_3638_;
v___y_3545_ = v_binderInfo_3637_;
v___y_3546_ = v___x_3639_;
v___y_3547_ = v___y_3564_;
v___y_3548_ = v___x_3642_;
goto v___jp_3537_;
}
else
{
size_t v___x_3643_; size_t v___x_3644_; uint8_t v___x_3645_; 
v___x_3643_ = lean_ptr_addr(v_body_3636_);
v___x_3644_ = lean_ptr_addr(v___x_3639_);
v___x_3645_ = lean_usize_dec_eq(v___x_3643_, v___x_3644_);
v___y_3538_ = v___y_3556_;
v___y_3539_ = v___y_3562_;
v___y_3540_ = v___y_3554_;
v___y_3541_ = v___y_3559_;
v___y_3542_ = v_binderName_3634_;
v___y_3543_ = v___y_3557_;
v___y_3544_ = v___x_3638_;
v___y_3545_ = v_binderInfo_3637_;
v___y_3546_ = v___x_3639_;
v___y_3547_ = v___y_3564_;
v___y_3548_ = v___x_3645_;
goto v___jp_3537_;
}
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_dec_ref(v___y_3566_);
lean_dec_ref(v___y_3554_);
v___x_3646_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1);
v___x_3647_ = l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(v___x_3646_);
v___y_3506_ = v___y_3562_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3559_;
v___y_3509_ = v___y_3557_;
v___y_3510_ = v___y_3564_;
v___y_3511_ = v___x_3647_;
goto v___jp_3505_;
}
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec_ref(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___x_3648_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__18));
v___x_3649_ = l_Lean_Name_mkStr3(v___y_3563_, v___y_3560_, v___x_3648_);
v___x_3650_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3156_, v___x_3649_, v___y_3559_, v___y_3556_, v___y_3564_, v___y_3562_);
return v___x_3650_;
}
}
v___jp_3651_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___f_3668_; uint8_t v___x_3669_; 
v___x_3666_ = l_Lean_Meta_Monotonicity_headBetaUnderLambda(v_f_3661_);
v___x_3667_ = l_Lean_Expr_bindingBody_x21(v___x_3666_);
lean_inc_ref(v___x_3667_);
v___f_3668_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3668_, 0, v___x_3667_);
v___x_3669_ = l_Lean_Expr_hasLooseBVars(v___x_3667_);
if (v___x_3669_ == 0)
{
v___y_3553_ = v___y_3653_;
v___y_3554_ = v___x_3666_;
v___y_3555_ = v___y_3655_;
v___y_3556_ = v___y_3663_;
v___y_3557_ = v___y_3657_;
v___y_3558_ = v___y_3658_;
v___y_3559_ = v___y_3662_;
v___y_3560_ = v___y_3659_;
v___y_3561_ = v___y_3652_;
v___y_3562_ = v___y_3665_;
v___y_3563_ = v___y_3654_;
v___y_3564_ = v___y_3664_;
v___y_3565_ = v___f_3668_;
v___y_3566_ = v___x_3667_;
v___y_3567_ = v___y_3656_;
goto v___jp_3552_;
}
else
{
v___y_3553_ = v___y_3653_;
v___y_3554_ = v___x_3666_;
v___y_3555_ = v___y_3655_;
v___y_3556_ = v___y_3663_;
v___y_3557_ = v___y_3657_;
v___y_3558_ = v___y_3658_;
v___y_3559_ = v___y_3662_;
v___y_3560_ = v___y_3659_;
v___y_3561_ = v___y_3652_;
v___y_3562_ = v___y_3665_;
v___y_3563_ = v___y_3654_;
v___y_3564_ = v___y_3664_;
v___y_3565_ = v___f_3668_;
v___y_3566_ = v___x_3667_;
v___y_3567_ = v___y_3660_;
goto v___jp_3552_;
}
}
v___jp_3670_:
{
lean_object* v___x_3675_; 
lean_inc(v_goal_3156_);
v___x_3675_ = l_Lean_MVarId_getType(v_goal_3156_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; uint8_t v___x_3677_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3676_);
lean_dec_ref(v___x_3675_);
v___x_3677_ = l_Lean_Expr_isForall(v_a_3676_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; 
lean_inc(v_a_3676_);
v___x_3678_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3676_, v___y_3672_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = l_Lean_Expr_cleanupAnnotations(v_a_3679_);
v___x_3681_ = l_Lean_Expr_isApp(v___x_3680_);
if (v___x_3681_ == 0)
{
lean_dec_ref(v___x_3680_);
lean_dec(v_a_3676_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___y_3164_ = v___y_3671_;
v___y_3165_ = v___y_3672_;
v___y_3166_ = v___y_3673_;
v___y_3167_ = v___y_3674_;
goto v___jp_3163_;
}
else
{
lean_object* v_arg_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_arg_3682_ = lean_ctor_get(v___x_3680_, 1);
lean_inc_ref(v_arg_3682_);
v___x_3683_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3680_);
v___x_3684_ = l_Lean_Expr_isApp(v___x_3683_);
if (v___x_3684_ == 0)
{
lean_dec_ref(v___x_3683_);
lean_dec_ref(v_arg_3682_);
lean_dec(v_a_3676_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___y_3164_ = v___y_3671_;
v___y_3165_ = v___y_3672_;
v___y_3166_ = v___y_3673_;
v___y_3167_ = v___y_3674_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3683_);
v___x_3686_ = l_Lean_Expr_isApp(v___x_3685_);
if (v___x_3686_ == 0)
{
lean_dec_ref(v___x_3685_);
lean_dec_ref(v_arg_3682_);
lean_dec(v_a_3676_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___y_3164_ = v___y_3671_;
v___y_3165_ = v___y_3672_;
v___y_3166_ = v___y_3673_;
v___y_3167_ = v___y_3674_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3687_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3685_);
v___x_3688_ = l_Lean_Expr_isApp(v___x_3687_);
if (v___x_3688_ == 0)
{
lean_dec_ref(v___x_3687_);
lean_dec_ref(v_arg_3682_);
lean_dec(v_a_3676_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___y_3164_ = v___y_3671_;
v___y_3165_ = v___y_3672_;
v___y_3166_ = v___y_3673_;
v___y_3167_ = v___y_3674_;
goto v___jp_3163_;
}
else
{
lean_object* v_arg_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v_arg_3689_ = lean_ctor_get(v___x_3687_, 1);
lean_inc_ref(v_arg_3689_);
v___x_3690_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3687_);
v___x_3691_ = l_Lean_Expr_isApp(v___x_3690_);
if (v___x_3691_ == 0)
{
lean_dec_ref(v___x_3690_);
lean_dec_ref(v_arg_3689_);
lean_dec_ref(v_arg_3682_);
lean_dec(v_a_3676_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___y_3164_ = v___y_3671_;
v___y_3165_ = v___y_3672_;
v___y_3166_ = v___y_3673_;
v___y_3167_ = v___y_3674_;
goto v___jp_3163_;
}
else
{
lean_object* v_arg_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; 
v_arg_3692_ = lean_ctor_get(v___x_3690_, 1);
lean_inc_ref(v_arg_3692_);
v___x_3693_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3690_);
v___x_3694_ = ((lean_object*)(l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_));
v___x_3695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_3696_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__9));
v___x_3697_ = l_Lean_Expr_isConstOf(v___x_3693_, v___x_3696_);
lean_dec_ref(v___x_3693_);
if (v___x_3697_ == 0)
{
lean_dec_ref(v_arg_3692_);
lean_dec_ref(v_arg_3689_);
lean_dec_ref(v_arg_3682_);
lean_dec(v_a_3676_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___y_3164_ = v___y_3671_;
v___y_3165_ = v___y_3672_;
v___y_3166_ = v___y_3673_;
v___y_3167_ = v___y_3674_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3698_; lean_object* v_a_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3698_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(v_arg_3682_, v___y_3672_);
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref(v___x_3698_);
v___x_3700_ = l_Lean_Expr_headBeta(v_a_3699_);
v___x_3701_ = l_Lean_Expr_isLambda(v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; 
lean_inc(v___y_3674_);
lean_inc_ref(v___y_3673_);
lean_inc(v___y_3672_);
lean_inc_ref(v___y_3671_);
v___x_3702_ = l_Lean_Meta_etaExpand(v___x_3700_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref(v___x_3702_);
lean_inc(v_a_3676_);
v___y_3652_ = v___x_3697_;
v___y_3653_ = v_a_3676_;
v___y_3654_ = v___x_3694_;
v___y_3655_ = v_arg_3689_;
v___y_3656_ = v___x_3697_;
v___y_3657_ = v_a_3676_;
v___y_3658_ = v_arg_3692_;
v___y_3659_ = v___x_3695_;
v___y_3660_ = v___x_3677_;
v_f_3661_ = v_a_3703_;
v___y_3662_ = v___y_3671_;
v___y_3663_ = v___y_3672_;
v___y_3664_ = v___y_3673_;
v___y_3665_ = v___y_3674_;
goto v___jp_3651_;
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_arg_3692_);
lean_dec_ref(v_arg_3689_);
lean_dec(v_a_3676_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3704_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3702_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3702_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_inc(v_a_3676_);
v___y_3652_ = v___x_3697_;
v___y_3653_ = v_a_3676_;
v___y_3654_ = v___x_3694_;
v___y_3655_ = v_arg_3689_;
v___y_3656_ = v___x_3697_;
v___y_3657_ = v_a_3676_;
v___y_3658_ = v_arg_3692_;
v___y_3659_ = v___x_3695_;
v___y_3660_ = v___x_3677_;
v_f_3661_ = v___x_3700_;
v___y_3662_ = v___y_3671_;
v___y_3663_ = v___y_3672_;
v___y_3664_ = v___y_3673_;
v___y_3665_ = v___y_3674_;
goto v___jp_3651_;
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
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_a_3676_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3712_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3678_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3678_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v___x_3720_; 
lean_dec(v_a_3676_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_cls_3155_);
v___x_3720_ = l_Lean_Meta_intro1Core(v_goal_3156_, v___x_3677_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3738_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3738_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3738_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_snd_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3736_; 
v_snd_3725_ = lean_ctor_get(v_a_3721_, 1);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_a_3721_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; 
v_unused_3737_ = lean_ctor_get(v_a_3721_, 0);
lean_dec(v_unused_3737_);
v___x_3727_ = v_a_3721_;
v_isShared_3728_ = v_isSharedCheck_3736_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_snd_3725_);
lean_dec(v_a_3721_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3736_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_box(0);
if (v_isShared_3728_ == 0)
{
lean_ctor_set_tag(v___x_3727_, 1);
lean_ctor_set(v___x_3727_, 1, v___x_3729_);
lean_ctor_set(v___x_3727_, 0, v_snd_3725_);
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_snd_3725_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3731_);
v___x_3733_ = v___x_3723_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_a_3739_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3720_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3720_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3747_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3675_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3675_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
v_resetjp_3757_:
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_unbox(v_a_3756_);
lean_dec(v_a_3756_);
if (v___x_3760_ == 0)
{
lean_del_object(v___x_3758_);
v___y_3671_ = v___y_3158_;
v___y_3672_ = v___y_3159_;
v___y_3673_ = v___y_3160_;
v___y_3674_ = v___y_3161_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3761_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20);
lean_inc(v_goal_3156_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 1);
lean_ctor_set(v___x_3758_, 0, v_goal_3156_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_goal_3156_);
v___x_3763_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3761_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
lean_inc(v_cls_3155_);
v___x_3765_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3155_, v___x_3764_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_dec_ref(v___x_3765_);
v___y_3671_ = v___y_3158_;
v___y_3672_ = v___y_3159_;
v___y_3673_ = v___y_3160_;
v___y_3674_ = v___y_3161_;
goto v___jp_3670_;
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v_failK_3157_);
lean_dec(v_goal_3156_);
lean_dec(v_cls_3155_);
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3765_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___boxed(lean_object* v_cls_3776_, lean_object* v_goal_3777_, lean_object* v_failK_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Meta_Monotonicity_solveMonoStep___lam__2(v_cls_3776_, v_goal_3777_, v_failK_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep(lean_object* v_failK_3785_, lean_object* v_goal_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v_cls_3792_; lean_object* v___f_3793_; lean_object* v___x_3794_; 
v_cls_3792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2));
lean_inc(v_goal_3786_);
v___f_3793_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___boxed), 8, 3);
lean_closure_set(v___f_3793_, 0, v_cls_3792_);
lean_closure_set(v___f_3793_, 1, v_goal_3786_);
lean_closure_set(v___f_3793_, 2, v_failK_3785_);
v___x_3794_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(v_goal_3786_, v___f_3793_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___boxed(lean_object* v_failK_3795_, lean_object* v_goal_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Meta_Monotonicity_solveMonoStep(v_failK_3795_, v_goal_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1(lean_object* v_mvarId_3803_, lean_object* v_val_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_mvarId_3803_, v_val_3804_, v___y_3806_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___boxed(lean_object* v_mvarId_3811_, lean_object* v_val_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1(v_mvarId_3811_, v_val_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5(lean_object* v_00_u03b1_3819_, lean_object* v_name_3820_, uint8_t v_bi_3821_, lean_object* v_type_3822_, lean_object* v_k_3823_, uint8_t v_kind_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(v_name_3820_, v_bi_3821_, v_type_3822_, v_k_3823_, v_kind_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_name_3832_, lean_object* v_bi_3833_, lean_object* v_type_3834_, lean_object* v_k_3835_, lean_object* v_kind_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
uint8_t v_bi_boxed_3842_; uint8_t v_kind_boxed_3843_; lean_object* v_res_3844_; 
v_bi_boxed_3842_ = lean_unbox(v_bi_3833_);
v_kind_boxed_3843_ = lean_unbox(v_kind_3836_);
v_res_3844_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5(v_00_u03b1_3831_, v_name_3832_, v_bi_boxed_3842_, v_type_3834_, v_k_3835_, v_kind_boxed_3843_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4(lean_object* v_00_u03b1_3845_, lean_object* v_name_3846_, lean_object* v_type_3847_, lean_object* v_k_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(v_name_3846_, v_type_3847_, v_k_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___boxed(lean_object* v_00_u03b1_3855_, lean_object* v_name_3856_, lean_object* v_type_3857_, lean_object* v_k_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4(v_00_u03b1_3855_, v_name_3856_, v_type_3857_, v_k_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6(lean_object* v_upperBound_3865_, lean_object* v___x_3866_, uint8_t v___x_3867_, lean_object* v_inst_3868_, lean_object* v_R_3869_, lean_object* v_a_3870_, lean_object* v_b_3871_, lean_object* v_c_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(v_upperBound_3865_, v___x_3866_, v___x_3867_, v_a_3870_, v_b_3871_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___boxed(lean_object* v_upperBound_3879_, lean_object* v___x_3880_, lean_object* v___x_3881_, lean_object* v_inst_3882_, lean_object* v_R_3883_, lean_object* v_a_3884_, lean_object* v_b_3885_, lean_object* v_c_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
uint8_t v___x_44016__boxed_3892_; lean_object* v_res_3893_; 
v___x_44016__boxed_3892_ = lean_unbox(v___x_3881_);
v_res_3893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6(v_upperBound_3879_, v___x_3880_, v___x_44016__boxed_3892_, v_inst_3882_, v_R_3883_, v_a_3884_, v_b_3885_, v_c_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v___x_3880_);
lean_dec(v_upperBound_3879_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1(lean_object* v_00_u03b2_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_, lean_object* v_x_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1___redArg(v_x_3895_, v_x_3896_, v_x_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3899_, lean_object* v_x_3900_, size_t v_x_3901_, size_t v_x_3902_, lean_object* v_x_3903_, lean_object* v_x_3904_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_x_3900_, v_x_3901_, v_x_3902_, v_x_3903_, v_x_3904_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3906_, lean_object* v_x_3907_, lean_object* v_x_3908_, lean_object* v_x_3909_, lean_object* v_x_3910_, lean_object* v_x_3911_){
_start:
{
size_t v_x_44052__boxed_3912_; size_t v_x_44053__boxed_3913_; lean_object* v_res_3914_; 
v_x_44052__boxed_3912_ = lean_unbox_usize(v_x_3908_);
lean_dec(v_x_3908_);
v_x_44053__boxed_3913_ = lean_unbox_usize(v_x_3909_);
lean_dec(v_x_3909_);
v_res_3914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5(v_00_u03b2_3906_, v_x_3907_, v_x_44052__boxed_3912_, v_x_44053__boxed_3913_, v_x_3910_, v_x_3911_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13(lean_object* v_00_u03b2_3915_, lean_object* v_n_3916_, lean_object* v_k_3917_, lean_object* v_v_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13___redArg(v_n_3916_, v_k_3917_, v_v_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14(lean_object* v_00_u03b2_3920_, size_t v_depth_3921_, lean_object* v_keys_3922_, lean_object* v_vals_3923_, lean_object* v_heq_3924_, lean_object* v_i_3925_, lean_object* v_entries_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(v_depth_3921_, v_keys_3922_, v_vals_3923_, v_i_3925_, v_entries_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___boxed(lean_object* v_00_u03b2_3928_, lean_object* v_depth_3929_, lean_object* v_keys_3930_, lean_object* v_vals_3931_, lean_object* v_heq_3932_, lean_object* v_i_3933_, lean_object* v_entries_3934_){
_start:
{
size_t v_depth_boxed_3935_; lean_object* v_res_3936_; 
v_depth_boxed_3935_ = lean_unbox_usize(v_depth_3929_);
lean_dec(v_depth_3929_);
v_res_3936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14(v_00_u03b2_3928_, v_depth_boxed_3935_, v_keys_3930_, v_vals_3931_, v_heq_3932_, v_i_3933_, v_entries_3934_);
lean_dec_ref(v_vals_3931_);
lean_dec_ref(v_keys_3930_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14(lean_object* v_00_u03b2_3937_, lean_object* v_x_3938_, lean_object* v_x_3939_, lean_object* v_x_3940_, lean_object* v_x_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14___redArg(v_x_3938_, v_x_3939_, v_x_3940_, v_x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0(lean_object* v_failK_3943_, lean_object* v_as_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
if (lean_obj_tag(v_as_3944_) == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec_ref(v_failK_3943_);
v___x_3950_ = lean_box(0);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
return v___x_3951_;
}
else
{
lean_object* v_head_3952_; lean_object* v_tail_3953_; lean_object* v___x_3954_; 
v_head_3952_ = lean_ctor_get(v_as_3944_, 0);
lean_inc(v_head_3952_);
v_tail_3953_ = lean_ctor_get(v_as_3944_, 1);
lean_inc(v_tail_3953_);
lean_dec_ref(v_as_3944_);
lean_inc(v___y_3948_);
lean_inc_ref(v___y_3947_);
lean_inc(v___y_3946_);
lean_inc_ref(v___y_3945_);
lean_inc_ref(v_failK_3943_);
v___x_3954_ = l_Lean_Meta_Monotonicity_solveMono(v_failK_3943_, v_head_3952_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_dec_ref(v___x_3954_);
v_as_3944_ = v_tail_3953_;
goto _start;
}
else
{
lean_dec(v_tail_3953_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec_ref(v_failK_3943_);
return v___x_3954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMono(lean_object* v_failK_3956_, lean_object* v_goal_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v___x_3963_; 
lean_inc(v_a_3961_);
lean_inc_ref(v_a_3960_);
lean_inc(v_a_3959_);
lean_inc_ref(v_a_3958_);
lean_inc_ref(v_failK_3956_);
v___x_3963_ = l_Lean_Meta_Monotonicity_solveMonoStep(v_failK_3956_, v_goal_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref(v___x_3963_);
v___x_3965_ = l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0(v_failK_3956_, v_a_3964_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
return v___x_3965_;
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_failK_3956_);
v_a_3966_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3963_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3963_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMono___boxed(lean_object* v_failK_3974_, lean_object* v_goal_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Meta_Monotonicity_solveMono(v_failK_3974_, v_goal_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0___boxed(lean_object* v_failK_3982_, lean_object* v_as_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0(v_failK_3982_, v_as_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0(lean_object* v___x_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3992_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4002_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
lean_inc(v___y_3998_);
lean_inc_ref(v___y_3997_);
lean_inc(v___y_3996_);
lean_inc_ref(v___y_3995_);
v___x_4002_ = l_Lean_Meta_Monotonicity_solveMonoStep(v___x_3990_, v_a_4001_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4004_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref(v___x_4002_);
v___x_4004_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_4003_, v___y_3992_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4012_; 
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; 
v_unused_4013_ = lean_ctor_get(v___x_4004_, 0);
lean_dec(v_unused_4013_);
v___x_4006_ = v___x_4004_;
v_isShared_4007_ = v_isSharedCheck_4012_;
goto v_resetjp_4005_;
}
else
{
lean_dec(v___x_4004_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4012_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4010_; 
v___x_4008_ = lean_box(0);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 0, v___x_4008_);
v___x_4010_ = v___x_4006_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
else
{
return v___x_4004_;
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
v_a_4014_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_4002_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4002_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v___x_3990_);
v_a_4022_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4000_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4000_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0___boxed(lean_object* v___x_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0(v___x_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg(lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v___f_4053_; lean_object* v___x_4054_; 
v___f_4053_ = ((lean_object*)(l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__1));
v___x_4054_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4053_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___boxed(lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_Meta_Monotonicity_evalMonotonicity___redArg(v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity(lean_object* v___stx_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Meta_Monotonicity_evalMonotonicity___redArg(v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___boxed(lean_object* v___stx_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Meta_Monotonicity_evalMonotonicity(v___stx_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
lean_dec(v___stx_4076_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1(){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4098_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4099_ = ((lean_object*)(l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0));
v___x_4100_ = ((lean_object*)(l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2));
v___x_4101_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_evalMonotonicity___boxed), 10, 0);
v___x_4102_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4098_, v___x_4099_, v___x_4100_, v___x_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___boxed(lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1();
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2));
v___x_4137_ = 0;
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_));
v___x_4139_ = l_Lean_registerTraceClass(v___x_4136_, v___x_4137_, v___x_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2____boxed(lean_object* v_a_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_();
return v_res_4141_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_RecAppSyntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Monotonicity(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Monotonicity_monotoneExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Monotonicity_monotoneExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Monotonicity(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Init_Internal_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Monotonicity(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Monotonicity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Monotonicity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Monotonicity(builtin);
}
#ifdef __cplusplus
}
#endif
