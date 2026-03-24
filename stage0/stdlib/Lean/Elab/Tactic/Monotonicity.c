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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_;
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
lean_inc_ref(v___y_701_);
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
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v_k_718_, lean_object* v_b_719_, lean_object* v_c_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
v___x_726_ = lean_apply_7(v_k_718_, v_b_719_, v_c_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, lean_box(0));
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v_k_727_, lean_object* v_b_728_, lean_object* v_c_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_727_, v_b_728_, v_c_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
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
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
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
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
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
lean_object* v___x_885_; uint8_t v_foApprox_886_; uint8_t v_ctxApprox_887_; uint8_t v_quasiPatternApprox_888_; uint8_t v_constApprox_889_; uint8_t v_isDefEqStuckEx_890_; uint8_t v_unificationHints_891_; uint8_t v_proofIrrelevance_892_; uint8_t v_assignSyntheticOpaque_893_; uint8_t v_offsetCnstrs_894_; uint8_t v_etaStruct_895_; uint8_t v_univApprox_896_; uint8_t v_iota_897_; uint8_t v_beta_898_; uint8_t v_proj_899_; uint8_t v_zeta_900_; uint8_t v_zetaDelta_901_; uint8_t v_zetaUnused_902_; uint8_t v_zetaHave_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_943_; 
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
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_943_ == 0)
{
v___x_905_ = v___x_885_;
v_isShared_906_ = v_isSharedCheck_943_;
goto v_resetjp_904_;
}
else
{
lean_dec(v___x_885_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_943_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
uint8_t v_trackZetaDelta_907_; lean_object* v_zetaDeltaSet_908_; lean_object* v_lctx_909_; lean_object* v_localInstances_910_; lean_object* v_defEqCtx_x3f_911_; lean_object* v_synthPendingDepth_912_; lean_object* v_canUnfold_x3f_913_; uint8_t v_univApprox_914_; uint8_t v_inTypeClassResolution_915_; uint8_t v_cacheInferType_916_; uint8_t v___x_917_; lean_object* v_config_919_; 
v_trackZetaDelta_907_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*7);
v_zetaDeltaSet_908_ = lean_ctor_get(v___y_880_, 1);
v_lctx_909_ = lean_ctor_get(v___y_880_, 2);
v_localInstances_910_ = lean_ctor_get(v___y_880_, 3);
v_defEqCtx_x3f_911_ = lean_ctor_get(v___y_880_, 4);
v_synthPendingDepth_912_ = lean_ctor_get(v___y_880_, 5);
v_canUnfold_x3f_913_ = lean_ctor_get(v___y_880_, 6);
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
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 0, v_foApprox_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 1, v_ctxApprox_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 2, v_quasiPatternApprox_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 3, v_constApprox_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 4, v_isDefEqStuckEx_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 5, v_unificationHints_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 6, v_proofIrrelevance_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 7, v_assignSyntheticOpaque_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 8, v_offsetCnstrs_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 10, v_etaStruct_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 11, v_univApprox_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 12, v_iota_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 13, v_beta_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 14, v_proj_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 15, v_zeta_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 16, v_zetaDelta_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 17, v_zetaUnused_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 18, v_zetaHave_903_);
v_config_919_ = v_reuseFailAlloc_942_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
uint64_t v___x_920_; uint64_t v___x_921_; uint64_t v___x_922_; uint8_t v___x_923_; uint64_t v___x_924_; uint64_t v___x_925_; uint64_t v_key_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_ctor_set_uint8(v_config_919_, 9, v___x_917_);
v___x_920_ = l_Lean_Meta_Context_configKey(v___y_880_);
v___x_921_ = 2ULL;
v___x_922_ = lean_uint64_shift_right(v___x_920_, v___x_921_);
v___x_923_ = 0;
v___x_924_ = lean_uint64_shift_left(v___x_922_, v___x_921_);
v___x_925_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v_key_926_ = lean_uint64_lor(v___x_924_, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_927_, 0, v_config_919_);
lean_ctor_set_uint64(v___x_927_, sizeof(void*)*1, v_key_926_);
lean_inc(v_canUnfold_x3f_913_);
lean_inc(v_synthPendingDepth_912_);
lean_inc(v_defEqCtx_x3f_911_);
lean_inc_ref(v_localInstances_910_);
lean_inc_ref(v_lctx_909_);
lean_inc(v_zetaDeltaSet_908_);
v___x_928_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_zetaDeltaSet_908_);
lean_ctor_set(v___x_928_, 2, v_lctx_909_);
lean_ctor_set(v___x_928_, 3, v_localInstances_910_);
lean_ctor_set(v___x_928_, 4, v_defEqCtx_x3f_911_);
lean_ctor_set(v___x_928_, 5, v_synthPendingDepth_912_);
lean_ctor_set(v___x_928_, 6, v_canUnfold_x3f_913_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*7, v_trackZetaDelta_907_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*7 + 1, v_univApprox_914_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*7 + 2, v_inTypeClassResolution_915_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*7 + 3, v_cacheInferType_916_);
v___x_929_ = l_Lean_Meta_DiscrTree_mkPath(v_e_879_, v___x_923_, v___x_928_, v___y_881_, v___y_882_, v___y_883_);
lean_dec_ref(v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref(v___x_929_);
v___x_931_ = l_Lean_Meta_Monotonicity_monotoneExt;
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_decl_876_);
lean_ctor_set(v___x_932_, 1, v_a_930_);
lean_inc_ref(v___y_882_);
v___x_933_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__1___redArg(v___x_931_, v___x_932_, v_kind_877_, v___y_881_, v___y_882_, v___y_883_);
return v___x_933_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_decl_876_);
v_a_934_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_929_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_929_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v_decl_944_, lean_object* v_kind_945_, lean_object* v_x_946_, lean_object* v_e_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
uint8_t v_kind_boxed_953_; lean_object* v_res_954_; 
v_kind_boxed_953_ = lean_unbox(v_kind_945_);
v_res_954_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v_decl_944_, v_kind_boxed_953_, v_x_946_, v_e_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v_x_946_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v___f_955_, lean_object* v_f_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; 
v___x_962_ = l_Lean_Meta_Monotonicity_headBetaUnderLambda(v_f_956_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = 0;
v___x_965_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__2___redArg(v___x_962_, v___x_963_, v___f_955_, v___x_964_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v___f_966_, lean_object* v_f_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___f_966_, v_f_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_974_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
lean_ctor_set(v___x_979_, 3, v___x_977_);
lean_ctor_set(v___x_979_, 4, v___x_977_);
lean_ctor_set(v___x_979_, 5, v___x_977_);
lean_ctor_set(v___x_979_, 6, v___x_977_);
lean_ctor_set(v___x_979_, 7, v___x_977_);
lean_ctor_set(v___x_979_, 8, v___x_977_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_unsigned_to_nat(32u);
v___x_981_ = lean_mk_empty_array_with_capacity(v___x_980_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_983_ = ((size_t)5ULL);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_unsigned_to_nat(32u);
v___x_986_ = lean_mk_empty_array_with_capacity(v___x_985_);
v___x_987_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_988_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_986_);
lean_ctor_set(v___x_988_, 2, v___x_984_);
lean_ctor_set(v___x_988_, 3, v___x_984_);
lean_ctor_set_usize(v___x_988_, 4, v___x_983_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_989_ = lean_box(1);
v___x_990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_990_);
lean_ctor_set(v___x_992_, 2, v___x_989_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1004_ = l_Lean_stringToMessageData(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1014_, lean_object* v_declHint_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; lean_object* v_env_1019_; uint8_t v___x_1020_; 
v___x_1018_ = lean_st_ref_get(v___y_1016_);
v_env_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc_ref(v_env_1019_);
lean_dec(v___x_1018_);
v___x_1020_ = l_Lean_Name_isAnonymous(v_declHint_1015_);
if (v___x_1020_ == 0)
{
uint8_t v_isExporting_1021_; 
v_isExporting_1021_ = lean_ctor_get_uint8(v_env_1019_, sizeof(void*)*8);
if (v_isExporting_1021_ == 0)
{
lean_object* v___x_1022_; 
lean_dec_ref(v_env_1019_);
lean_dec(v_declHint_1015_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_msg_1014_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
lean_inc_ref(v_env_1019_);
v___x_1023_ = l_Lean_Environment_setExporting(v_env_1019_, v___x_1020_);
lean_inc(v_declHint_1015_);
lean_inc_ref(v___x_1023_);
v___x_1024_ = l_Lean_Environment_contains(v___x_1023_, v_declHint_1015_, v_isExporting_1021_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref(v___x_1023_);
lean_dec_ref(v_env_1019_);
lean_dec(v_declHint_1015_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_msg_1014_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_c_1031_; lean_object* v___x_1032_; 
v___x_1026_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1028_ = l_Lean_Options_empty;
v___x_1029_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1023_);
lean_ctor_set(v___x_1029_, 1, v___x_1026_);
lean_ctor_set(v___x_1029_, 2, v___x_1027_);
lean_ctor_set(v___x_1029_, 3, v___x_1028_);
lean_inc(v_declHint_1015_);
v___x_1030_ = l_Lean_MessageData_ofConstName(v_declHint_1015_, v___x_1020_);
v_c_1031_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1031_, 0, v___x_1029_);
lean_ctor_set(v_c_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1019_, v_declHint_1015_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec_ref(v_env_1019_);
lean_dec(v_declHint_1015_);
v___x_1033_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v_c_1031_);
v___x_1035_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_MessageData_note(v___x_1036_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_msg_1014_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1075_; 
v_val_1040_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1042_ = v___x_1032_;
v_isShared_1043_ = v_isSharedCheck_1075_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v___x_1032_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1075_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_mod_1047_; uint8_t v___x_1048_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Lean_Environment_header(v_env_1019_);
lean_dec_ref(v_env_1019_);
v___x_1046_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1045_);
v_mod_1047_ = lean_array_get(v___x_1044_, v___x_1046_, v_val_1040_);
lean_dec(v_val_1040_);
lean_dec_ref(v___x_1046_);
v___x_1048_ = l_Lean_isPrivateName(v_declHint_1015_);
lean_dec(v_declHint_1015_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_c_1031_);
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_MessageData_ofName(v_mod_1047_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_MessageData_note(v___x_1056_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_msg_1014_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1058_);
v___x_1060_ = v___x_1042_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_c_1031_);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_ofName(v_mod_1047_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_MessageData_note(v___x_1069_);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_msg_1014_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1071_);
v___x_1073_ = v___x_1042_;
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
}
}
}
}
}
else
{
lean_object* v___x_1076_; 
lean_dec_ref(v_env_1019_);
lean_dec(v_declHint_1015_);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_msg_1014_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1077_, lean_object* v_declHint_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1077_, v_declHint_1078_, v___y_1079_);
lean_dec(v___y_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_1082_, lean_object* v_declHint_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
v___x_1089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1082_, v_declHint_1083_, v___y_1087_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1094_ = l_Lean_unknownIdentifierMessageTag;
v___x_1095_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_a_1090_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_1100_, lean_object* v_declHint_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9(v_msg_1100_, v_declHint_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_fileName_1115_; lean_object* v_fileMap_1116_; lean_object* v_options_1117_; lean_object* v_currRecDepth_1118_; lean_object* v_maxRecDepth_1119_; lean_object* v_ref_1120_; lean_object* v_currNamespace_1121_; lean_object* v_openDecls_1122_; lean_object* v_initHeartbeats_1123_; lean_object* v_maxHeartbeats_1124_; lean_object* v_quotContext_1125_; lean_object* v_currMacroScope_1126_; uint8_t v_diag_1127_; lean_object* v_cancelTk_x3f_1128_; uint8_t v_suppressElabErrors_1129_; lean_object* v_inheritedTraceOptions_1130_; lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_fileName_1115_ = lean_ctor_get(v___y_1112_, 0);
v_fileMap_1116_ = lean_ctor_get(v___y_1112_, 1);
v_options_1117_ = lean_ctor_get(v___y_1112_, 2);
v_currRecDepth_1118_ = lean_ctor_get(v___y_1112_, 3);
v_maxRecDepth_1119_ = lean_ctor_get(v___y_1112_, 4);
v_ref_1120_ = lean_ctor_get(v___y_1112_, 5);
v_currNamespace_1121_ = lean_ctor_get(v___y_1112_, 6);
v_openDecls_1122_ = lean_ctor_get(v___y_1112_, 7);
v_initHeartbeats_1123_ = lean_ctor_get(v___y_1112_, 8);
v_maxHeartbeats_1124_ = lean_ctor_get(v___y_1112_, 9);
v_quotContext_1125_ = lean_ctor_get(v___y_1112_, 10);
v_currMacroScope_1126_ = lean_ctor_get(v___y_1112_, 11);
v_diag_1127_ = lean_ctor_get_uint8(v___y_1112_, sizeof(void*)*14);
v_cancelTk_x3f_1128_ = lean_ctor_get(v___y_1112_, 12);
v_suppressElabErrors_1129_ = lean_ctor_get_uint8(v___y_1112_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1130_ = lean_ctor_get(v___y_1112_, 13);
v_ref_1131_ = l_Lean_replaceRef(v_ref_1108_, v_ref_1120_);
lean_inc_ref(v_inheritedTraceOptions_1130_);
lean_inc(v_cancelTk_x3f_1128_);
lean_inc(v_currMacroScope_1126_);
lean_inc(v_quotContext_1125_);
lean_inc(v_maxHeartbeats_1124_);
lean_inc(v_initHeartbeats_1123_);
lean_inc(v_openDecls_1122_);
lean_inc(v_currNamespace_1121_);
lean_inc(v_maxRecDepth_1119_);
lean_inc(v_currRecDepth_1118_);
lean_inc_ref(v_options_1117_);
lean_inc_ref(v_fileMap_1116_);
lean_inc_ref(v_fileName_1115_);
v___x_1132_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1132_, 0, v_fileName_1115_);
lean_ctor_set(v___x_1132_, 1, v_fileMap_1116_);
lean_ctor_set(v___x_1132_, 2, v_options_1117_);
lean_ctor_set(v___x_1132_, 3, v_currRecDepth_1118_);
lean_ctor_set(v___x_1132_, 4, v_maxRecDepth_1119_);
lean_ctor_set(v___x_1132_, 5, v_ref_1131_);
lean_ctor_set(v___x_1132_, 6, v_currNamespace_1121_);
lean_ctor_set(v___x_1132_, 7, v_openDecls_1122_);
lean_ctor_set(v___x_1132_, 8, v_initHeartbeats_1123_);
lean_ctor_set(v___x_1132_, 9, v_maxHeartbeats_1124_);
lean_ctor_set(v___x_1132_, 10, v_quotContext_1125_);
lean_ctor_set(v___x_1132_, 11, v_currMacroScope_1126_);
lean_ctor_set(v___x_1132_, 12, v_cancelTk_x3f_1128_);
lean_ctor_set(v___x_1132_, 13, v_inheritedTraceOptions_1130_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*14, v_diag_1127_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*14 + 1, v_suppressElabErrors_1129_);
v___x_1133_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v_msg_1109_, v___y_1110_, v___y_1111_, v___x_1132_, v___y_1113_);
lean_dec_ref(v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1134_, lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1134_, v_msg_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v_ref_1134_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_1142_, lean_object* v_msg_1143_, lean_object* v_declHint_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1152_; 
v___x_1150_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9(v_msg_1143_, v_declHint_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1142_, v_a_1151_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_1153_, lean_object* v_msg_1154_, lean_object* v_declHint_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(v_ref_1153_, v_msg_1154_, v_declHint_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v_ref_1153_);
return v_res_1161_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object* v_ref_1168_, lean_object* v_constName_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1175_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1176_ = 0;
lean_inc(v_constName_1169_);
v___x_1177_ = l_Lean_MessageData_ofConstName(v_constName_1169_, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1175_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(v_ref_1168_, v___x_1180_, v_constName_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_1182_, lean_object* v_constName_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ref_1182_, v_constName_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v_ref_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_constName_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_ref_1196_; lean_object* v___x_1197_; 
v_ref_1196_ = lean_ctor_get(v___y_1193_, 5);
v___x_1197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ref_1196_, v_constName_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_constName_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(v_constName_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3(lean_object* v_constName_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_env_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = lean_st_ref_get(v___y_1209_);
v_env_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_ref(v_env_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = 0;
lean_inc(v_constName_1205_);
v___x_1214_ = l_Lean_Environment_find_x3f(v_env_1212_, v_constName_1205_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(v_constName_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1215_;
}
else
{
lean_object* v_val_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_constName_1205_);
v_val_1216_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1214_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_val_1216_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 0);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_val_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3___boxed(lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3(v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1237_; uint64_t v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1237_);
return v___x_1238_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1240_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1241_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set_uint64(v___x_1241_, sizeof(void*)*1, v___x_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1246_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
lean_ctor_set(v___x_1246_, 2, v___x_1245_);
lean_ctor_set(v___x_1246_, 3, v___x_1245_);
lean_ctor_set(v___x_1246_, 4, v___x_1245_);
lean_ctor_set(v___x_1246_, 5, v___x_1245_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
lean_ctor_set(v___x_1248_, 3, v___x_1247_);
lean_ctor_set(v___x_1248_, 4, v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v___x_1249_, lean_object* v___x_1250_, lean_object* v___f_1251_, lean_object* v___x_1252_, lean_object* v_decl_1253_, lean_object* v_x_1254_, uint8_t v_kind_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___y_1279_; lean_object* v___x_1289_; 
v___x_1259_ = 0;
v___x_1260_ = 1;
v___x_1261_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1262_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1263_ = lean_unsigned_to_nat(32u);
v___x_1264_ = lean_mk_empty_array_with_capacity(v___x_1263_);
v___x_1265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1266_ = ((size_t)5ULL);
lean_inc_n(v___x_1249_, 2);
v___x_1267_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1264_);
lean_ctor_set(v___x_1267_, 2, v___x_1249_);
lean_ctor_set(v___x_1267_, 3, v___x_1249_);
lean_ctor_set_usize(v___x_1267_, 4, v___x_1266_);
v___x_1268_ = lean_box(1);
lean_inc_ref(v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1262_);
lean_ctor_set(v___x_1269_, 1, v___x_1267_);
lean_ctor_set(v___x_1269_, 2, v___x_1268_);
v___x_1270_ = lean_mk_empty_array_with_capacity(v___x_1249_);
v___x_1271_ = lean_box(0);
lean_inc(v___x_1249_);
lean_inc_ref(v___x_1270_);
lean_inc_ref(v___x_1269_);
lean_inc(v___x_1250_);
v___x_1272_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1272_, 0, v___x_1261_);
lean_ctor_set(v___x_1272_, 1, v___x_1250_);
lean_ctor_set(v___x_1272_, 2, v___x_1269_);
lean_ctor_set(v___x_1272_, 3, v___x_1270_);
lean_ctor_set(v___x_1272_, 4, v___x_1271_);
lean_ctor_set(v___x_1272_, 5, v___x_1249_);
lean_ctor_set(v___x_1272_, 6, v___x_1271_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7, v___x_1259_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7 + 1, v___x_1259_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7 + 2, v___x_1259_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7 + 3, v___x_1260_);
lean_inc_n(v___x_1249_, 3);
v___x_1273_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1249_);
lean_ctor_set(v___x_1273_, 1, v___x_1249_);
lean_ctor_set(v___x_1273_, 2, v___x_1249_);
lean_ctor_set(v___x_1273_, 3, v___x_1262_);
lean_ctor_set(v___x_1273_, 4, v___x_1262_);
lean_ctor_set(v___x_1273_, 5, v___x_1262_);
lean_ctor_set(v___x_1273_, 6, v___x_1262_);
lean_ctor_set(v___x_1273_, 7, v___x_1262_);
lean_ctor_set(v___x_1273_, 8, v___x_1262_);
v___x_1274_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__5_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3___closed__6_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
lean_inc(v___x_1250_);
v___x_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1273_);
lean_ctor_set(v___x_1276_, 1, v___x_1274_);
lean_ctor_set(v___x_1276_, 2, v___x_1250_);
lean_ctor_set(v___x_1276_, 3, v___x_1267_);
lean_ctor_set(v___x_1276_, 4, v___x_1275_);
v___x_1277_ = lean_st_mk_ref(v___x_1276_);
lean_inc(v_decl_1253_);
v___x_1289_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3(v_decl_1253_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; uint8_t v_foApprox_1292_; uint8_t v_ctxApprox_1293_; uint8_t v_quasiPatternApprox_1294_; uint8_t v_constApprox_1295_; uint8_t v_isDefEqStuckEx_1296_; uint8_t v_unificationHints_1297_; uint8_t v_proofIrrelevance_1298_; uint8_t v_assignSyntheticOpaque_1299_; uint8_t v_offsetCnstrs_1300_; uint8_t v_etaStruct_1301_; uint8_t v_univApprox_1302_; uint8_t v_iota_1303_; uint8_t v_beta_1304_; uint8_t v_proj_1305_; uint8_t v_zeta_1306_; uint8_t v_zetaDelta_1307_; uint8_t v_zetaUnused_1308_; uint8_t v_zetaHave_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1383_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref(v___x_1289_);
v___x_1291_ = l_Lean_Meta_Context_config(v___x_1272_);
v_foApprox_1292_ = lean_ctor_get_uint8(v___x_1291_, 0);
v_ctxApprox_1293_ = lean_ctor_get_uint8(v___x_1291_, 1);
v_quasiPatternApprox_1294_ = lean_ctor_get_uint8(v___x_1291_, 2);
v_constApprox_1295_ = lean_ctor_get_uint8(v___x_1291_, 3);
v_isDefEqStuckEx_1296_ = lean_ctor_get_uint8(v___x_1291_, 4);
v_unificationHints_1297_ = lean_ctor_get_uint8(v___x_1291_, 5);
v_proofIrrelevance_1298_ = lean_ctor_get_uint8(v___x_1291_, 6);
v_assignSyntheticOpaque_1299_ = lean_ctor_get_uint8(v___x_1291_, 7);
v_offsetCnstrs_1300_ = lean_ctor_get_uint8(v___x_1291_, 8);
v_etaStruct_1301_ = lean_ctor_get_uint8(v___x_1291_, 10);
v_univApprox_1302_ = lean_ctor_get_uint8(v___x_1291_, 11);
v_iota_1303_ = lean_ctor_get_uint8(v___x_1291_, 12);
v_beta_1304_ = lean_ctor_get_uint8(v___x_1291_, 13);
v_proj_1305_ = lean_ctor_get_uint8(v___x_1291_, 14);
v_zeta_1306_ = lean_ctor_get_uint8(v___x_1291_, 15);
v_zetaDelta_1307_ = lean_ctor_get_uint8(v___x_1291_, 16);
v_zetaUnused_1308_ = lean_ctor_get_uint8(v___x_1291_, 17);
v_zetaHave_1309_ = lean_ctor_get_uint8(v___x_1291_, 18);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1311_ = v___x_1291_;
v_isShared_1312_ = v_isSharedCheck_1383_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v___x_1291_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1383_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; uint8_t v___x_1315_; lean_object* v_config_1317_; 
v___x_1313_ = l_Lean_ConstantInfo_type(v_a_1290_);
lean_dec(v_a_1290_);
v___x_1314_ = 0;
v___x_1315_ = 2;
if (v_isShared_1312_ == 0)
{
v_config_1317_ = v___x_1311_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 0, v_foApprox_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 1, v_ctxApprox_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 2, v_quasiPatternApprox_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 3, v_constApprox_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 4, v_isDefEqStuckEx_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 5, v_unificationHints_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 6, v_proofIrrelevance_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 7, v_assignSyntheticOpaque_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 8, v_offsetCnstrs_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 10, v_etaStruct_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 11, v_univApprox_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 12, v_iota_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 13, v_beta_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 14, v_proj_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 15, v_zeta_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 16, v_zetaDelta_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 17, v_zetaUnused_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 18, v_zetaHave_1309_);
v_config_1317_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v___x_1322_; uint64_t v_key_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_ctor_set_uint8(v_config_1317_, 9, v___x_1315_);
v___x_1318_ = l_Lean_Meta_Context_configKey(v___x_1272_);
v___x_1319_ = 2ULL;
v___x_1320_ = lean_uint64_shift_right(v___x_1318_, v___x_1319_);
v___x_1321_ = lean_uint64_shift_left(v___x_1320_, v___x_1319_);
v___x_1322_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v_key_1323_ = lean_uint64_lor(v___x_1321_, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1324_, 0, v_config_1317_);
lean_ctor_set_uint64(v___x_1324_, sizeof(void*)*1, v_key_1323_);
v___x_1325_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1250_);
lean_ctor_set(v___x_1325_, 2, v___x_1269_);
lean_ctor_set(v___x_1325_, 3, v___x_1270_);
lean_ctor_set(v___x_1325_, 4, v___x_1271_);
lean_ctor_set(v___x_1325_, 5, v___x_1249_);
lean_ctor_set(v___x_1325_, 6, v___x_1271_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*7, v___x_1259_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*7 + 1, v___x_1259_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*7 + 2, v___x_1259_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*7 + 3, v___x_1260_);
v___x_1326_ = l_Lean_Meta_forallMetaTelescopeReducing(v___x_1313_, v___x_1271_, v___x_1314_, v___x_1325_, v___x_1277_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v_snd_1328_; lean_object* v_snd_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref(v___x_1326_);
v_snd_1328_ = lean_ctor_get(v_a_1327_, 1);
lean_inc(v_snd_1328_);
lean_dec(v_a_1327_);
v_snd_1329_ = lean_ctor_get(v_snd_1328_, 1);
lean_inc(v_snd_1329_);
lean_dec(v_snd_1328_);
v___x_1330_ = l_Lean_Expr_cleanupAnnotations(v_snd_1329_);
v___x_1331_ = l_Lean_Expr_isApp(v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref(v___x_1330_);
lean_dec(v_decl_1253_);
lean_dec_ref(v___x_1252_);
v___x_1332_ = lean_box(0);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___x_1277_);
v___x_1333_ = lean_apply_6(v___f_1251_, v___x_1332_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_, lean_box(0));
v___y_1279_ = v___x_1333_;
goto v___jp_1278_;
}
else
{
lean_object* v_arg_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_arg_1334_ = lean_ctor_get(v___x_1330_, 1);
lean_inc_ref(v_arg_1334_);
v___x_1335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1330_);
v___x_1336_ = l_Lean_Expr_isApp(v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_decl_1253_);
lean_dec_ref(v___x_1252_);
v___x_1337_ = lean_box(0);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___x_1277_);
v___x_1338_ = lean_apply_6(v___f_1251_, v___x_1337_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_, lean_box(0));
v___y_1279_ = v___x_1338_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1335_);
v___x_1340_ = l_Lean_Expr_isApp(v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v___x_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_decl_1253_);
lean_dec_ref(v___x_1252_);
v___x_1341_ = lean_box(0);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___x_1277_);
v___x_1342_ = lean_apply_6(v___f_1251_, v___x_1341_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_, lean_box(0));
v___y_1279_ = v___x_1342_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1339_);
v___x_1344_ = l_Lean_Expr_isApp(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_decl_1253_);
lean_dec_ref(v___x_1252_);
v___x_1345_ = lean_box(0);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___x_1277_);
v___x_1346_ = lean_apply_6(v___f_1251_, v___x_1345_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_, lean_box(0));
v___y_1279_ = v___x_1346_;
goto v___jp_1278_;
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
lean_dec_ref(v_arg_1334_);
lean_dec(v_decl_1253_);
lean_dec_ref(v___x_1252_);
v___x_1349_ = lean_box(0);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___x_1277_);
v___x_1350_ = lean_apply_6(v___f_1251_, v___x_1349_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_, lean_box(0));
v___y_1279_ = v___x_1350_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1347_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1354_ = l_Lean_Name_mkStr3(v___x_1252_, v___x_1352_, v___x_1353_);
v___x_1355_ = l_Lean_Expr_isConstOf(v___x_1351_, v___x_1354_);
lean_dec(v___x_1354_);
lean_dec_ref(v___x_1351_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v_arg_1334_);
lean_dec(v_decl_1253_);
v___x_1356_ = lean_box(0);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___x_1277_);
v___x_1357_ = lean_apply_6(v___f_1251_, v___x_1356_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_, lean_box(0));
v___y_1279_ = v___x_1357_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
lean_dec_ref(v___f_1251_);
v___x_1358_ = lean_box(v_kind_1255_);
v___f_1359_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed), 9, 2);
lean_closure_set(v___f_1359_, 0, v_decl_1253_);
lean_closure_set(v___f_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_Expr_headBeta(v_arg_1334_);
v___x_1361_ = l_Lean_Expr_isLambda(v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Meta_etaExpand(v___x_1360_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___f_1359_, v_a_1363_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___x_1272_);
v___y_1279_ = v___x_1364_;
goto v___jp_1278_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v___f_1359_);
lean_dec(v___x_1277_);
lean_dec_ref(v___x_1272_);
v_a_1365_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1362_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___f_1359_, v___x_1360_, v___x_1272_, v___x_1277_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___x_1272_);
v___y_1279_ = v___x_1373_;
goto v___jp_1278_;
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
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v___x_1277_);
lean_dec_ref(v___x_1272_);
lean_dec(v_decl_1253_);
lean_dec_ref(v___x_1252_);
lean_dec_ref(v___f_1251_);
v_a_1374_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1326_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1326_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v___x_1277_);
lean_dec_ref(v___x_1272_);
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_decl_1253_);
lean_dec_ref(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec(v___x_1250_);
lean_dec(v___x_1249_);
v_a_1384_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1289_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1289_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
v___jp_1278_:
{
if (lean_obj_tag(v___y_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
v_a_1280_ = lean_ctor_get(v___y_1279_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___y_1279_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1282_ = v___y_1279_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___y_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = lean_st_ref_get(v___x_1277_);
lean_dec(v___x_1277_);
lean_dec(v___x_1284_);
if (v_isShared_1283_ == 0)
{
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1280_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_dec(v___x_1277_);
return v___y_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___f_1394_, lean_object* v___x_1395_, lean_object* v_decl_1396_, lean_object* v_x_1397_, lean_object* v_kind_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v_kind_boxed_1402_; lean_object* v_res_1403_; 
v_kind_boxed_1402_ = lean_unbox(v_kind_1398_);
v_res_1403_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___x_1392_, v___x_1393_, v___f_1394_, v___x_1395_, v_decl_1396_, v_x_1397_, v_kind_boxed_1402_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v_x_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_msgData_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v_env_1409_; lean_object* v_options_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1408_ = lean_st_ref_get(v___y_1406_);
v_env_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_ref(v_env_1409_);
lean_dec(v___x_1408_);
v_options_1410_ = lean_ctor_get(v___y_1405_, 2);
v___x_1411_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1412_ = lean_unsigned_to_nat(32u);
v___x_1413_ = lean_mk_empty_array_with_capacity(v___x_1412_);
lean_dec_ref(v___x_1413_);
v___x_1414_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_1410_);
v___x_1415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1415_, 0, v_env_1409_);
lean_ctor_set(v___x_1415_, 1, v___x_1411_);
lean_ctor_set(v___x_1415_, 2, v___x_1414_);
lean_ctor_set(v___x_1415_, 3, v_options_1410_);
v___x_1416_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v_msgData_1404_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_msgData_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6(v_msgData_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_ref_1427_; lean_object* v___x_1428_; lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_ref_1427_ = lean_ctor_get(v___y_1424_, 5);
v___x_1428_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4_spec__6(v_msg_1423_, v___y_1424_, v___y_1425_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_inc(v_ref_1427_);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_ref_1427_);
lean_ctor_set(v___x_1433_, 1, v_a_1429_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 1);
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_msg_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(v_msg_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1442_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(lean_object* v___x_1449_, lean_object* v_decl_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1454_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1455_ = l_Lean_MessageData_ofName(v___x_1449_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(v___x_1458_, v___y_1451_, v___y_1452_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v___x_1460_, lean_object* v_decl_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__4_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(v___x_1460_, v_decl_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_decl_1461_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__33_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1554_ = l_Lean_registerBuiltinAttribute(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1557_, lean_object* v_msg_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v_msg_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_msg_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0(v_00_u03b1_1565_, v_msg_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1573_, lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___redArg(v_msg_1574_, v___y_1575_, v___y_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1579_, lean_object* v_msg_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__4(v_00_u03b1_1579_, v_msg_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b1_1585_, lean_object* v_constName_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___redArg(v_constName_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_constName_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b1_1593_, v_constName_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_00_u03b1_1601_, lean_object* v_ref_1602_, lean_object* v_constName_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ref_1602_, v_constName_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1610_, lean_object* v_ref_1611_, lean_object* v_constName_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_00_u03b1_1610_, v_ref_1611_, v_constName_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v_ref_1611_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1619_, lean_object* v_ref_1620_, lean_object* v_msg_1621_, lean_object* v_declHint_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___redArg(v_ref_1620_, v_msg_1621_, v_declHint_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1629_, lean_object* v_ref_1630_, lean_object* v_msg_1631_, lean_object* v_declHint_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8(v_00_u03b1_1629_, v_ref_1630_, v_msg_1631_, v_declHint_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v_ref_1630_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1639_, lean_object* v_declHint_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1639_, v_declHint_1640_, v___y_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1647_, lean_object* v_declHint_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1647_, v_declHint_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1655_, lean_object* v_ref_1656_, lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1656_, v_msg_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1664_, lean_object* v_ref_1665_, lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1664_, v_ref_1665_, v_msg_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_ref_1665_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___closed__27_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1___closed__0_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_1677_ = l_Lean_addBuiltinDocString(v___x_1675_, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2____boxed(lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___regBuiltin___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_docString__1_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_();
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_findMonoThms(lean_object* v_e_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v_env_1687_; lean_object* v___x_1688_; lean_object* v_ext_1689_; lean_object* v_toEnvExtension_1690_; lean_object* v_asyncMode_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1686_ = lean_st_ref_get(v_a_1684_);
v_env_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc_ref(v_env_1687_);
lean_dec(v___x_1686_);
v___x_1688_ = l_Lean_Meta_Monotonicity_monotoneExt;
v_ext_1689_ = lean_ctor_get(v___x_1688_, 1);
lean_inc_ref(v_ext_1689_);
v_toEnvExtension_1690_ = lean_ctor_get(v_ext_1689_, 0);
lean_inc_ref(v_toEnvExtension_1690_);
lean_dec_ref(v_ext_1689_);
v_asyncMode_1691_ = lean_ctor_get(v_toEnvExtension_1690_, 2);
lean_inc(v_asyncMode_1691_);
lean_dec_ref(v_toEnvExtension_1690_);
v___x_1692_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__3___closed__0);
v___x_1693_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1692_, v___x_1688_, v_env_1687_, v_asyncMode_1691_);
lean_dec(v_asyncMode_1691_);
v___x_1694_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_1693_, v_e_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_findMonoThms___boxed(lean_object* v_e_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_Monotonicity_findMonoThms(v_e_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1701_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__0));
v___x_1704_ = l_Lean_stringToMessageData(v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0(lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
if (lean_obj_tag(v_a_1705_) == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = l_List_reverse___redArg(v_a_1706_);
return v___x_1707_;
}
else
{
lean_object* v_head_1708_; lean_object* v_tail_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1721_; 
v_head_1708_ = lean_ctor_get(v_a_1705_, 0);
v_tail_1709_ = lean_ctor_get(v_a_1705_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_a_1705_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1711_ = v_a_1705_;
v_isShared_1712_ = v_isSharedCheck_1721_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_tail_1709_);
lean_inc(v_head_1708_);
lean_dec(v_a_1705_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1721_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1713_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0___closed__1);
v___x_1714_ = l_Lean_MessageData_ofName(v_head_1708_);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v___x_1713_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v_a_1706_);
lean_ctor_set(v___x_1711_, 0, v___x_1716_);
v___x_1718_ = v___x_1711_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_a_1706_);
v___x_1718_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v_a_1705_ = v_tail_1709_;
v_a_1706_ = v___x_1718_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__0));
v___x_1724_ = l_Lean_stringToMessageData(v___x_1723_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__2));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__4));
v___x_1730_ = l_Lean_stringToMessageData(v___x_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__6));
v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__8));
v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg(lean_object* v_f_1737_, lean_object* v_monoThms_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___y_1745_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_array_get_size(v_monoThms_1738_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_nat_dec_eq(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1756_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__5);
v___x_1757_ = lean_array_to_list(v_monoThms_1738_);
v___x_1758_ = lean_box(0);
v___x_1759_ = l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_defaultFailK_spec__0(v___x_1757_, v___x_1758_);
v___x_1760_ = l_Lean_MessageData_andList(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1756_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__7);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___y_1745_ = v___x_1763_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1764_; 
lean_dec_ref(v_monoThms_1738_);
v___x_1764_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__9);
v___y_1745_ = v___x_1764_;
goto v___jp_1744_;
}
v___jp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1746_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__1);
v___x_1747_ = l_Lean_indentExpr(v_f_1737_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_obj_once(&l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3, &l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3_once, _init_l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__3);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___y_1745_);
v___x_1752_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_1751_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___redArg___boxed(lean_object* v_f_1765_, lean_object* v_monoThms_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Meta_Monotonicity_defaultFailK___redArg(v_f_1765_, v_monoThms_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK(lean_object* v_00_u03b1_1773_, lean_object* v_f_1774_, lean_object* v_monoThms_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Monotonicity_defaultFailK___redArg(v_f_1774_, v_monoThms_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_defaultFailK___boxed(lean_object* v_00_u03b1_1782_, lean_object* v_f_1783_, lean_object* v_monoThms_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_Monotonicity_defaultFailK(v_00_u03b1_1782_, v_f_1783_, v_monoThms_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___lam__0(lean_object* v___x_1791_, lean_object* v_e_1792_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = l_Lean_indentD(v_e_1792_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1791_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__0));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__2));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(lean_object* v_goal_1805_, lean_object* v_name_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1812_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1_once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__1);
v___x_1813_ = 0;
lean_inc(v_name_1806_);
v___x_1814_ = l_Lean_MessageData_ofConstName(v_name_1806_, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1812_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3_once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___f_1818_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___lam__0), 2, 1);
lean_closure_set(v___f_1818_, 0, v___x_1817_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__4));
v___x_1820_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyConst___boxed), 8, 3);
lean_closure_set(v___x_1820_, 0, v_goal_1805_);
lean_closure_set(v___x_1820_, 1, v_name_1806_);
lean_closure_set(v___x_1820_, 2, v___x_1819_);
v___x_1821_ = l_Lean_Meta_mapErrorImp___redArg(v___x_1820_, v___f_1818_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1821_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1821_);
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
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___boxed(lean_object* v_goal_1838_, lean_object* v_name_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_1838_, v_name_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1845_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__0(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = l_Lean_Expr_bvar___override(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__3));
v___x_1855_ = l_Lean_stringToMessageData(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__6(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__5));
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__8(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__7));
v___x_1861_ = l_Lean_stringToMessageData(v___x_1860_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__18(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__17));
v___x_1886_ = l_Lean_stringToMessageData(v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoCall(lean_object* v_00_u03b1_1897_, lean_object* v_inst___u03b1_1898_, lean_object* v_e_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; uint8_t v___y_2165_; uint8_t v___x_2292_; 
v___x_2292_ = l_Lean_Expr_isApp(v_e_1899_);
if (v___x_2292_ == 0)
{
v___y_2165_ = v___x_2292_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = l_Lean_Expr_appArg_x21(v_e_1899_);
v___x_2294_ = l_Lean_Expr_hasLooseBVars(v___x_2293_);
lean_dec_ref(v___x_2293_);
if (v___x_2294_ == 0)
{
v___y_2165_ = v___x_2292_;
goto v___jp_2164_;
}
else
{
v___y_2030_ = v_a_1900_;
v___y_2031_ = v_a_1901_;
v___y_2032_ = v_a_1902_;
v___y_2033_ = v_a_1903_;
goto v___jp_2029_;
}
}
v___jp_1905_:
{
lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__0, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__0_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__0);
v___x_1911_ = lean_expr_eqv(v_e_1899_, v___x_1910_);
lean_dec_ref(v_e_1899_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1914_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__2));
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_00_u03b1_1897_);
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_inst___u03b1_1898_);
v___x_1917_ = lean_unsigned_to_nat(2u);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1917_);
v___x_1919_ = lean_array_push(v___x_1918_, v___x_1915_);
v___x_1920_ = lean_array_push(v___x_1919_, v___x_1916_);
v___x_1921_ = l_Lean_Meta_mkAppOptM(v___x_1914_, v___x_1920_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1930_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_a_1922_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_a_1931_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1921_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1921_);
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
v___jp_1939_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1945_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1899_);
v___x_1946_ = l_Lean_MessageData_ofExpr(v_e_1899_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__6, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__6_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__6);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_MessageData_ofExpr(v___y_1940_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_1951_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_dec_ref(v___x_1952_);
v___y_1906_ = v___y_1941_;
v___y_1907_ = v___y_1942_;
v___y_1908_ = v___y_1943_;
v___y_1909_ = v___y_1944_;
goto v___jp_1905_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
v___jp_1961_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1967_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1899_);
v___x_1968_ = l_Lean_MessageData_ofExpr(v_e_1899_);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__8, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__8_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__8);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = l_Lean_indentExpr(v___y_1962_);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_1973_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_dec_ref(v___x_1974_);
v___y_1906_ = v___y_1963_;
v___y_1907_ = v___y_1964_;
v___y_1908_ = v___y_1965_;
v___y_1909_ = v___y_1966_;
goto v___jp_1905_;
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
v___jp_1983_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___y_1992_);
v___x_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___y_1988_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_00_u03b1_1897_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___y_1987_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1986_);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_inst___u03b1_1898_);
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_unsigned_to_nat(8u);
v___x_2002_ = lean_mk_empty_array_with_capacity(v___x_2001_);
v___x_2003_ = lean_array_push(v___x_2002_, v___x_1994_);
v___x_2004_ = lean_array_push(v___x_2003_, v___x_1995_);
v___x_2005_ = lean_array_push(v___x_2004_, v___x_1996_);
v___x_2006_ = lean_array_push(v___x_2005_, v___x_1997_);
v___x_2007_ = lean_array_push(v___x_2006_, v___x_1998_);
v___x_2008_ = lean_array_push(v___x_2007_, v___x_1999_);
v___x_2009_ = lean_array_push(v___x_2008_, v___x_2000_);
v___x_2010_ = lean_array_push(v___x_2009_, v___y_1989_);
v___x_2011_ = l_Lean_Meta_mkAppOptM(v___y_1993_, v___x_2010_, v___y_1991_, v___y_1984_, v___y_1985_, v___y_1990_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_a_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
v_a_2021_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2011_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2011_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
v___jp_2029_:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Expr_isProj(v_e_1899_);
if (v___x_2034_ == 0)
{
v___y_1906_ = v___y_2030_;
v___y_1907_ = v___y_2031_;
v___y_1908_ = v___y_2032_;
v___y_1909_ = v___y_2033_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = l_Lean_Expr_projExpr_x21(v_e_1899_);
lean_inc_ref(v_inst___u03b1_1898_);
lean_inc_ref(v_00_u03b1_1897_);
v___x_2036_ = l_Lean_Meta_Monotonicity_solveMonoCall(v_00_u03b1_1897_, v_inst___u03b1_1898_, v___x_2035_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2119_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2119_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2119_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
if (lean_obj_tag(v_a_2037_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2042_; 
lean_del_object(v___x_2039_);
v_val_2041_ = lean_ctor_get(v_a_2037_, 0);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2030_);
lean_inc(v_val_2041_);
v___x_2042_ = lean_infer_type(v_val_2041_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2042_);
lean_inc(v_a_2043_);
v___x_2044_ = l_Lean_Expr_cleanupAnnotations(v_a_2043_);
v___x_2045_ = l_Lean_Expr_isApp(v___x_2044_);
if (v___x_2045_ == 0)
{
lean_dec_ref(v___x_2044_);
lean_dec_ref(v_a_2037_);
v___y_1940_ = v_a_2043_;
v___y_1941_ = v___y_2030_;
v___y_1942_ = v___y_2031_;
v___y_1943_ = v___y_2032_;
v___y_1944_ = v___y_2033_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2044_);
v___x_2047_ = l_Lean_Expr_isApp(v___x_2046_);
if (v___x_2047_ == 0)
{
lean_dec_ref(v___x_2046_);
lean_dec_ref(v_a_2037_);
v___y_1940_ = v_a_2043_;
v___y_1941_ = v___y_2030_;
v___y_1942_ = v___y_2031_;
v___y_1943_ = v___y_2032_;
v___y_1944_ = v___y_2033_;
goto v___jp_1939_;
}
else
{
lean_object* v_arg_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_arg_2048_ = lean_ctor_get(v___x_2046_, 1);
lean_inc_ref(v_arg_2048_);
v___x_2049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2046_);
v___x_2050_ = l_Lean_Expr_isApp(v___x_2049_);
if (v___x_2050_ == 0)
{
lean_dec_ref(v___x_2049_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_a_2037_);
v___y_1940_ = v_a_2043_;
v___y_1941_ = v___y_2030_;
v___y_1942_ = v___y_2031_;
v___y_1943_ = v___y_2032_;
v___y_1944_ = v___y_2033_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2049_);
v___x_2052_ = l_Lean_Expr_isApp(v___x_2051_);
if (v___x_2052_ == 0)
{
lean_dec_ref(v___x_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_a_2037_);
v___y_1940_ = v_a_2043_;
v___y_1941_ = v___y_2030_;
v___y_1942_ = v___y_2031_;
v___y_1943_ = v___y_2032_;
v___y_1944_ = v___y_2033_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2051_);
v___x_2054_ = l_Lean_Expr_isApp(v___x_2053_);
if (v___x_2054_ == 0)
{
lean_dec_ref(v___x_2053_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_a_2037_);
v___y_1940_ = v_a_2043_;
v___y_1941_ = v___y_2030_;
v___y_1942_ = v___y_2031_;
v___y_1943_ = v___y_2032_;
v___y_1944_ = v___y_2033_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2053_);
v___x_2056_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__9));
v___x_2057_ = l_Lean_Expr_isConstOf(v___x_2055_, v___x_2056_);
lean_dec_ref(v___x_2055_);
if (v___x_2057_ == 0)
{
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_a_2037_);
v___y_1940_ = v_a_2043_;
v___y_1941_ = v___y_2030_;
v___y_1942_ = v___y_2031_;
v___y_1943_ = v___y_2032_;
v___y_1944_ = v___y_2033_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v_a_2043_);
v___x_2058_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__11));
lean_inc_ref(v_arg_2048_);
v___x_2059_ = l_Lean_Meta_whnfUntil(v_arg_2048_, v___x_2058_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref(v___x_2059_);
if (lean_obj_tag(v_a_2060_) == 1)
{
lean_object* v_val_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v_arg_2048_);
v_val_2061_ = lean_ctor_get(v_a_2060_, 0);
lean_inc(v_val_2061_);
lean_dec_ref(v_a_2060_);
lean_inc(v_val_2061_);
v___x_2062_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_2061_, v___y_2031_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2062_);
v___x_2064_ = l_Lean_Expr_cleanupAnnotations(v_a_2063_);
v___x_2065_ = l_Lean_Expr_isApp(v___x_2064_);
if (v___x_2065_ == 0)
{
lean_dec_ref(v___x_2064_);
lean_dec_ref(v_a_2037_);
v___y_1962_ = v_val_2061_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v_arg_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_arg_2066_ = lean_ctor_get(v___x_2064_, 1);
lean_inc_ref(v_arg_2066_);
v___x_2067_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2064_);
v___x_2068_ = l_Lean_Expr_isApp(v___x_2067_);
if (v___x_2068_ == 0)
{
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_a_2037_);
v___y_1962_ = v_val_2061_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v_arg_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_arg_2069_ = lean_ctor_get(v___x_2067_, 1);
lean_inc_ref(v_arg_2069_);
v___x_2070_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2067_);
v___x_2071_ = l_Lean_Expr_isApp(v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec_ref(v___x_2070_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_a_2037_);
v___y_1962_ = v_val_2061_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v_arg_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_arg_2072_ = lean_ctor_get(v___x_2070_, 1);
lean_inc_ref(v_arg_2072_);
v___x_2073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2070_);
v___x_2074_ = l_Lean_Expr_isApp(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec_ref(v___x_2073_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_a_2037_);
v___y_1962_ = v_val_2061_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v_arg_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_arg_2075_ = lean_ctor_get(v___x_2073_, 1);
lean_inc_ref(v_arg_2075_);
v___x_2076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2073_);
v___x_2077_ = l_Lean_Expr_isConstOf(v___x_2076_, v___x_2058_);
lean_dec_ref(v___x_2076_);
if (v___x_2077_ == 0)
{
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_a_2037_);
v___y_1962_ = v_val_2061_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
lean_dec(v_val_2061_);
v___x_2078_ = l_Lean_Expr_projIdx_x21(v_e_1899_);
lean_dec_ref(v_e_1899_);
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = lean_nat_dec_eq(v___x_2078_, v___x_2079_);
lean_dec(v___x_2078_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__14));
v___y_1984_ = v___y_2031_;
v___y_1985_ = v___y_2032_;
v___y_1986_ = v_arg_2066_;
v___y_1987_ = v_arg_2069_;
v___y_1988_ = v_arg_2072_;
v___y_1989_ = v_a_2037_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2030_;
v___y_1992_ = v_arg_2075_;
v___y_1993_ = v___x_2081_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2082_; 
v___x_2082_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__16));
v___y_1984_ = v___y_2031_;
v___y_1985_ = v___y_2032_;
v___y_1986_ = v_arg_2066_;
v___y_1987_ = v_arg_2069_;
v___y_1988_ = v_arg_2072_;
v___y_1989_ = v_a_2037_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2030_;
v___y_1992_ = v_arg_2075_;
v___y_1993_ = v___x_2082_;
goto v___jp_1983_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_val_2061_);
lean_dec_ref(v_a_2037_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2083_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2062_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2062_);
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
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2037_);
v___x_2091_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1899_);
v___x_2092_ = l_Lean_MessageData_ofExpr(v_e_1899_);
v___x_2093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__18, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__18_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__18);
v___x_2095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2093_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = l_Lean_MessageData_ofExpr(v_arg_2048_);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2097_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref(v___x_2098_);
v___y_1906_ = v___y_2030_;
v___y_1907_ = v___y_2031_;
v___y_1908_ = v___y_2032_;
v___y_1909_ = v___y_2033_;
goto v___jp_1905_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_a_2037_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
return v___x_2059_;
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
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v_a_2037_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2107_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2042_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2042_);
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
else
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec(v_a_2037_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v___x_2115_ = lean_box(0);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2115_);
v___x_2117_ = v___x_2039_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
return v___x_2036_;
}
}
}
v___jp_2120_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2126_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1899_);
v___x_2127_ = l_Lean_MessageData_ofExpr(v_e_1899_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__6, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__6_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__6);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_MessageData_ofExpr(v___y_2121_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2132_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_dec_ref(v___x_2133_);
v___y_2030_ = v___y_2122_;
v___y_2031_ = v___y_2123_;
v___y_2032_ = v___y_2124_;
v___y_2033_ = v___y_2125_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
v___jp_2142_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2148_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1899_);
v___x_2149_ = l_Lean_MessageData_ofExpr(v_e_1899_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__8, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__8_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__8);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_indentExpr(v___y_2143_);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_dec_ref(v___x_2155_);
v___y_2030_ = v___y_2144_;
v___y_2031_ = v___y_2145_;
v___y_2032_ = v___y_2146_;
v___y_2033_ = v___y_2147_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
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
v___jp_2164_:
{
if (v___y_2165_ == 0)
{
v___y_2030_ = v_a_1900_;
v___y_2031_ = v_a_1901_;
v___y_2032_ = v_a_1902_;
v___y_2033_ = v_a_1903_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = l_Lean_Expr_appFn_x21(v_e_1899_);
lean_inc_ref(v_inst___u03b1_1898_);
lean_inc_ref(v_00_u03b1_1897_);
v___x_2167_ = l_Lean_Meta_Monotonicity_solveMonoCall(v_00_u03b1_1897_, v_inst___u03b1_1898_, v___x_2166_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2291_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2291_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2291_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
if (lean_obj_tag(v_a_2168_) == 1)
{
lean_object* v_val_2172_; lean_object* v___x_2173_; 
lean_del_object(v___x_2170_);
v_val_2172_ = lean_ctor_get(v_a_2168_, 0);
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_val_2172_);
v___x_2173_ = lean_infer_type(v_val_2172_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v___x_2173_);
lean_inc(v_a_2174_);
v___x_2175_ = l_Lean_Expr_cleanupAnnotations(v_a_2174_);
v___x_2176_ = l_Lean_Expr_isApp(v___x_2175_);
if (v___x_2176_ == 0)
{
lean_dec_ref(v___x_2175_);
lean_dec_ref(v_a_2168_);
v___y_2121_ = v_a_2174_;
v___y_2122_ = v_a_1900_;
v___y_2123_ = v_a_1901_;
v___y_2124_ = v_a_1902_;
v___y_2125_ = v_a_1903_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2175_);
v___x_2178_ = l_Lean_Expr_isApp(v___x_2177_);
if (v___x_2178_ == 0)
{
lean_dec_ref(v___x_2177_);
lean_dec_ref(v_a_2168_);
v___y_2121_ = v_a_2174_;
v___y_2122_ = v_a_1900_;
v___y_2123_ = v_a_1901_;
v___y_2124_ = v_a_1902_;
v___y_2125_ = v_a_1903_;
goto v___jp_2120_;
}
else
{
lean_object* v_arg_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_arg_2179_ = lean_ctor_get(v___x_2177_, 1);
lean_inc_ref(v_arg_2179_);
v___x_2180_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2177_);
v___x_2181_ = l_Lean_Expr_isApp(v___x_2180_);
if (v___x_2181_ == 0)
{
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v_a_2168_);
v___y_2121_ = v_a_2174_;
v___y_2122_ = v_a_1900_;
v___y_2123_ = v_a_1901_;
v___y_2124_ = v_a_1902_;
v___y_2125_ = v_a_1903_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2180_);
v___x_2183_ = l_Lean_Expr_isApp(v___x_2182_);
if (v___x_2183_ == 0)
{
lean_dec_ref(v___x_2182_);
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v_a_2168_);
v___y_2121_ = v_a_2174_;
v___y_2122_ = v_a_1900_;
v___y_2123_ = v_a_1901_;
v___y_2124_ = v_a_1902_;
v___y_2125_ = v_a_1903_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2182_);
v___x_2185_ = l_Lean_Expr_isApp(v___x_2184_);
if (v___x_2185_ == 0)
{
lean_dec_ref(v___x_2184_);
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v_a_2168_);
v___y_2121_ = v_a_2174_;
v___y_2122_ = v_a_1900_;
v___y_2123_ = v_a_1901_;
v___y_2124_ = v_a_1902_;
v___y_2125_ = v_a_1903_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2184_);
v___x_2187_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__9));
v___x_2188_ = l_Lean_Expr_isConstOf(v___x_2186_, v___x_2187_);
lean_dec_ref(v___x_2186_);
if (v___x_2188_ == 0)
{
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v_a_2168_);
v___y_2121_ = v_a_2174_;
v___y_2122_ = v_a_1900_;
v___y_2123_ = v_a_1901_;
v___y_2124_ = v_a_1902_;
v___y_2125_ = v_a_1903_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_a_2174_);
v___x_2189_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__20));
lean_inc_ref(v_arg_2179_);
v___x_2190_ = l_Lean_Meta_whnfUntil(v_arg_2179_, v___x_2189_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2278_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2278_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2278_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
if (lean_obj_tag(v_a_2191_) == 1)
{
lean_object* v_val_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v_arg_2179_);
v_val_2195_ = lean_ctor_get(v_a_2191_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_a_2191_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2197_ = v_a_2191_;
v_isShared_2198_ = v_isSharedCheck_2261_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_val_2195_);
lean_dec(v_a_2191_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2261_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; 
lean_inc(v_val_2195_);
v___x_2199_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_2195_, v_a_1901_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = l_Lean_Expr_cleanupAnnotations(v_a_2200_);
v___x_2202_ = l_Lean_Expr_isApp(v___x_2201_);
if (v___x_2202_ == 0)
{
lean_dec_ref(v___x_2201_);
lean_del_object(v___x_2197_);
lean_del_object(v___x_2193_);
lean_dec_ref(v_a_2168_);
v___y_2143_ = v_val_2195_;
v___y_2144_ = v_a_1900_;
v___y_2145_ = v_a_1901_;
v___y_2146_ = v_a_1902_;
v___y_2147_ = v_a_1903_;
goto v___jp_2142_;
}
else
{
lean_object* v_arg_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_arg_2203_ = lean_ctor_get(v___x_2201_, 1);
lean_inc_ref(v_arg_2203_);
v___x_2204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2201_);
v___x_2205_ = l_Lean_Expr_isApp(v___x_2204_);
if (v___x_2205_ == 0)
{
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_arg_2203_);
lean_del_object(v___x_2197_);
lean_del_object(v___x_2193_);
lean_dec_ref(v_a_2168_);
v___y_2143_ = v_val_2195_;
v___y_2144_ = v_a_1900_;
v___y_2145_ = v_a_1901_;
v___y_2146_ = v_a_1902_;
v___y_2147_ = v_a_1903_;
goto v___jp_2142_;
}
else
{
lean_object* v_arg_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_arg_2206_ = lean_ctor_get(v___x_2204_, 1);
lean_inc_ref(v_arg_2206_);
v___x_2207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2204_);
v___x_2208_ = l_Lean_Expr_isApp(v___x_2207_);
if (v___x_2208_ == 0)
{
lean_dec_ref(v___x_2207_);
lean_dec_ref(v_arg_2206_);
lean_dec_ref(v_arg_2203_);
lean_del_object(v___x_2197_);
lean_del_object(v___x_2193_);
lean_dec_ref(v_a_2168_);
v___y_2143_ = v_val_2195_;
v___y_2144_ = v_a_1900_;
v___y_2145_ = v_a_1901_;
v___y_2146_ = v_a_1902_;
v___y_2147_ = v_a_1903_;
goto v___jp_2142_;
}
else
{
lean_object* v_arg_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v_arg_2209_ = lean_ctor_get(v___x_2207_, 1);
lean_inc_ref(v_arg_2209_);
v___x_2210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2207_);
v___x_2211_ = l_Lean_Expr_isConstOf(v___x_2210_, v___x_2189_);
lean_dec_ref(v___x_2210_);
if (v___x_2211_ == 0)
{
lean_dec_ref(v_arg_2209_);
lean_dec_ref(v_arg_2206_);
lean_dec_ref(v_arg_2203_);
lean_del_object(v___x_2197_);
lean_del_object(v___x_2193_);
lean_dec_ref(v_a_2168_);
v___y_2143_ = v_val_2195_;
v___y_2144_ = v_a_1900_;
v___y_2145_ = v_a_1901_;
v___y_2146_ = v_a_1902_;
v___y_2147_ = v_a_1903_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_dec(v_val_2195_);
v___x_2212_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__22));
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_arg_2209_);
v___x_2214_ = v___x_2197_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_arg_2209_);
v___x_2214_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2216_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 1);
lean_ctor_set(v___x_2193_, 0, v_arg_2206_);
v___x_2216_ = v___x_2193_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_arg_2206_);
v___x_2216_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_00_u03b1_1897_);
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_inst___u03b1_1898_);
v___x_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_arg_2203_);
v___x_2220_ = l_Lean_Expr_appArg_x21(v_e_1899_);
lean_dec_ref(v_e_1899_);
v___x_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_unsigned_to_nat(8u);
v___x_2224_ = lean_mk_empty_array_with_capacity(v___x_2223_);
v___x_2225_ = lean_array_push(v___x_2224_, v___x_2214_);
v___x_2226_ = lean_array_push(v___x_2225_, v___x_2216_);
v___x_2227_ = lean_array_push(v___x_2226_, v___x_2217_);
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2218_);
v___x_2229_ = lean_array_push(v___x_2228_, v___x_2219_);
v___x_2230_ = lean_array_push(v___x_2229_, v___x_2221_);
v___x_2231_ = lean_array_push(v___x_2230_, v___x_2222_);
v___x_2232_ = lean_array_push(v___x_2231_, v_a_2168_);
v___x_2233_ = l_Lean_Meta_mkAppOptM(v___x_2212_, v___x_2232_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2242_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2242_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2242_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v_a_2234_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2238_);
v___x_2240_ = v___x_2236_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2233_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2233_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
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
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_del_object(v___x_2197_);
lean_dec(v_val_2195_);
lean_del_object(v___x_2193_);
lean_dec_ref(v_a_2168_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2253_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2199_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2199_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_del_object(v___x_2193_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2168_);
v___x_2262_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__4, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__4);
lean_inc_ref(v_e_1899_);
v___x_2263_ = l_Lean_MessageData_ofExpr(v_e_1899_);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoCall___closed__18, &l_Lean_Meta_Monotonicity_solveMonoCall___closed__18_once, _init_l_Lean_Meta_Monotonicity_solveMonoCall___closed__18);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_MessageData_ofExpr(v_arg_2179_);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_2268_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_dec_ref(v___x_2269_);
v___y_2030_ = v_a_1900_;
v___y_2031_ = v_a_1901_;
v___y_2032_ = v_a_1902_;
v___y_2033_ = v_a_1903_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
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
else
{
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v_a_2168_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
return v___x_2190_;
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
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v_a_2168_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v_a_2279_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2173_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2173_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_dec(v_a_2168_);
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
v___x_2287_ = lean_box(0);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2287_);
v___x_2289_ = v___x_2170_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_dec_ref(v_e_1899_);
lean_dec_ref(v_inst___u03b1_1898_);
lean_dec_ref(v_00_u03b1_1897_);
return v___x_2167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoCall___boxed(lean_object* v_00_u03b1_2295_, lean_object* v_inst___u03b1_2296_, lean_object* v_e_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Meta_Monotonicity_solveMonoCall(v_00_u03b1_2295_, v_inst___u03b1_2296_, v_e_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(lean_object* v_e_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v___x_2307_; 
v___x_2307_ = l_Lean_Expr_hasMVar(v_e_2304_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_e_2304_);
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; lean_object* v_mctx_2310_; lean_object* v___x_2311_; lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___x_2314_; lean_object* v_cache_2315_; lean_object* v_zetaDeltaFVarIds_2316_; lean_object* v_postponed_2317_; lean_object* v_diag_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2327_; 
v___x_2309_ = lean_st_ref_get(v___y_2305_);
v_mctx_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc_ref(v_mctx_2310_);
lean_dec(v___x_2309_);
v___x_2311_ = l_Lean_instantiateMVarsCore(v_mctx_2310_, v_e_2304_);
v_fst_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_fst_2312_);
v_snd_2313_ = lean_ctor_get(v___x_2311_, 1);
lean_inc(v_snd_2313_);
lean_dec_ref(v___x_2311_);
v___x_2314_ = lean_st_ref_take(v___y_2305_);
v_cache_2315_ = lean_ctor_get(v___x_2314_, 1);
v_zetaDeltaFVarIds_2316_ = lean_ctor_get(v___x_2314_, 2);
v_postponed_2317_ = lean_ctor_get(v___x_2314_, 3);
v_diag_2318_ = lean_ctor_get(v___x_2314_, 4);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v___x_2314_, 0);
lean_dec(v_unused_2328_);
v___x_2320_ = v___x_2314_;
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_diag_2318_);
lean_inc(v_postponed_2317_);
lean_inc(v_zetaDeltaFVarIds_2316_);
lean_inc(v_cache_2315_);
lean_dec(v___x_2314_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_snd_2313_);
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_snd_2313_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_cache_2315_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_zetaDeltaFVarIds_2316_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_postponed_2317_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_diag_2318_);
v___x_2323_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_st_ref_set(v___y_2305_, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_fst_2312_);
return v___x_2325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg___boxed(lean_object* v_e_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(v_e_2329_, v___y_2330_);
lean_dec(v___y_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0(lean_object* v_e_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(v_e_2333_, v___y_2335_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___boxed(lean_object* v_e_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0(v_e_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(lean_object* v_cls_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_options_2353_; uint8_t v_hasTrace_2354_; 
v_options_2353_ = lean_ctor_get(v___y_2351_, 2);
v_hasTrace_2354_ = lean_ctor_get_uint8(v_options_2353_, sizeof(void*)*1);
if (v_hasTrace_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_cls_2350_);
v___x_2355_ = lean_box(v_hasTrace_2354_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
else
{
lean_object* v_inheritedTraceOptions_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_inheritedTraceOptions_2357_ = lean_ctor_get(v___y_2351_, 13);
v___x_2358_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___closed__1));
v___x_2359_ = l_Lean_Name_append(v___x_2358_, v_cls_2350_);
v___x_2360_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2357_, v_options_2353_, v___x_2359_);
lean_dec(v___x_2359_);
v___x_2361_ = lean_box(v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg___boxed(lean_object* v_cls_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_2363_, v___y_2364_);
lean_dec_ref(v___y_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2(lean_object* v_cls_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_2367_, v___y_2370_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___boxed(lean_object* v_cls_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2(v_cls_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0(lean_object* v_k_2381_, lean_object* v_b_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
v___x_2388_ = lean_apply_6(v_k_2381_, v_b_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, lean_box(0));
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0___boxed(lean_object* v_k_2389_, lean_object* v_b_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0(v_k_2389_, v_b_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(lean_object* v_name_2397_, lean_object* v_type_2398_, lean_object* v_val_2399_, lean_object* v_k_2400_, uint8_t v_nondep_2401_, uint8_t v_kind_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___f_2408_; lean_object* v___x_2409_; 
v___f_2408_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2408_, 0, v_k_2400_);
v___x_2409_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2397_, v_type_2398_, v_val_2399_, v___f_2408_, v_nondep_2401_, v_kind_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v_a_2418_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2409_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2409_);
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
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___boxed(lean_object* v_name_2426_, lean_object* v_type_2427_, lean_object* v_val_2428_, lean_object* v_k_2429_, lean_object* v_nondep_2430_, lean_object* v_kind_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v_nondep_boxed_2437_; uint8_t v_kind_boxed_2438_; lean_object* v_res_2439_; 
v_nondep_boxed_2437_ = lean_unbox(v_nondep_2430_);
v_kind_boxed_2438_ = lean_unbox(v_kind_2431_);
v_res_2439_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(v_name_2426_, v_type_2427_, v_val_2428_, v_k_2429_, v_nondep_boxed_2437_, v_kind_boxed_2438_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9(lean_object* v_00_u03b1_2440_, lean_object* v_name_2441_, lean_object* v_type_2442_, lean_object* v_val_2443_, lean_object* v_k_2444_, uint8_t v_nondep_2445_, uint8_t v_kind_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(v_name_2441_, v_type_2442_, v_val_2443_, v_k_2444_, v_nondep_2445_, v_kind_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_name_2454_, lean_object* v_type_2455_, lean_object* v_val_2456_, lean_object* v_k_2457_, lean_object* v_nondep_2458_, lean_object* v_kind_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
uint8_t v_nondep_boxed_2465_; uint8_t v_kind_boxed_2466_; lean_object* v_res_2467_; 
v_nondep_boxed_2465_ = lean_unbox(v_nondep_2458_);
v_kind_boxed_2466_ = lean_unbox(v_kind_2459_);
v_res_2467_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9(v_00_u03b1_2453_, v_name_2454_, v_type_2455_, v_val_2456_, v_k_2457_, v_nondep_boxed_2465_, v_kind_boxed_2466_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(lean_object* v_mvarId_2468_, lean_object* v_x_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2468_, v_x_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2484_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2475_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2475_);
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
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg___boxed(lean_object* v_mvarId_2492_, lean_object* v_x_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(v_mvarId_2492_, v_x_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10(lean_object* v_00_u03b1_2500_, lean_object* v_mvarId_2501_, lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(v_mvarId_2501_, v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___boxed(lean_object* v_00_u03b1_2509_, lean_object* v_mvarId_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10(v_00_u03b1_2509_, v_mvarId_2510_, v_x_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14___redArg(lean_object* v_x_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_){
_start:
{
lean_object* v_ks_2522_; lean_object* v_vs_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2547_; 
v_ks_2522_ = lean_ctor_get(v_x_2518_, 0);
v_vs_2523_ = lean_ctor_get(v_x_2518_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_x_2518_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2525_ = v_x_2518_;
v_isShared_2526_ = v_isSharedCheck_2547_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_vs_2523_);
lean_inc(v_ks_2522_);
lean_dec(v_x_2518_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2547_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = lean_array_get_size(v_ks_2522_);
v___x_2528_ = lean_nat_dec_lt(v_x_2519_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
lean_dec(v_x_2519_);
v___x_2529_ = lean_array_push(v_ks_2522_, v_x_2520_);
v___x_2530_ = lean_array_push(v_vs_2523_, v_x_2521_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v___x_2530_);
lean_ctor_set(v___x_2525_, 0, v___x_2529_);
v___x_2532_ = v___x_2525_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
else
{
lean_object* v_k_x27_2534_; uint8_t v___x_2535_; 
v_k_x27_2534_ = lean_array_fget_borrowed(v_ks_2522_, v_x_2519_);
v___x_2535_ = l_Lean_instBEqMVarId_beq(v_x_2520_, v_k_x27_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2537_; 
if (v_isShared_2526_ == 0)
{
v___x_2537_ = v___x_2525_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_ks_2522_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_vs_2523_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_unsigned_to_nat(1u);
v___x_2539_ = lean_nat_add(v_x_2519_, v___x_2538_);
lean_dec(v_x_2519_);
v_x_2518_ = v___x_2537_;
v_x_2519_ = v___x_2539_;
goto _start;
}
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2542_ = lean_array_fset(v_ks_2522_, v_x_2519_, v_x_2520_);
v___x_2543_ = lean_array_fset(v_vs_2523_, v_x_2519_, v_x_2521_);
lean_dec(v_x_2519_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v___x_2543_);
lean_ctor_set(v___x_2525_, 0, v___x_2542_);
v___x_2545_ = v___x_2525_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13___redArg(lean_object* v_n_2548_, lean_object* v_k_2549_, lean_object* v_v_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14___redArg(v_n_2548_, v___x_2551_, v_k_2549_, v_v_2550_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(lean_object* v_x_2554_, size_t v_x_2555_, size_t v_x_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v_es_2559_; size_t v___x_2560_; size_t v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; lean_object* v_j_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_es_2559_ = lean_ctor_get(v_x_2554_, 0);
v___x_2560_ = ((size_t)5ULL);
v___x_2561_ = ((size_t)1ULL);
v___x_2562_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2563_ = lean_usize_land(v_x_2555_, v___x_2562_);
v_j_2564_ = lean_usize_to_nat(v___x_2563_);
v___x_2565_ = lean_array_get_size(v_es_2559_);
v___x_2566_ = lean_nat_dec_lt(v_j_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_dec(v_j_2564_);
lean_dec(v_x_2558_);
lean_dec(v_x_2557_);
return v_x_2554_;
}
else
{
lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2603_; 
lean_inc_ref(v_es_2559_);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v_x_2554_, 0);
lean_dec(v_unused_2604_);
v___x_2568_ = v_x_2554_;
v_isShared_2569_ = v_isSharedCheck_2603_;
goto v_resetjp_2567_;
}
else
{
lean_dec(v_x_2554_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2603_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_v_2570_; lean_object* v___x_2571_; lean_object* v_xs_x27_2572_; lean_object* v___y_2574_; 
v_v_2570_ = lean_array_fget(v_es_2559_, v_j_2564_);
v___x_2571_ = lean_box(0);
v_xs_x27_2572_ = lean_array_fset(v_es_2559_, v_j_2564_, v___x_2571_);
switch(lean_obj_tag(v_v_2570_))
{
case 0:
{
lean_object* v_key_2579_; lean_object* v_val_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2590_; 
v_key_2579_ = lean_ctor_get(v_v_2570_, 0);
v_val_2580_ = lean_ctor_get(v_v_2570_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_v_2570_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2582_ = v_v_2570_;
v_isShared_2583_ = v_isSharedCheck_2590_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_val_2580_);
lean_inc(v_key_2579_);
lean_dec(v_v_2570_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2590_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
uint8_t v___x_2584_; 
v___x_2584_ = l_Lean_instBEqMVarId_beq(v_x_2557_, v_key_2579_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_del_object(v___x_2582_);
v___x_2585_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2579_, v_val_2580_, v_x_2557_, v_x_2558_);
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
v___y_2574_ = v___x_2586_;
goto v___jp_2573_;
}
else
{
lean_object* v___x_2588_; 
lean_dec(v_val_2580_);
lean_dec(v_key_2579_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 1, v_x_2558_);
lean_ctor_set(v___x_2582_, 0, v_x_2557_);
v___x_2588_ = v___x_2582_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_x_2557_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_x_2558_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
v___y_2574_ = v___x_2588_;
goto v___jp_2573_;
}
}
}
}
case 1:
{
lean_object* v_node_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2601_; 
v_node_2591_ = lean_ctor_get(v_v_2570_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_v_2570_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2593_ = v_v_2570_;
v_isShared_2594_ = v_isSharedCheck_2601_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_node_2591_);
lean_dec(v_v_2570_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2601_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2595_ = lean_usize_shift_right(v_x_2555_, v___x_2560_);
v___x_2596_ = lean_usize_add(v_x_2556_, v___x_2561_);
v___x_2597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_node_2591_, v___x_2595_, v___x_2596_, v_x_2557_, v_x_2558_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2597_);
v___x_2599_ = v___x_2593_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
v___y_2574_ = v___x_2599_;
goto v___jp_2573_;
}
}
}
default: 
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_x_2557_);
lean_ctor_set(v___x_2602_, 1, v_x_2558_);
v___y_2574_ = v___x_2602_;
goto v___jp_2573_;
}
}
v___jp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_array_fset(v_xs_x27_2572_, v_j_2564_, v___y_2574_);
lean_dec(v_j_2564_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2575_);
v___x_2577_ = v___x_2568_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_object* v_ks_2605_; lean_object* v_vs_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2626_; 
v_ks_2605_ = lean_ctor_get(v_x_2554_, 0);
v_vs_2606_ = lean_ctor_get(v_x_2554_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2608_ = v_x_2554_;
v_isShared_2609_ = v_isSharedCheck_2626_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_vs_2606_);
lean_inc(v_ks_2605_);
lean_dec(v_x_2554_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2626_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_ks_2605_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_vs_2606_);
v___x_2611_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v_newNode_2612_; uint8_t v___y_2614_; size_t v___x_2620_; uint8_t v___x_2621_; 
v_newNode_2612_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13___redArg(v___x_2611_, v_x_2557_, v_x_2558_);
v___x_2620_ = ((size_t)7ULL);
v___x_2621_ = lean_usize_dec_le(v___x_2620_, v_x_2556_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2622_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2612_);
v___x_2623_ = lean_unsigned_to_nat(4u);
v___x_2624_ = lean_nat_dec_lt(v___x_2622_, v___x_2623_);
lean_dec(v___x_2622_);
v___y_2614_ = v___x_2624_;
goto v___jp_2613_;
}
else
{
v___y_2614_ = v___x_2621_;
goto v___jp_2613_;
}
v___jp_2613_:
{
if (v___y_2614_ == 0)
{
lean_object* v_ks_2615_; lean_object* v_vs_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_ks_2615_ = lean_ctor_get(v_newNode_2612_, 0);
lean_inc_ref(v_ks_2615_);
v_vs_2616_ = lean_ctor_get(v_newNode_2612_, 1);
lean_inc_ref(v_vs_2616_);
lean_dec_ref(v_newNode_2612_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___closed__0);
v___x_2619_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(v_x_2556_, v_ks_2615_, v_vs_2616_, v___x_2617_, v___x_2618_);
lean_dec_ref(v_vs_2616_);
lean_dec_ref(v_ks_2615_);
return v___x_2619_;
}
else
{
return v_newNode_2612_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(size_t v_depth_2627_, lean_object* v_keys_2628_, lean_object* v_vals_2629_, lean_object* v_i_2630_, lean_object* v_entries_2631_){
_start:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = lean_array_get_size(v_keys_2628_);
v___x_2633_ = lean_nat_dec_lt(v_i_2630_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_dec(v_i_2630_);
return v_entries_2631_;
}
else
{
lean_object* v_k_2634_; lean_object* v_v_2635_; uint64_t v___x_2636_; size_t v_h_2637_; size_t v___x_2638_; lean_object* v___x_2639_; size_t v___x_2640_; size_t v___x_2641_; size_t v___x_2642_; size_t v_h_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v_k_2634_ = lean_array_fget_borrowed(v_keys_2628_, v_i_2630_);
v_v_2635_ = lean_array_fget_borrowed(v_vals_2629_, v_i_2630_);
v___x_2636_ = l_Lean_instHashableMVarId_hash(v_k_2634_);
v_h_2637_ = lean_uint64_to_usize(v___x_2636_);
v___x_2638_ = ((size_t)5ULL);
v___x_2639_ = lean_unsigned_to_nat(1u);
v___x_2640_ = ((size_t)1ULL);
v___x_2641_ = lean_usize_sub(v_depth_2627_, v___x_2640_);
v___x_2642_ = lean_usize_mul(v___x_2638_, v___x_2641_);
v_h_2643_ = lean_usize_shift_right(v_h_2637_, v___x_2642_);
v___x_2644_ = lean_nat_add(v_i_2630_, v___x_2639_);
lean_dec(v_i_2630_);
lean_inc(v_v_2635_);
lean_inc(v_k_2634_);
v___x_2645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_entries_2631_, v_h_2643_, v_depth_2627_, v_k_2634_, v_v_2635_);
v_i_2630_ = v___x_2644_;
v_entries_2631_ = v___x_2645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg___boxed(lean_object* v_depth_2647_, lean_object* v_keys_2648_, lean_object* v_vals_2649_, lean_object* v_i_2650_, lean_object* v_entries_2651_){
_start:
{
size_t v_depth_boxed_2652_; lean_object* v_res_2653_; 
v_depth_boxed_2652_ = lean_unbox_usize(v_depth_2647_);
lean_dec(v_depth_2647_);
v_res_2653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(v_depth_boxed_2652_, v_keys_2648_, v_vals_2649_, v_i_2650_, v_entries_2651_);
lean_dec_ref(v_vals_2649_);
lean_dec_ref(v_keys_2648_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_2654_, lean_object* v_x_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_){
_start:
{
size_t v_x_41069__boxed_2659_; size_t v_x_41070__boxed_2660_; lean_object* v_res_2661_; 
v_x_41069__boxed_2659_ = lean_unbox_usize(v_x_2655_);
lean_dec(v_x_2655_);
v_x_41070__boxed_2660_ = lean_unbox_usize(v_x_2656_);
lean_dec(v_x_2656_);
v_res_2661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_x_2654_, v_x_41069__boxed_2659_, v_x_41070__boxed_2660_, v_x_2657_, v_x_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1___redArg(lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_){
_start:
{
uint64_t v___x_2665_; size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2665_ = l_Lean_instHashableMVarId_hash(v_x_2663_);
v___x_2666_ = lean_uint64_to_usize(v___x_2665_);
v___x_2667_ = ((size_t)1ULL);
v___x_2668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_x_2662_, v___x_2666_, v___x_2667_, v_x_2663_, v_x_2664_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(lean_object* v_mvarId_2669_, lean_object* v_val_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; lean_object* v_mctx_2674_; lean_object* v_cache_2675_; lean_object* v_zetaDeltaFVarIds_2676_; lean_object* v_postponed_2677_; lean_object* v_diag_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2705_; 
v___x_2673_ = lean_st_ref_take(v___y_2671_);
v_mctx_2674_ = lean_ctor_get(v___x_2673_, 0);
v_cache_2675_ = lean_ctor_get(v___x_2673_, 1);
v_zetaDeltaFVarIds_2676_ = lean_ctor_get(v___x_2673_, 2);
v_postponed_2677_ = lean_ctor_get(v___x_2673_, 3);
v_diag_2678_ = lean_ctor_get(v___x_2673_, 4);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2680_ = v___x_2673_;
v_isShared_2681_ = v_isSharedCheck_2705_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_diag_2678_);
lean_inc(v_postponed_2677_);
lean_inc(v_zetaDeltaFVarIds_2676_);
lean_inc(v_cache_2675_);
lean_inc(v_mctx_2674_);
lean_dec(v___x_2673_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2705_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_depth_2682_; lean_object* v_levelAssignDepth_2683_; lean_object* v_mvarCounter_2684_; lean_object* v_lDepth_2685_; lean_object* v_decls_2686_; lean_object* v_userNames_2687_; lean_object* v_lAssignment_2688_; lean_object* v_eAssignment_2689_; lean_object* v_dAssignment_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2704_; 
v_depth_2682_ = lean_ctor_get(v_mctx_2674_, 0);
v_levelAssignDepth_2683_ = lean_ctor_get(v_mctx_2674_, 1);
v_mvarCounter_2684_ = lean_ctor_get(v_mctx_2674_, 2);
v_lDepth_2685_ = lean_ctor_get(v_mctx_2674_, 3);
v_decls_2686_ = lean_ctor_get(v_mctx_2674_, 4);
v_userNames_2687_ = lean_ctor_get(v_mctx_2674_, 5);
v_lAssignment_2688_ = lean_ctor_get(v_mctx_2674_, 6);
v_eAssignment_2689_ = lean_ctor_get(v_mctx_2674_, 7);
v_dAssignment_2690_ = lean_ctor_get(v_mctx_2674_, 8);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_mctx_2674_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2692_ = v_mctx_2674_;
v_isShared_2693_ = v_isSharedCheck_2704_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_dAssignment_2690_);
lean_inc(v_eAssignment_2689_);
lean_inc(v_lAssignment_2688_);
lean_inc(v_userNames_2687_);
lean_inc(v_decls_2686_);
lean_inc(v_lDepth_2685_);
lean_inc(v_mvarCounter_2684_);
lean_inc(v_levelAssignDepth_2683_);
lean_inc(v_depth_2682_);
lean_dec(v_mctx_2674_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2704_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1___redArg(v_eAssignment_2689_, v_mvarId_2669_, v_val_2670_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 7, v___x_2694_);
v___x_2696_ = v___x_2692_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_depth_2682_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_levelAssignDepth_2683_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_mvarCounter_2684_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_lDepth_2685_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v_decls_2686_);
lean_ctor_set(v_reuseFailAlloc_2703_, 5, v_userNames_2687_);
lean_ctor_set(v_reuseFailAlloc_2703_, 6, v_lAssignment_2688_);
lean_ctor_set(v_reuseFailAlloc_2703_, 7, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2703_, 8, v_dAssignment_2690_);
v___x_2696_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2696_);
v___x_2698_ = v___x_2680_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_cache_2675_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_zetaDeltaFVarIds_2676_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_postponed_2677_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_diag_2678_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = lean_st_ref_set(v___y_2671_, v___x_2698_);
v___x_2700_ = lean_box(0);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg___boxed(lean_object* v_mvarId_2706_, lean_object* v_val_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_mvarId_2706_, v_val_2707_, v___y_2708_);
lean_dec(v___y_2708_);
return v_res_2710_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2712_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__2));
v___x_2713_ = lean_unsigned_to_nat(20u);
v___x_2714_ = lean_unsigned_to_nat(1918u);
v___x_2715_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__0));
v___x_2716_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__1___closed__0));
v___x_2717_ = l_mkPanicMessageWithDecl(v___x_2716_, v___x_2715_, v___x_2714_, v___x_2713_, v___x_2712_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0(lean_object* v_a_2718_, uint8_t v___x_2719_, uint8_t v___x_2720_, lean_object* v_goal_2721_, lean_object* v___x_2722_, lean_object* v_body_2723_, lean_object* v_x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___y_2731_; 
if (lean_obj_tag(v___x_2722_) == 6)
{
lean_object* v_binderName_2752_; lean_object* v_binderType_2753_; lean_object* v_body_2754_; uint8_t v_binderInfo_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___y_2759_; size_t v___x_2763_; size_t v___x_2764_; uint8_t v___x_2765_; 
v_binderName_2752_ = lean_ctor_get(v___x_2722_, 0);
v_binderType_2753_ = lean_ctor_get(v___x_2722_, 1);
v_body_2754_ = lean_ctor_get(v___x_2722_, 2);
v_binderInfo_2755_ = lean_ctor_get_uint8(v___x_2722_, sizeof(void*)*3 + 8);
v___x_2756_ = l_Lean_Expr_bindingDomain_x21(v___x_2722_);
v___x_2757_ = lean_expr_instantiate1(v_body_2723_, v_x_2724_);
v___x_2763_ = lean_ptr_addr(v_binderType_2753_);
v___x_2764_ = lean_ptr_addr(v___x_2756_);
v___x_2765_ = lean_usize_dec_eq(v___x_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
v___y_2759_ = v___x_2765_;
goto v___jp_2758_;
}
else
{
size_t v___x_2766_; size_t v___x_2767_; uint8_t v___x_2768_; 
v___x_2766_ = lean_ptr_addr(v_body_2754_);
v___x_2767_ = lean_ptr_addr(v___x_2757_);
v___x_2768_ = lean_usize_dec_eq(v___x_2766_, v___x_2767_);
v___y_2759_ = v___x_2768_;
goto v___jp_2758_;
}
v___jp_2758_:
{
if (v___y_2759_ == 0)
{
lean_object* v___x_2760_; 
lean_inc(v_binderName_2752_);
lean_dec_ref(v___x_2722_);
v___x_2760_ = l_Lean_Expr_lam___override(v_binderName_2752_, v___x_2756_, v___x_2757_, v_binderInfo_2755_);
v___y_2731_ = v___x_2760_;
goto v___jp_2730_;
}
else
{
uint8_t v___x_2761_; 
v___x_2761_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2755_, v_binderInfo_2755_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; 
lean_inc(v_binderName_2752_);
lean_dec_ref(v___x_2722_);
v___x_2762_ = l_Lean_Expr_lam___override(v_binderName_2752_, v___x_2756_, v___x_2757_, v_binderInfo_2755_);
v___y_2731_ = v___x_2762_;
goto v___jp_2730_;
}
else
{
lean_dec_ref(v___x_2757_);
lean_dec_ref(v___x_2756_);
v___y_2731_ = v___x_2722_;
goto v___jp_2730_;
}
}
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec_ref(v___x_2722_);
v___x_2769_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1);
v___x_2770_ = l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(v___x_2769_);
v___y_2731_ = v___x_2770_;
goto v___jp_2730_;
}
v___jp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2732_ = l_Lean_Expr_appFn_x21(v_a_2718_);
v___x_2733_ = l_Lean_Expr_app___override(v___x_2732_, v___y_2731_);
v___x_2734_ = lean_box(0);
v___x_2735_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2733_, v___x_2734_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref(v___x_2735_);
v___x_2737_ = lean_unsigned_to_nat(1u);
v___x_2738_ = lean_mk_empty_array_with_capacity(v___x_2737_);
v___x_2739_ = lean_array_push(v___x_2738_, v_x_2724_);
v___x_2740_ = 1;
lean_inc(v_a_2736_);
v___x_2741_ = l_Lean_Meta_mkLetFVars(v___x_2739_, v_a_2736_, v___x_2719_, v___x_2720_, v___x_2740_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec_ref(v___x_2739_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref(v___x_2741_);
v___x_2743_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_2721_, v_a_2742_, v___y_2726_);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v___x_2743_, 0);
lean_dec(v_unused_2751_);
v___x_2745_ = v___x_2743_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_dec(v___x_2743_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v_a_2736_);
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2736_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
else
{
lean_dec(v_a_2736_);
lean_dec(v_goal_2721_);
return v___x_2741_;
}
}
else
{
lean_dec_ref(v_x_2724_);
lean_dec(v_goal_2721_);
return v___x_2735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___boxed(lean_object* v_a_2771_, lean_object* v___x_2772_, lean_object* v___x_2773_, lean_object* v_goal_2774_, lean_object* v___x_2775_, lean_object* v_body_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
uint8_t v___x_41299__boxed_2783_; uint8_t v___x_41300__boxed_2784_; lean_object* v_res_2785_; 
v___x_41299__boxed_2783_ = lean_unbox(v___x_2772_);
v___x_41300__boxed_2784_ = lean_unbox(v___x_2773_);
v_res_2785_ = l_Lean_Meta_Monotonicity_solveMonoStep___lam__0(v_a_2771_, v___x_41299__boxed_2783_, v___x_41300__boxed_2784_, v_goal_2774_, v___x_2775_, v_body_2776_, v_x_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v_body_2776_);
lean_dec_ref(v_a_2771_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__1(lean_object* v___x_2786_, lean_object* v_f_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_expr_instantiate1(v___x_2786_, v_f_2787_);
v___x_2794_ = l_Lean_Meta_Monotonicity_findMonoThms(v___x_2793_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__1___boxed(lean_object* v___x_2795_, lean_object* v_f_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_Monotonicity_solveMonoStep___lam__1(v___x_2795_, v_f_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec_ref(v_f_2796_);
lean_dec_ref(v___x_2795_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7(uint8_t v___x_2803_, size_t v_sz_2804_, size_t v_i_2805_, lean_object* v_bs_2806_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_usize_dec_lt(v_i_2805_, v_sz_2804_);
if (v___x_2807_ == 0)
{
return v_bs_2806_;
}
else
{
lean_object* v_v_2808_; lean_object* v___x_2809_; lean_object* v_bs_x27_2810_; lean_object* v___x_2811_; size_t v___x_2812_; size_t v___x_2813_; lean_object* v___x_2814_; 
v_v_2808_ = lean_array_uget(v_bs_2806_, v_i_2805_);
v___x_2809_ = lean_unsigned_to_nat(0u);
v_bs_x27_2810_ = lean_array_uset(v_bs_2806_, v_i_2805_, v___x_2809_);
v___x_2811_ = l_Lean_MessageData_ofConstName(v_v_2808_, v___x_2803_);
v___x_2812_ = ((size_t)1ULL);
v___x_2813_ = lean_usize_add(v_i_2805_, v___x_2812_);
v___x_2814_ = lean_array_uset(v_bs_x27_2810_, v_i_2805_, v___x_2811_);
v_i_2805_ = v___x_2813_;
v_bs_2806_ = v___x_2814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7___boxed(lean_object* v___x_2816_, lean_object* v_sz_2817_, lean_object* v_i_2818_, lean_object* v_bs_2819_){
_start:
{
uint8_t v___x_41443__boxed_2820_; size_t v_sz_boxed_2821_; size_t v_i_boxed_2822_; lean_object* v_res_2823_; 
v___x_41443__boxed_2820_ = lean_unbox(v___x_2816_);
v_sz_boxed_2821_ = lean_unbox_usize(v_sz_2817_);
lean_dec(v_sz_2817_);
v_i_boxed_2822_ = lean_unbox_usize(v_i_2818_);
lean_dec(v_i_2818_);
v_res_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7(v___x_41443__boxed_2820_, v_sz_boxed_2821_, v_i_boxed_2822_, v_bs_2819_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(lean_object* v_upperBound_2827_, lean_object* v___x_2828_, uint8_t v___x_2829_, lean_object* v_a_2830_, lean_object* v_b_2831_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_nat_dec_lt(v_a_2830_, v_upperBound_2827_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
lean_dec(v_a_2830_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_b_2831_);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
lean_dec_ref(v_b_2831_);
v___x_2835_ = lean_box(0);
v___x_2836_ = l_Lean_instInhabitedExpr;
v___x_2837_ = lean_array_get_borrowed(v___x_2836_, v___x_2828_, v_a_2830_);
v___x_2838_ = l_Lean_Expr_hasLooseBVars(v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___closed__0));
v___x_2840_ = lean_unsigned_to_nat(1u);
v___x_2841_ = lean_nat_add(v_a_2830_, v___x_2840_);
lean_dec(v_a_2830_);
v_a_2830_ = v___x_2841_;
v_b_2831_ = v___x_2839_;
goto _start;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec(v_a_2830_);
v___x_2843_ = lean_box(v___x_2829_);
v___x_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v___x_2835_);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg___boxed(lean_object* v_upperBound_2847_, lean_object* v___x_2848_, lean_object* v___x_2849_, lean_object* v_a_2850_, lean_object* v_b_2851_, lean_object* v___y_2852_){
_start:
{
uint8_t v___x_41468__boxed_2853_; lean_object* v_res_2854_; 
v___x_41468__boxed_2853_ = lean_unbox(v___x_2849_);
v_res_2854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(v_upperBound_2847_, v___x_2848_, v___x_41468__boxed_2853_, v_a_2850_, v_b_2851_);
lean_dec_ref(v___x_2848_);
lean_dec(v_upperBound_2847_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(lean_object* v_name_2855_, uint8_t v_bi_2856_, lean_object* v_type_2857_, lean_object* v_k_2858_, uint8_t v_kind_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___f_2865_; lean_object* v___x_2866_; 
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2865_, 0, v_k_2858_);
v___x_2866_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2855_, v_bi_2856_, v_type_2857_, v___f_2865_, v_kind_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2875_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2866_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2866_);
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
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg___boxed(lean_object* v_name_2883_, lean_object* v_bi_2884_, lean_object* v_type_2885_, lean_object* v_k_2886_, lean_object* v_kind_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v_bi_boxed_2893_; uint8_t v_kind_boxed_2894_; lean_object* v_res_2895_; 
v_bi_boxed_2893_ = lean_unbox(v_bi_2884_);
v_kind_boxed_2894_ = lean_unbox(v_kind_2887_);
v_res_2895_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(v_name_2883_, v_bi_boxed_2893_, v_type_2885_, v_k_2886_, v_kind_boxed_2894_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(lean_object* v_name_2896_, lean_object* v_type_2897_, lean_object* v_k_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
uint8_t v___x_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = 0;
v___x_2905_ = 0;
v___x_2906_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(v_name_2896_, v___x_2904_, v_type_2897_, v_k_2898_, v___x_2905_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg___boxed(lean_object* v_name_2907_, lean_object* v_type_2908_, lean_object* v_k_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(v_name_2907_, v_type_2908_, v_k_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2915_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2916_; double v___x_2917_; 
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = lean_float_of_nat(v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(lean_object* v_cls_2920_, lean_object* v_msg_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_ref_2927_; lean_object* v___x_2928_; lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2973_; 
v_ref_2927_ = lean_ctor_get(v___y_2924_, 5);
v___x_2928_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0_spec__0(v_msg_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2973_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2973_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v_traceState_2934_; lean_object* v_env_2935_; lean_object* v_nextMacroScope_2936_; lean_object* v_ngen_2937_; lean_object* v_auxDeclNGen_2938_; lean_object* v_cache_2939_; lean_object* v_messages_2940_; lean_object* v_infoState_2941_; lean_object* v_snapshotTasks_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2972_; 
v___x_2933_ = lean_st_ref_take(v___y_2925_);
v_traceState_2934_ = lean_ctor_get(v___x_2933_, 4);
v_env_2935_ = lean_ctor_get(v___x_2933_, 0);
v_nextMacroScope_2936_ = lean_ctor_get(v___x_2933_, 1);
v_ngen_2937_ = lean_ctor_get(v___x_2933_, 2);
v_auxDeclNGen_2938_ = lean_ctor_get(v___x_2933_, 3);
v_cache_2939_ = lean_ctor_get(v___x_2933_, 5);
v_messages_2940_ = lean_ctor_get(v___x_2933_, 6);
v_infoState_2941_ = lean_ctor_get(v___x_2933_, 7);
v_snapshotTasks_2942_ = lean_ctor_get(v___x_2933_, 8);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2944_ = v___x_2933_;
v_isShared_2945_ = v_isSharedCheck_2972_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_snapshotTasks_2942_);
lean_inc(v_infoState_2941_);
lean_inc(v_messages_2940_);
lean_inc(v_cache_2939_);
lean_inc(v_traceState_2934_);
lean_inc(v_auxDeclNGen_2938_);
lean_inc(v_ngen_2937_);
lean_inc(v_nextMacroScope_2936_);
lean_inc(v_env_2935_);
lean_dec(v___x_2933_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2972_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
uint64_t v_tid_2946_; lean_object* v_traces_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2971_; 
v_tid_2946_ = lean_ctor_get_uint64(v_traceState_2934_, sizeof(void*)*1);
v_traces_2947_ = lean_ctor_get(v_traceState_2934_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_traceState_2934_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2949_ = v_traceState_2934_;
v_isShared_2950_ = v_isSharedCheck_2971_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_traces_2947_);
lean_dec(v_traceState_2934_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2971_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; double v___x_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2951_ = lean_box(0);
v___x_2952_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__0);
v___x_2953_ = 0;
v___x_2954_ = ((lean_object*)(l_Lean_Meta_Monotonicity_defaultFailK___redArg___closed__8));
v___x_2955_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2955_, 0, v_cls_2920_);
lean_ctor_set(v___x_2955_, 1, v___x_2951_);
lean_ctor_set(v___x_2955_, 2, v___x_2954_);
lean_ctor_set_float(v___x_2955_, sizeof(void*)*3, v___x_2952_);
lean_ctor_set_float(v___x_2955_, sizeof(void*)*3 + 8, v___x_2952_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*3 + 16, v___x_2953_);
v___x_2956_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___closed__1));
v___x_2957_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v_a_2929_);
lean_ctor_set(v___x_2957_, 2, v___x_2956_);
lean_inc(v_ref_2927_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v_ref_2927_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = l_Lean_PersistentArray_push___redArg(v_traces_2947_, v___x_2958_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2959_);
v___x_2961_ = v___x_2949_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2959_);
lean_ctor_set_uint64(v_reuseFailAlloc_2970_, sizeof(void*)*1, v_tid_2946_);
v___x_2961_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2963_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 4, v___x_2961_);
v___x_2963_ = v___x_2944_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_env_2935_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_nextMacroScope_2936_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_ngen_2937_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_auxDeclNGen_2938_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2969_, 5, v_cache_2939_);
lean_ctor_set(v_reuseFailAlloc_2969_, 6, v_messages_2940_);
lean_ctor_set(v_reuseFailAlloc_2969_, 7, v_infoState_2941_);
lean_ctor_set(v_reuseFailAlloc_2969_, 8, v_snapshotTasks_2942_);
v___x_2963_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2964_ = lean_st_ref_set(v___y_2925_, v___x_2963_);
v___x_2965_ = lean_box(0);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 0, v___x_2965_);
v___x_2967_ = v___x_2931_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3___boxed(lean_object* v_cls_2974_, lean_object* v_msg_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_2974_, v_msg_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(lean_object* v_a_2982_, lean_object* v_____r_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_a_2982_);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0___boxed(lean_object* v_a_2991_, lean_object* v_____r_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(v_a_2991_, v_____r_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_2998_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__3));
v___x_3009_ = l_Lean_stringToMessageData(v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5(lean_object* v_goal_3010_, uint8_t v___x_3011_, lean_object* v_as_3012_, size_t v_sz_3013_, size_t v_i_3014_, lean_object* v_b_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_a_3022_; uint8_t v___x_3026_; 
v___x_3026_ = lean_usize_dec_lt(v_i_3014_, v_sz_3013_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
lean_dec(v_goal_3010_);
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_b_3015_);
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v_cls_3030_; lean_object* v___y_3032_; uint8_t v___y_3033_; lean_object* v_a_3057_; lean_object* v___y_3061_; lean_object* v_a_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v_b_3015_);
v___x_3028_ = lean_box(0);
v___x_3029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__0));
v_cls_3030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2));
v_a_3072_ = lean_array_uget_borrowed(v_as_3012_, v_i_3014_);
lean_inc(v_a_3072_);
lean_inc(v_goal_3010_);
v___x_3073_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3010_, v_a_3072_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v___x_3073_);
v___x_3075_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3030_, v___y_3018_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; uint8_t v___x_3077_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref(v___x_3075_);
v___x_3077_ = lean_unbox(v_a_3076_);
lean_dec(v_a_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(v_a_3074_, v___x_3028_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
v___y_3061_ = v___x_3078_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__4);
lean_inc(v_a_3072_);
v___x_3080_ = l_Lean_MessageData_ofConstName(v_a_3072_, v___x_3011_);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3030_, v___x_3081_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3084_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref(v___x_3082_);
v___x_3084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___lam__0(v_a_3074_, v_a_3083_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
v___y_3061_ = v___x_3084_;
goto v___jp_3060_;
}
else
{
lean_object* v_a_3085_; 
lean_dec(v_a_3074_);
v_a_3085_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3085_);
lean_dec_ref(v___x_3082_);
v_a_3057_ = v_a_3085_;
goto v___jp_3056_;
}
}
}
else
{
lean_object* v_a_3086_; 
lean_dec(v_a_3074_);
v_a_3086_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___x_3075_);
v_a_3057_ = v_a_3086_;
goto v___jp_3056_;
}
}
else
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3073_);
v_a_3057_ = v_a_3087_;
goto v___jp_3056_;
}
v___jp_3031_:
{
if (v___y_3033_ == 0)
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3030_, v___y_3018_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; uint8_t v___x_3036_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
v___x_3036_ = lean_unbox(v_a_3035_);
lean_dec(v_a_3035_);
if (v___x_3036_ == 0)
{
lean_dec_ref(v___y_3032_);
v_a_3022_ = v___x_3029_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = l_Lean_Exception_toMessageData(v___y_3032_);
v___x_3038_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3030_, v___x_3037_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_dec_ref(v___x_3038_);
v_a_3022_ = v___x_3029_;
goto v___jp_3021_;
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v_goal_3010_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v___y_3032_);
lean_dec(v_goal_3010_);
v_a_3047_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3034_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3034_);
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
else
{
lean_object* v___x_3055_; 
lean_dec(v_goal_3010_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___y_3032_);
return v___x_3055_;
}
}
v___jp_3056_:
{
uint8_t v___x_3058_; 
v___x_3058_ = l_Lean_Exception_isInterrupt(v_a_3057_);
if (v___x_3058_ == 0)
{
uint8_t v___x_3059_; 
lean_inc_ref(v_a_3057_);
v___x_3059_ = l_Lean_Exception_isRuntime(v_a_3057_);
v___y_3032_ = v_a_3057_;
v___y_3033_ = v___x_3059_;
goto v___jp_3031_;
}
else
{
v___y_3032_ = v_a_3057_;
v___y_3033_ = v___x_3058_;
goto v___jp_3031_;
}
}
v___jp_3060_:
{
if (lean_obj_tag(v___y_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3070_; 
v_a_3062_ = lean_ctor_get(v___y_3061_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___y_3061_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3064_ = v___y_3061_;
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___y_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
if (lean_obj_tag(v_a_3062_) == 1)
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
lean_dec(v_goal_3010_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_a_3062_);
lean_ctor_set(v___x_3066_, 1, v___x_3028_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v___x_3066_);
v___x_3068_ = v___x_3064_;
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
lean_del_object(v___x_3064_);
lean_dec(v_a_3062_);
v_a_3022_ = v___x_3029_;
goto v___jp_3021_;
}
}
}
else
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v___y_3061_, 0);
lean_inc(v_a_3071_);
lean_dec_ref(v___y_3061_);
v_a_3057_ = v_a_3071_;
goto v___jp_3056_;
}
}
}
v___jp_3021_:
{
size_t v___x_3023_; size_t v___x_3024_; 
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_add(v_i_3014_, v___x_3023_);
v_i_3014_ = v___x_3024_;
v_b_3015_ = v_a_3022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___boxed(lean_object* v_goal_3088_, lean_object* v___x_3089_, lean_object* v_as_3090_, lean_object* v_sz_3091_, lean_object* v_i_3092_, lean_object* v_b_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
uint8_t v___x_41729__boxed_3099_; size_t v_sz_boxed_3100_; size_t v_i_boxed_3101_; lean_object* v_res_3102_; 
v___x_41729__boxed_3099_ = lean_unbox(v___x_3089_);
v_sz_boxed_3100_ = lean_unbox_usize(v_sz_3091_);
lean_dec(v_sz_3091_);
v_i_boxed_3101_ = lean_unbox_usize(v_i_3092_);
lean_dec(v_i_3092_);
v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5(v_goal_3088_, v___x_41729__boxed_3099_, v_as_3090_, v_sz_boxed_3100_, v_i_boxed_3101_, v_b_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec_ref(v_as_3090_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__8(lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
if (lean_obj_tag(v_a_3103_) == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = l_List_reverse___redArg(v_a_3104_);
return v___x_3105_;
}
else
{
lean_object* v_head_3106_; lean_object* v_tail_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3115_; 
v_head_3106_ = lean_ctor_get(v_a_3103_, 0);
v_tail_3107_ = lean_ctor_get(v_a_3103_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_a_3103_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3109_ = v_a_3103_;
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_tail_3107_);
lean_inc(v_head_3106_);
lean_dec(v_a_3103_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v_a_3104_);
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_head_3106_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_a_3104_);
v___x_3112_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
v_a_3103_ = v_tail_3107_;
v_a_3104_ = v___x_3112_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__0));
v___x_3118_ = l_Lean_stringToMessageData(v___x_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2(void){
_start:
{
lean_object* v___x_3119_; lean_object* v_dummy_3120_; 
v___x_3119_ = lean_box(0);
v_dummy_3120_ = l_Lean_Expr_sort___override(v___x_3119_);
return v_dummy_3120_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__3));
v___x_3123_ = l_Lean_stringToMessageData(v___x_3122_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__5));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__7));
v___x_3129_ = l_Lean_stringToMessageData(v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__9));
v___x_3132_ = l_Lean_stringToMessageData(v___x_3131_);
return v___x_3132_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__13));
v___x_3138_ = l_Lean_stringToMessageData(v___x_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__15));
v___x_3141_ = l_Lean_stringToMessageData(v___x_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__19));
v___x_3146_ = l_Lean_stringToMessageData(v___x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2(lean_object* v_cls_3147_, lean_object* v_goal_3148_, lean_object* v_failK_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3165_; lean_object* v___y_3166_; uint8_t v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3399_; lean_object* v___y_3400_; uint8_t v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3460_; lean_object* v___y_3461_; uint8_t v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; uint8_t v___y_3559_; uint8_t v___y_3644_; lean_object* v___y_3645_; uint8_t v___y_3646_; uint8_t v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v_f_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___x_3747_; lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3767_; 
lean_inc(v_cls_3147_);
v___x_3747_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3147_, v___y_3152_);
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3767_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3767_;
goto v_resetjp_3749_;
}
v___jp_3155_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3160_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__1);
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v_goal_3148_);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_3162_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
return v___x_3163_;
}
v___jp_3164_:
{
lean_object* v___x_3173_; size_t v_sz_3174_; size_t v___x_3175_; lean_object* v___x_3176_; 
v___x_3173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__0));
v_sz_3174_ = lean_array_size(v___y_3168_);
v___x_3175_ = ((size_t)0ULL);
lean_inc(v_goal_3148_);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5(v_goal_3148_, v___y_3167_, v___y_3168_, v_sz_3174_, v___x_3175_, v___x_3173_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3216_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3216_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3216_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v_fst_3181_; 
v_fst_3181_ = lean_ctor_get(v_a_3177_, 0);
lean_inc(v_fst_3181_);
lean_dec(v_a_3177_);
if (lean_obj_tag(v_fst_3181_) == 0)
{
lean_object* v___x_3182_; lean_object* v_env_3183_; lean_object* v___x_3184_; 
lean_del_object(v___x_3179_);
v___x_3182_ = lean_st_ref_get(v___y_3172_);
v_env_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_ref(v_env_3183_);
lean_dec(v___x_3182_);
v___x_3184_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_3183_, v___y_3166_);
if (lean_obj_tag(v___x_3184_) == 1)
{
lean_object* v_val_3185_; lean_object* v_numDiscrs_3186_; lean_object* v_nargs_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v_dummy_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_val_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_val_3185_);
lean_dec_ref(v___x_3184_);
v_numDiscrs_3186_ = lean_ctor_get(v_val_3185_, 1);
lean_inc(v_numDiscrs_3186_);
v_nargs_3187_ = l_Lean_Expr_getAppNumArgs(v___y_3166_);
v___x_3188_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_3185_);
lean_dec(v_val_3185_);
v___x_3189_ = lean_nat_add(v___x_3188_, v_numDiscrs_3186_);
lean_dec(v_numDiscrs_3186_);
v_dummy_3190_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__2);
lean_inc(v_nargs_3187_);
v___x_3191_ = lean_mk_array(v_nargs_3187_, v_dummy_3190_);
v___x_3192_ = lean_unsigned_to_nat(1u);
v___x_3193_ = lean_nat_sub(v_nargs_3187_, v___x_3192_);
lean_dec(v_nargs_3187_);
lean_inc_ref(v___y_3166_);
v___x_3194_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3166_, v___x_3191_, v___x_3193_);
v___x_3195_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(v___x_3189_, v___x_3194_, v___y_3167_, v___x_3188_, v___x_3173_);
lean_dec_ref(v___x_3194_);
lean_dec(v___x_3189_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v_fst_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref(v___x_3195_);
v_fst_3197_ = lean_ctor_get(v_a_3196_, 0);
lean_inc(v_fst_3197_);
lean_dec(v_a_3196_);
if (lean_obj_tag(v_fst_3197_) == 0)
{
lean_object* v___x_3198_; 
lean_dec_ref(v___y_3168_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v_failK_3149_);
v___x_3198_ = l_Lean_Meta_Split_splitMatch(v_goal_3148_, v___y_3166_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
return v___x_3198_;
}
else
{
lean_object* v_val_3199_; uint8_t v___x_3200_; 
v_val_3199_ = lean_ctor_get(v_fst_3197_, 0);
lean_inc(v_val_3199_);
lean_dec_ref(v_fst_3197_);
v___x_3200_ = lean_unbox(v_val_3199_);
lean_dec(v_val_3199_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_dec_ref(v___y_3166_);
lean_dec(v_goal_3148_);
v___x_3201_ = lean_apply_8(v_failK_3149_, lean_box(0), v___y_3165_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, lean_box(0));
return v___x_3201_;
}
else
{
lean_object* v___x_3202_; 
lean_dec_ref(v___y_3168_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v_failK_3149_);
v___x_3202_ = l_Lean_Meta_Split_splitMatch(v_goal_3148_, v___y_3166_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
v_a_3203_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3195_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3195_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v___x_3211_; 
lean_dec(v___x_3184_);
lean_dec_ref(v___y_3166_);
lean_dec(v_goal_3148_);
v___x_3211_ = lean_apply_8(v_failK_3149_, lean_box(0), v___y_3165_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, lean_box(0));
return v___x_3211_;
}
}
else
{
lean_object* v_val_3212_; lean_object* v___x_3214_; 
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
v_val_3212_ = lean_ctor_get(v_fst_3181_, 0);
lean_inc(v_val_3212_);
lean_dec_ref(v_fst_3181_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 0, v_val_3212_);
v___x_3214_ = v___x_3179_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_val_3212_);
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
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
v_a_3217_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3176_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3176_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
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
v___jp_3225_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___y_3227_);
v___x_3231_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_3148_, v___y_3226_, v___y_3228_);
lean_dec(v___y_3228_);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v___x_3231_, 0);
lean_dec(v_unused_3240_);
v___x_3233_ = v___x_3231_;
v_isShared_3234_ = v_isSharedCheck_3239_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3231_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3239_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3235_ = lean_box(0);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3235_);
v___x_3237_ = v___x_3233_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
v___jp_3241_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2__spec__0_spec__2___closed__0));
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
v___x_3249_ = lean_apply_8(v_failK_3149_, lean_box(0), v___y_3242_, v___x_3248_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, lean_box(0));
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_dec_ref(v___x_3249_);
v___y_3226_ = v___y_3243_;
v___y_3227_ = v___y_3244_;
v___y_3228_ = v___y_3245_;
v___y_3229_ = v___y_3246_;
v___y_3230_ = v___y_3247_;
goto v___jp_3225_;
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v_goal_3148_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
v___jp_3258_:
{
lean_object* v___x_3266_; 
lean_inc(v___y_3265_);
lean_inc_ref(v___y_3264_);
lean_inc(v___y_3263_);
lean_inc_ref(v___y_3262_);
lean_inc_ref(v___y_3260_);
v___x_3266_ = lean_infer_type(v___y_3260_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = l_Lean_Meta_isExprDefEq(v_a_3267_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; uint8_t v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = lean_unbox(v_a_3269_);
lean_dec(v_a_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v_a_3272_; uint8_t v___x_3273_; 
lean_inc(v_cls_3147_);
v___x_3271_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3147_, v___y_3264_);
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = lean_unbox(v_a_3272_);
lean_dec(v_a_3272_);
if (v___x_3273_ == 0)
{
lean_dec(v_cls_3147_);
v___y_3242_ = v___y_3259_;
v___y_3243_ = v___y_3260_;
v___y_3244_ = v___y_3262_;
v___y_3245_ = v___y_3263_;
v___y_3246_ = v___y_3264_;
v___y_3247_ = v___y_3265_;
goto v___jp_3241_;
}
else
{
lean_object* v___x_3274_; 
lean_inc(v___y_3265_);
lean_inc_ref(v___y_3264_);
lean_inc(v___y_3263_);
lean_inc_ref(v___y_3262_);
lean_inc_ref(v___y_3260_);
v___x_3274_ = lean_infer_type(v___y_3260_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__4);
lean_inc_ref(v___y_3260_);
v___x_3277_ = l_Lean_MessageData_ofExpr(v___y_3260_);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3276_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__6);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = l_Lean_MessageData_ofExpr(v_a_3275_);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__8);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3147_, v___x_3284_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_dec_ref(v___x_3285_);
v___y_3242_ = v___y_3259_;
v___y_3243_ = v___y_3260_;
v___y_3244_ = v___y_3262_;
v___y_3245_ = v___y_3263_;
v___y_3246_ = v___y_3264_;
v___y_3247_ = v___y_3265_;
goto v___jp_3241_;
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3294_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3274_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3274_);
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
}
else
{
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___y_3226_ = v___y_3260_;
v___y_3227_ = v___y_3262_;
v___y_3228_ = v___y_3263_;
v___y_3229_ = v___y_3264_;
v___y_3230_ = v___y_3265_;
goto v___jp_3225_;
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3302_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3268_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3268_);
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
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3310_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3266_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3266_);
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
v___jp_3318_:
{
uint8_t v___x_3331_; 
v___x_3331_ = l_Lean_Expr_isBVar(v___y_3321_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
lean_dec_ref(v___y_3326_);
lean_dec_ref(v___y_3322_);
lean_inc_ref(v___y_3321_);
v___x_3332_ = l_Lean_Meta_Monotonicity_solveMonoCall(v___y_3325_, v___y_3324_, v___y_3321_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3332_);
if (lean_obj_tag(v_a_3333_) == 1)
{
lean_object* v_val_3334_; lean_object* v___x_3335_; lean_object* v_a_3336_; uint8_t v___x_3337_; 
lean_dec_ref(v___y_3320_);
v_val_3334_ = lean_ctor_get(v_a_3333_, 0);
lean_inc(v_val_3334_);
lean_dec_ref(v_a_3333_);
lean_inc(v_cls_3147_);
v___x_3335_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3147_, v___y_3329_);
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = lean_unbox(v_a_3336_);
lean_dec(v_a_3336_);
if (v___x_3337_ == 0)
{
lean_dec_ref(v___y_3321_);
v___y_3259_ = v___y_3319_;
v___y_3260_ = v_val_3334_;
v___y_3261_ = v___y_3323_;
v___y_3262_ = v___y_3327_;
v___y_3263_ = v___y_3328_;
v___y_3264_ = v___y_3329_;
v___y_3265_ = v___y_3330_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3338_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__10);
v___x_3339_ = l_Lean_MessageData_ofExpr(v___y_3321_);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3, &l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3_once, _init_l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst___closed__3);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
lean_inc(v_val_3334_);
v___x_3343_ = l_Lean_indentExpr(v_val_3334_);
v___x_3344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
lean_inc(v_cls_3147_);
v___x_3345_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3147_, v___x_3344_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_dec_ref(v___x_3345_);
v___y_3259_ = v___y_3319_;
v___y_3260_ = v_val_3334_;
v___y_3261_ = v___y_3323_;
v___y_3262_ = v___y_3327_;
v___y_3263_ = v___y_3328_;
v___y_3264_ = v___y_3329_;
v___y_3265_ = v___y_3330_;
goto v___jp_3258_;
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_val_3334_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec(v_a_3333_);
lean_dec_ref(v___y_3323_);
v___x_3354_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__12));
v___x_3355_ = l_Lean_Expr_bindingDomain_x21(v___y_3319_);
v___x_3356_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(v___x_3354_, v___x_3355_, v___y_3320_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; lean_object* v_a_3359_; uint8_t v___x_3360_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v___x_3356_);
lean_inc(v_cls_3147_);
v___x_3358_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__2___redArg(v_cls_3147_, v___y_3329_);
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = lean_unbox(v_a_3359_);
lean_dec(v_a_3359_);
if (v___x_3360_ == 0)
{
lean_dec(v_cls_3147_);
v___y_3165_ = v___y_3319_;
v___y_3166_ = v___y_3321_;
v___y_3167_ = v___x_3331_;
v___y_3168_ = v_a_3357_;
v___y_3169_ = v___y_3327_;
v___y_3170_ = v___y_3328_;
v___y_3171_ = v___y_3329_;
v___y_3172_ = v___y_3330_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3361_; size_t v_sz_3362_; size_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3361_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__14);
v_sz_3362_ = lean_array_size(v_a_3357_);
v___x_3363_ = ((size_t)0ULL);
lean_inc(v_a_3357_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__7(v___x_3331_, v_sz_3362_, v___x_3363_, v_a_3357_);
v___x_3365_ = lean_array_to_list(v___x_3364_);
v___x_3366_ = lean_box(0);
v___x_3367_ = l_List_mapTR_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__8(v___x_3365_, v___x_3366_);
v___x_3368_ = l_Lean_MessageData_ofList(v___x_3367_);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3361_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3147_, v___x_3369_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_dec_ref(v___x_3370_);
v___y_3165_ = v___y_3319_;
v___y_3166_ = v___y_3321_;
v___y_3167_ = v___x_3331_;
v___y_3168_ = v_a_3357_;
v___y_3169_ = v___y_3327_;
v___y_3170_ = v___y_3328_;
v___y_3171_ = v___y_3329_;
v___y_3172_ = v___y_3330_;
goto v___jp_3164_;
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v_a_3357_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3379_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3356_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3356_);
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
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3387_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3332_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3332_);
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
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_dec_ref(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___x_3395_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__1));
v___x_3396_ = l_Lean_Name_mkStr3(v___y_3326_, v___y_3322_, v___x_3395_);
v___x_3397_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3148_, v___x_3396_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v___x_3397_;
}
}
v___jp_3398_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec_ref(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
v___x_3413_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__16);
v___x_3414_ = l_Lean_MessageData_ofConstName(v___y_3402_, v___y_3401_);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2__spec__0___redArg(v___x_3417_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
v___jp_3427_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3434_ = l_Lean_Expr_appFn_x21(v___y_3432_);
lean_dec_ref(v___y_3432_);
v___x_3435_ = l_Lean_Expr_app___override(v___x_3434_, v___y_3433_);
v___x_3436_ = lean_box(0);
v___x_3437_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_3435_, v___x_3436_, v___y_3428_, v___y_3429_, v___y_3431_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3431_);
lean_dec_ref(v___y_3428_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3449_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
lean_inc(v_a_3438_);
v___x_3439_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_3148_, v_a_3438_, v___y_3429_);
lean_dec(v___y_3429_);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; 
v_unused_3450_ = lean_ctor_get(v___x_3439_, 0);
lean_dec(v_unused_3450_);
v___x_3441_ = v___x_3439_;
v_isShared_3442_ = v_isSharedCheck_3449_;
goto v_resetjp_3440_;
}
else
{
lean_dec(v___x_3439_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3449_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3443_ = l_Lean_Expr_mvarId_x21(v_a_3438_);
lean_dec(v_a_3438_);
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3445_);
v___x_3447_ = v___x_3441_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v___y_3429_);
lean_dec(v_goal_3148_);
v_a_3451_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3437_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3437_);
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
v___jp_3459_:
{
if (v___y_3470_ == 0)
{
lean_object* v___x_3471_; 
lean_dec_ref(v___y_3460_);
v___x_3471_ = l_Lean_Expr_lam___override(v___y_3467_, v___y_3469_, v___y_3468_, v___y_3462_);
v___y_3428_ = v___y_3461_;
v___y_3429_ = v___y_3463_;
v___y_3430_ = v___y_3464_;
v___y_3431_ = v___y_3465_;
v___y_3432_ = v___y_3466_;
v___y_3433_ = v___x_3471_;
goto v___jp_3427_;
}
else
{
uint8_t v___x_3472_; 
v___x_3472_ = l_Lean_instBEqBinderInfo_beq(v___y_3462_, v___y_3462_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
lean_dec_ref(v___y_3460_);
v___x_3473_ = l_Lean_Expr_lam___override(v___y_3467_, v___y_3469_, v___y_3468_, v___y_3462_);
v___y_3428_ = v___y_3461_;
v___y_3429_ = v___y_3463_;
v___y_3430_ = v___y_3464_;
v___y_3431_ = v___y_3465_;
v___y_3432_ = v___y_3466_;
v___y_3433_ = v___x_3473_;
goto v___jp_3427_;
}
else
{
lean_dec_ref(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
v___y_3428_ = v___y_3461_;
v___y_3429_ = v___y_3463_;
v___y_3430_ = v___y_3464_;
v___y_3431_ = v___y_3465_;
v___y_3432_ = v___y_3466_;
v___y_3433_ = v___y_3460_;
goto v___jp_3427_;
}
}
}
v___jp_3474_:
{
if (lean_obj_tag(v___y_3475_) == 6)
{
lean_object* v_binderName_3483_; lean_object* v_binderType_3484_; lean_object* v_body_3485_; uint8_t v_binderInfo_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; size_t v___x_3489_; size_t v___x_3490_; uint8_t v___x_3491_; 
v_binderName_3483_ = lean_ctor_get(v___y_3475_, 0);
lean_inc(v_binderName_3483_);
v_binderType_3484_ = lean_ctor_get(v___y_3475_, 1);
v_body_3485_ = lean_ctor_get(v___y_3475_, 2);
v_binderInfo_3486_ = lean_ctor_get_uint8(v___y_3475_, sizeof(void*)*3 + 8);
v___x_3487_ = l_Lean_Expr_bindingDomain_x21(v___y_3475_);
v___x_3488_ = lean_expr_instantiate1(v___y_3482_, v___y_3481_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v___y_3482_);
v___x_3489_ = lean_ptr_addr(v_binderType_3484_);
v___x_3490_ = lean_ptr_addr(v___x_3487_);
v___x_3491_ = lean_usize_dec_eq(v___x_3489_, v___x_3490_);
if (v___x_3491_ == 0)
{
v___y_3460_ = v___y_3475_;
v___y_3461_ = v___y_3476_;
v___y_3462_ = v_binderInfo_3486_;
v___y_3463_ = v___y_3477_;
v___y_3464_ = v___y_3478_;
v___y_3465_ = v___y_3479_;
v___y_3466_ = v___y_3480_;
v___y_3467_ = v_binderName_3483_;
v___y_3468_ = v___x_3488_;
v___y_3469_ = v___x_3487_;
v___y_3470_ = v___x_3491_;
goto v___jp_3459_;
}
else
{
size_t v___x_3492_; size_t v___x_3493_; uint8_t v___x_3494_; 
v___x_3492_ = lean_ptr_addr(v_body_3485_);
v___x_3493_ = lean_ptr_addr(v___x_3488_);
v___x_3494_ = lean_usize_dec_eq(v___x_3492_, v___x_3493_);
v___y_3460_ = v___y_3475_;
v___y_3461_ = v___y_3476_;
v___y_3462_ = v_binderInfo_3486_;
v___y_3463_ = v___y_3477_;
v___y_3464_ = v___y_3478_;
v___y_3465_ = v___y_3479_;
v___y_3466_ = v___y_3480_;
v___y_3467_ = v_binderName_3483_;
v___y_3468_ = v___x_3488_;
v___y_3469_ = v___x_3487_;
v___y_3470_ = v___x_3494_;
goto v___jp_3459_;
}
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec_ref(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v___y_3475_);
v___x_3495_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1);
v___x_3496_ = l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(v___x_3495_);
v___y_3428_ = v___y_3476_;
v___y_3429_ = v___y_3477_;
v___y_3430_ = v___y_3478_;
v___y_3431_ = v___y_3479_;
v___y_3432_ = v___y_3480_;
v___y_3433_ = v___x_3496_;
goto v___jp_3427_;
}
}
v___jp_3497_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3504_ = l_Lean_Expr_appFn_x21(v___y_3502_);
lean_dec_ref(v___y_3502_);
v___x_3505_ = l_Lean_Expr_app___override(v___x_3504_, v___y_3503_);
v___x_3506_ = lean_box(0);
v___x_3507_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_3505_, v___x_3506_, v___y_3498_, v___y_3499_, v___y_3501_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3498_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3519_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3507_);
lean_inc(v_a_3508_);
v___x_3509_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_goal_3148_, v_a_3508_, v___y_3499_);
lean_dec(v___y_3499_);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; 
v_unused_3520_ = lean_ctor_get(v___x_3509_, 0);
lean_dec(v_unused_3520_);
v___x_3511_ = v___x_3509_;
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v___x_3509_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3513_ = l_Lean_Expr_mvarId_x21(v_a_3508_);
lean_dec(v_a_3508_);
v___x_3514_ = lean_box(0);
v___x_3515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3513_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3515_);
v___x_3517_ = v___x_3511_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v___y_3499_);
lean_dec(v_goal_3148_);
v_a_3521_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3507_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3507_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
v___jp_3529_:
{
if (v___y_3540_ == 0)
{
lean_object* v___x_3541_; 
lean_dec_ref(v___y_3530_);
v___x_3541_ = l_Lean_Expr_lam___override(v___y_3539_, v___y_3534_, v___y_3531_, v___y_3536_);
v___y_3498_ = v___y_3532_;
v___y_3499_ = v___y_3533_;
v___y_3500_ = v___y_3535_;
v___y_3501_ = v___y_3537_;
v___y_3502_ = v___y_3538_;
v___y_3503_ = v___x_3541_;
goto v___jp_3497_;
}
else
{
uint8_t v___x_3542_; 
v___x_3542_ = l_Lean_instBEqBinderInfo_beq(v___y_3536_, v___y_3536_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec_ref(v___y_3530_);
v___x_3543_ = l_Lean_Expr_lam___override(v___y_3539_, v___y_3534_, v___y_3531_, v___y_3536_);
v___y_3498_ = v___y_3532_;
v___y_3499_ = v___y_3533_;
v___y_3500_ = v___y_3535_;
v___y_3501_ = v___y_3537_;
v___y_3502_ = v___y_3538_;
v___y_3503_ = v___x_3543_;
goto v___jp_3497_;
}
else
{
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3531_);
v___y_3498_ = v___y_3532_;
v___y_3499_ = v___y_3533_;
v___y_3500_ = v___y_3535_;
v___y_3501_ = v___y_3537_;
v___y_3502_ = v___y_3538_;
v___y_3503_ = v___y_3530_;
goto v___jp_3497_;
}
}
}
v___jp_3544_:
{
if (v___y_3559_ == 0)
{
uint8_t v___x_3560_; 
v___x_3560_ = l_Lean_Expr_isMData(v___y_3558_);
if (v___x_3560_ == 0)
{
if (lean_obj_tag(v___y_3558_) == 8)
{
lean_object* v_declName_3561_; lean_object* v_type_3562_; lean_object* v_value_3563_; lean_object* v_body_3564_; uint8_t v_nondep_3565_; uint8_t v___x_3566_; 
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v_declName_3561_ = lean_ctor_get(v___y_3558_, 0);
lean_inc(v_declName_3561_);
v_type_3562_ = lean_ctor_get(v___y_3558_, 1);
lean_inc_ref(v_type_3562_);
v_value_3563_ = lean_ctor_get(v___y_3558_, 2);
lean_inc_ref(v_value_3563_);
v_body_3564_ = lean_ctor_get(v___y_3558_, 3);
lean_inc_ref(v_body_3564_);
v_nondep_3565_ = lean_ctor_get_uint8(v___y_3558_, sizeof(void*)*4 + 8);
lean_dec_ref(v___y_3558_);
v___x_3566_ = l_Lean_Expr_hasLooseBVars(v_type_3562_);
if (v___x_3566_ == 0)
{
uint8_t v___x_3567_; 
v___x_3567_ = l_Lean_Expr_hasLooseBVars(v_value_3563_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___f_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; 
lean_dec_ref(v___y_3554_);
v___x_3568_ = lean_box(v___y_3552_);
v___x_3569_ = lean_box(v___x_3567_);
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3570_, 0, v___y_3551_);
lean_closure_set(v___f_3570_, 1, v___x_3568_);
lean_closure_set(v___f_3570_, 2, v___x_3569_);
lean_closure_set(v___f_3570_, 3, v_goal_3148_);
lean_closure_set(v___f_3570_, 4, v___y_3548_);
lean_closure_set(v___f_3570_, 5, v_body_3564_);
v___x_3571_ = 0;
v___x_3572_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__9___redArg(v_declName_3561_, v_type_3562_, v_value_3563_, v___f_3570_, v_nondep_3565_, v___x_3571_, v___y_3546_, v___y_3550_, v___y_3553_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3546_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3583_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3577_ = l_Lean_Expr_mvarId_x21(v_a_3573_);
lean_dec(v_a_3573_);
v___x_3578_ = lean_box(0);
v___x_3579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3579_);
v___x_3581_ = v___x_3575_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
v_a_3584_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3572_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3572_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_dec_ref(v_type_3562_);
lean_dec(v_declName_3561_);
lean_dec_ref(v___y_3551_);
v___y_3475_ = v___y_3548_;
v___y_3476_ = v___y_3546_;
v___y_3477_ = v___y_3550_;
v___y_3478_ = v___y_3545_;
v___y_3479_ = v___y_3553_;
v___y_3480_ = v___y_3554_;
v___y_3481_ = v_value_3563_;
v___y_3482_ = v_body_3564_;
goto v___jp_3474_;
}
}
else
{
lean_dec_ref(v_type_3562_);
lean_dec(v_declName_3561_);
lean_dec_ref(v___y_3551_);
v___y_3475_ = v___y_3548_;
v___y_3476_ = v___y_3546_;
v___y_3477_ = v___y_3550_;
v___y_3478_ = v___y_3545_;
v___y_3479_ = v___y_3553_;
v___y_3480_ = v___y_3554_;
v___y_3481_ = v_value_3563_;
v___y_3482_ = v_body_3564_;
goto v___jp_3474_;
}
}
else
{
uint8_t v___x_3592_; 
lean_dec_ref(v___y_3551_);
v___x_3592_ = l_Lean_Expr_isLambda(v___y_3558_);
if (v___x_3592_ == 0)
{
v___y_3319_ = v___y_3548_;
v___y_3320_ = v___y_3557_;
v___y_3321_ = v___y_3558_;
v___y_3322_ = v___y_3555_;
v___y_3323_ = v___y_3554_;
v___y_3324_ = v___y_3547_;
v___y_3325_ = v___y_3549_;
v___y_3326_ = v___y_3556_;
v___y_3327_ = v___y_3546_;
v___y_3328_ = v___y_3550_;
v___y_3329_ = v___y_3553_;
v___y_3330_ = v___y_3545_;
goto v___jp_3318_;
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___x_3593_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__17));
lean_inc_ref(v___y_3555_);
lean_inc_ref(v___y_3556_);
v___x_3594_ = l_Lean_Name_mkStr3(v___y_3556_, v___y_3555_, v___x_3593_);
lean_inc(v___x_3594_);
v___x_3595_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3148_, v___x_3594_, v___y_3546_, v___y_3550_, v___y_3553_, v___y_3545_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
if (lean_obj_tag(v_a_3596_) == 1)
{
lean_object* v_tail_3597_; 
v_tail_3597_ = lean_ctor_get(v_a_3596_, 1);
lean_inc(v_tail_3597_);
if (lean_obj_tag(v_tail_3597_) == 0)
{
lean_object* v_head_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v___x_3594_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v___y_3547_);
v_head_3598_ = lean_ctor_get(v_a_3596_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_a_3596_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v_a_3596_, 1);
lean_dec(v_unused_3625_);
v___x_3600_ = v_a_3596_;
v_isShared_3601_ = v_isSharedCheck_3624_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_head_3598_);
lean_dec(v_a_3596_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3624_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = l_Lean_Expr_bindingName_x21(v___y_3558_);
lean_dec_ref(v___y_3558_);
v___x_3603_ = l_Lean_MVarId_intro(v_head_3598_, v___x_3602_, v___y_3546_, v___y_3550_, v___y_3553_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3546_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3615_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3606_ = v___x_3603_;
v_isShared_3607_ = v_isSharedCheck_3615_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3603_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3615_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v_snd_3608_; lean_object* v___x_3610_; 
v_snd_3608_ = lean_ctor_get(v_a_3604_, 1);
lean_inc(v_snd_3608_);
lean_dec(v_a_3604_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v_snd_3608_);
v___x_3610_ = v___x_3600_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_snd_3608_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_tail_3597_);
v___x_3610_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3610_);
v___x_3612_ = v___x_3606_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
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
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_del_object(v___x_3600_);
v_a_3616_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3603_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3603_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3596_);
lean_dec(v_tail_3597_);
v___y_3399_ = v___y_3548_;
v___y_3400_ = v___y_3557_;
v___y_3401_ = v___x_3560_;
v___y_3402_ = v___x_3594_;
v___y_3403_ = v___y_3558_;
v___y_3404_ = v___y_3554_;
v___y_3405_ = v___y_3555_;
v___y_3406_ = v___y_3549_;
v___y_3407_ = v___y_3547_;
v___y_3408_ = v___y_3556_;
v___y_3409_ = v___y_3546_;
v___y_3410_ = v___y_3550_;
v___y_3411_ = v___y_3553_;
v___y_3412_ = v___y_3545_;
goto v___jp_3398_;
}
}
else
{
lean_dec(v_a_3596_);
v___y_3399_ = v___y_3548_;
v___y_3400_ = v___y_3557_;
v___y_3401_ = v___x_3560_;
v___y_3402_ = v___x_3594_;
v___y_3403_ = v___y_3558_;
v___y_3404_ = v___y_3554_;
v___y_3405_ = v___y_3555_;
v___y_3406_ = v___y_3549_;
v___y_3407_ = v___y_3547_;
v___y_3408_ = v___y_3556_;
v___y_3409_ = v___y_3546_;
v___y_3410_ = v___y_3550_;
v___y_3411_ = v___y_3553_;
v___y_3412_ = v___y_3545_;
goto v___jp_3398_;
}
}
else
{
lean_dec(v___x_3594_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
return v___x_3595_;
}
}
}
}
else
{
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3551_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
if (lean_obj_tag(v___y_3548_) == 6)
{
lean_object* v_binderName_3626_; lean_object* v_binderType_3627_; lean_object* v_body_3628_; uint8_t v_binderInfo_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; size_t v___x_3632_; size_t v___x_3633_; uint8_t v___x_3634_; 
v_binderName_3626_ = lean_ctor_get(v___y_3548_, 0);
lean_inc(v_binderName_3626_);
v_binderType_3627_ = lean_ctor_get(v___y_3548_, 1);
v_body_3628_ = lean_ctor_get(v___y_3548_, 2);
v_binderInfo_3629_ = lean_ctor_get_uint8(v___y_3548_, sizeof(void*)*3 + 8);
v___x_3630_ = l_Lean_Expr_bindingDomain_x21(v___y_3548_);
v___x_3631_ = l_Lean_Expr_mdataExpr_x21(v___y_3558_);
lean_dec_ref(v___y_3558_);
v___x_3632_ = lean_ptr_addr(v_binderType_3627_);
v___x_3633_ = lean_ptr_addr(v___x_3630_);
v___x_3634_ = lean_usize_dec_eq(v___x_3632_, v___x_3633_);
if (v___x_3634_ == 0)
{
v___y_3530_ = v___y_3548_;
v___y_3531_ = v___x_3631_;
v___y_3532_ = v___y_3546_;
v___y_3533_ = v___y_3550_;
v___y_3534_ = v___x_3630_;
v___y_3535_ = v___y_3545_;
v___y_3536_ = v_binderInfo_3629_;
v___y_3537_ = v___y_3553_;
v___y_3538_ = v___y_3554_;
v___y_3539_ = v_binderName_3626_;
v___y_3540_ = v___x_3634_;
goto v___jp_3529_;
}
else
{
size_t v___x_3635_; size_t v___x_3636_; uint8_t v___x_3637_; 
v___x_3635_ = lean_ptr_addr(v_body_3628_);
v___x_3636_ = lean_ptr_addr(v___x_3631_);
v___x_3637_ = lean_usize_dec_eq(v___x_3635_, v___x_3636_);
v___y_3530_ = v___y_3548_;
v___y_3531_ = v___x_3631_;
v___y_3532_ = v___y_3546_;
v___y_3533_ = v___y_3550_;
v___y_3534_ = v___x_3630_;
v___y_3535_ = v___y_3545_;
v___y_3536_ = v_binderInfo_3629_;
v___y_3537_ = v___y_3553_;
v___y_3538_ = v___y_3554_;
v___y_3539_ = v_binderName_3626_;
v___y_3540_ = v___x_3637_;
goto v___jp_3529_;
}
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3548_);
v___x_3638_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__0___closed__1);
v___x_3639_ = l_panic___at___00Lean_Meta_Monotonicity_headBetaUnderLambda_spec__0(v___x_3638_);
v___y_3498_ = v___y_3546_;
v___y_3499_ = v___y_3550_;
v___y_3500_ = v___y_3545_;
v___y_3501_ = v___y_3553_;
v___y_3502_ = v___y_3554_;
v___y_3503_ = v___x_3639_;
goto v___jp_3497_;
}
}
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v___y_3551_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___x_3640_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__18));
v___x_3641_ = l_Lean_Name_mkStr3(v___y_3556_, v___y_3555_, v___x_3640_);
v___x_3642_ = l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_applyConst(v_goal_3148_, v___x_3641_, v___y_3546_, v___y_3550_, v___y_3553_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3546_);
return v___x_3642_;
}
}
v___jp_3643_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___f_3660_; uint8_t v___x_3661_; 
v___x_3658_ = l_Lean_Meta_Monotonicity_headBetaUnderLambda(v_f_3653_);
v___x_3659_ = l_Lean_Expr_bindingBody_x21(v___x_3658_);
lean_inc_ref(v___x_3659_);
v___f_3660_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3660_, 0, v___x_3659_);
v___x_3661_ = l_Lean_Expr_hasLooseBVars(v___x_3659_);
if (v___x_3661_ == 0)
{
v___y_3545_ = v___y_3657_;
v___y_3546_ = v___y_3654_;
v___y_3547_ = v___y_3651_;
v___y_3548_ = v___x_3658_;
v___y_3549_ = v___y_3650_;
v___y_3550_ = v___y_3655_;
v___y_3551_ = v___y_3645_;
v___y_3552_ = v___y_3644_;
v___y_3553_ = v___y_3656_;
v___y_3554_ = v___y_3649_;
v___y_3555_ = v___y_3648_;
v___y_3556_ = v___y_3652_;
v___y_3557_ = v___f_3660_;
v___y_3558_ = v___x_3659_;
v___y_3559_ = v___y_3647_;
goto v___jp_3544_;
}
else
{
v___y_3545_ = v___y_3657_;
v___y_3546_ = v___y_3654_;
v___y_3547_ = v___y_3651_;
v___y_3548_ = v___x_3658_;
v___y_3549_ = v___y_3650_;
v___y_3550_ = v___y_3655_;
v___y_3551_ = v___y_3645_;
v___y_3552_ = v___y_3644_;
v___y_3553_ = v___y_3656_;
v___y_3554_ = v___y_3649_;
v___y_3555_ = v___y_3648_;
v___y_3556_ = v___y_3652_;
v___y_3557_ = v___f_3660_;
v___y_3558_ = v___x_3659_;
v___y_3559_ = v___y_3646_;
goto v___jp_3544_;
}
}
v___jp_3662_:
{
lean_object* v___x_3667_; 
lean_inc(v_goal_3148_);
v___x_3667_ = l_Lean_MVarId_getType(v_goal_3148_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; uint8_t v___x_3669_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3667_);
v___x_3669_ = l_Lean_Expr_isForall(v_a_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; 
lean_inc(v_a_3668_);
v___x_3670_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3668_, v___y_3664_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v___x_3670_);
v___x_3672_ = l_Lean_Expr_cleanupAnnotations(v_a_3671_);
v___x_3673_ = l_Lean_Expr_isApp(v___x_3672_);
if (v___x_3673_ == 0)
{
lean_dec_ref(v___x_3672_);
lean_dec(v_a_3668_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___y_3156_ = v___y_3663_;
v___y_3157_ = v___y_3664_;
v___y_3158_ = v___y_3665_;
v___y_3159_ = v___y_3666_;
goto v___jp_3155_;
}
else
{
lean_object* v_arg_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v_arg_3674_ = lean_ctor_get(v___x_3672_, 1);
lean_inc_ref(v_arg_3674_);
v___x_3675_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3672_);
v___x_3676_ = l_Lean_Expr_isApp(v___x_3675_);
if (v___x_3676_ == 0)
{
lean_dec_ref(v___x_3675_);
lean_dec_ref(v_arg_3674_);
lean_dec(v_a_3668_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___y_3156_ = v___y_3663_;
v___y_3157_ = v___y_3664_;
v___y_3158_ = v___y_3665_;
v___y_3159_ = v___y_3666_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3677_; uint8_t v___x_3678_; 
v___x_3677_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3675_);
v___x_3678_ = l_Lean_Expr_isApp(v___x_3677_);
if (v___x_3678_ == 0)
{
lean_dec_ref(v___x_3677_);
lean_dec_ref(v_arg_3674_);
lean_dec(v_a_3668_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___y_3156_ = v___y_3663_;
v___y_3157_ = v___y_3664_;
v___y_3158_ = v___y_3665_;
v___y_3159_ = v___y_3666_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3677_);
v___x_3680_ = l_Lean_Expr_isApp(v___x_3679_);
if (v___x_3680_ == 0)
{
lean_dec_ref(v___x_3679_);
lean_dec_ref(v_arg_3674_);
lean_dec(v_a_3668_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___y_3156_ = v___y_3663_;
v___y_3157_ = v___y_3664_;
v___y_3158_ = v___y_3665_;
v___y_3159_ = v___y_3666_;
goto v___jp_3155_;
}
else
{
lean_object* v_arg_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v_arg_3681_ = lean_ctor_get(v___x_3679_, 1);
lean_inc_ref(v_arg_3681_);
v___x_3682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3679_);
v___x_3683_ = l_Lean_Expr_isApp(v___x_3682_);
if (v___x_3683_ == 0)
{
lean_dec_ref(v___x_3682_);
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v_arg_3674_);
lean_dec(v_a_3668_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___y_3156_ = v___y_3663_;
v___y_3157_ = v___y_3664_;
v___y_3158_ = v___y_3665_;
v___y_3159_ = v___y_3666_;
goto v___jp_3155_;
}
else
{
lean_object* v_arg_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_arg_3684_ = lean_ctor_get(v___x_3682_, 1);
lean_inc_ref(v_arg_3684_);
v___x_3685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3682_);
v___x_3686_ = ((lean_object*)(l_Lean_Meta_Monotonicity_initFn___closed__3_00___x40_Lean_Elab_Tactic_Monotonicity_4195581025____hygCtx___hyg_2_));
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__Lean_Meta_Monotonicity_initFn___lam__0___closed__2_00___x40_Lean_Elab_Tactic_Monotonicity_1250514167____hygCtx___hyg_2_));
v___x_3688_ = ((lean_object*)(l_Lean_Meta_Monotonicity_solveMonoCall___closed__9));
v___x_3689_ = l_Lean_Expr_isConstOf(v___x_3685_, v___x_3688_);
lean_dec_ref(v___x_3685_);
if (v___x_3689_ == 0)
{
lean_dec_ref(v_arg_3684_);
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v_arg_3674_);
lean_dec(v_a_3668_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___y_3156_ = v___y_3663_;
v___y_3157_ = v___y_3664_;
v___y_3158_ = v___y_3665_;
v___y_3159_ = v___y_3666_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3690_; lean_object* v_a_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3690_ = l_Lean_instantiateMVars___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__0___redArg(v_arg_3674_, v___y_3664_);
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = l_Lean_Expr_headBeta(v_a_3691_);
v___x_3693_ = l_Lean_Expr_isLambda(v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Meta_etaExpand(v___x_3692_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3694_);
lean_inc(v_a_3668_);
v___y_3644_ = v___x_3689_;
v___y_3645_ = v_a_3668_;
v___y_3646_ = v___x_3669_;
v___y_3647_ = v___x_3689_;
v___y_3648_ = v___x_3687_;
v___y_3649_ = v_a_3668_;
v___y_3650_ = v_arg_3684_;
v___y_3651_ = v_arg_3681_;
v___y_3652_ = v___x_3686_;
v_f_3653_ = v_a_3695_;
v___y_3654_ = v___y_3663_;
v___y_3655_ = v___y_3664_;
v___y_3656_ = v___y_3665_;
v___y_3657_ = v___y_3666_;
goto v___jp_3643_;
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v_arg_3684_);
lean_dec_ref(v_arg_3681_);
lean_dec(v_a_3668_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3696_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3694_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3694_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_inc(v_a_3668_);
v___y_3644_ = v___x_3689_;
v___y_3645_ = v_a_3668_;
v___y_3646_ = v___x_3669_;
v___y_3647_ = v___x_3689_;
v___y_3648_ = v___x_3687_;
v___y_3649_ = v_a_3668_;
v___y_3650_ = v_arg_3684_;
v___y_3651_ = v_arg_3681_;
v___y_3652_ = v___x_3686_;
v_f_3653_ = v___x_3692_;
v___y_3654_ = v___y_3663_;
v___y_3655_ = v___y_3664_;
v___y_3656_ = v___y_3665_;
v___y_3657_ = v___y_3666_;
goto v___jp_3643_;
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
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_a_3668_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3704_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3670_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3670_);
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
lean_object* v___x_3712_; 
lean_dec(v_a_3668_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_cls_3147_);
v___x_3712_ = l_Lean_Meta_intro1Core(v_goal_3148_, v___x_3669_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3730_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3730_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3730_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_snd_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3728_; 
v_snd_3717_ = lean_ctor_get(v_a_3713_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_a_3713_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v_a_3713_, 0);
lean_dec(v_unused_3729_);
v___x_3719_ = v_a_3713_;
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_snd_3717_);
lean_dec(v_a_3713_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_box(0);
if (v_isShared_3720_ == 0)
{
lean_ctor_set_tag(v___x_3719_, 1);
lean_ctor_set(v___x_3719_, 1, v___x_3721_);
lean_ctor_set(v___x_3719_, 0, v_snd_3717_);
v___x_3723_ = v___x_3719_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_snd_3717_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3723_);
v___x_3725_ = v___x_3715_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3712_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3712_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3739_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3667_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3667_);
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
v_resetjp_3749_:
{
uint8_t v___x_3752_; 
v___x_3752_ = lean_unbox(v_a_3748_);
lean_dec(v_a_3748_);
if (v___x_3752_ == 0)
{
lean_del_object(v___x_3750_);
v___y_3663_ = v___y_3150_;
v___y_3664_ = v___y_3151_;
v___y_3665_ = v___y_3152_;
v___y_3666_ = v___y_3153_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3753_ = lean_obj_once(&l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20, &l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20_once, _init_l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___closed__20);
lean_inc(v_goal_3148_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set_tag(v___x_3750_, 1);
lean_ctor_set(v___x_3750_, 0, v_goal_3148_);
v___x_3755_ = v___x_3750_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_goal_3148_);
v___x_3755_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3753_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
lean_inc(v_cls_3147_);
v___x_3757_ = l_Lean_addTrace___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__3(v_cls_3147_, v___x_3756_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_dec_ref(v___x_3757_);
v___y_3663_ = v___y_3150_;
v___y_3664_ = v___y_3151_;
v___y_3665_ = v___y_3152_;
v___y_3666_ = v___y_3153_;
goto v___jp_3662_;
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v_failK_3149_);
lean_dec(v_goal_3148_);
lean_dec(v_cls_3147_);
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3757_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___boxed(lean_object* v_cls_3768_, lean_object* v_goal_3769_, lean_object* v_failK_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Meta_Monotonicity_solveMonoStep___lam__2(v_cls_3768_, v_goal_3769_, v_failK_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep(lean_object* v_failK_3777_, lean_object* v_goal_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_cls_3784_; lean_object* v___f_3785_; lean_object* v___x_3786_; 
v_cls_3784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2));
lean_inc(v_goal_3778_);
v___f_3785_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMonoStep___lam__2___boxed), 8, 3);
lean_closure_set(v___f_3785_, 0, v_cls_3784_);
lean_closure_set(v___f_3785_, 1, v_goal_3778_);
lean_closure_set(v___f_3785_, 2, v_failK_3777_);
v___x_3786_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__10___redArg(v_goal_3778_, v___f_3785_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMonoStep___boxed(lean_object* v_failK_3787_, lean_object* v_goal_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Meta_Monotonicity_solveMonoStep(v_failK_3787_, v_goal_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1(lean_object* v_mvarId_3795_, lean_object* v_val_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___redArg(v_mvarId_3795_, v_val_3796_, v___y_3798_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1___boxed(lean_object* v_mvarId_3803_, lean_object* v_val_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1(v_mvarId_3803_, v_val_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5(lean_object* v_00_u03b1_3811_, lean_object* v_name_3812_, uint8_t v_bi_3813_, lean_object* v_type_3814_, lean_object* v_k_3815_, uint8_t v_kind_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___redArg(v_name_3812_, v_bi_3813_, v_type_3814_, v_k_3815_, v_kind_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3823_, lean_object* v_name_3824_, lean_object* v_bi_3825_, lean_object* v_type_3826_, lean_object* v_k_3827_, lean_object* v_kind_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
uint8_t v_bi_boxed_3834_; uint8_t v_kind_boxed_3835_; lean_object* v_res_3836_; 
v_bi_boxed_3834_ = lean_unbox(v_bi_3825_);
v_kind_boxed_3835_ = lean_unbox(v_kind_3828_);
v_res_3836_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4_spec__5(v_00_u03b1_3823_, v_name_3824_, v_bi_boxed_3834_, v_type_3826_, v_k_3827_, v_kind_boxed_3835_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4(lean_object* v_00_u03b1_3837_, lean_object* v_name_3838_, lean_object* v_type_3839_, lean_object* v_k_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___redArg(v_name_3838_, v_type_3839_, v_k_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4___boxed(lean_object* v_00_u03b1_3847_, lean_object* v_name_3848_, lean_object* v_type_3849_, lean_object* v_k_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__4(v_00_u03b1_3847_, v_name_3848_, v_type_3849_, v_k_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6(lean_object* v_upperBound_3857_, lean_object* v___x_3858_, uint8_t v___x_3859_, lean_object* v_inst_3860_, lean_object* v_R_3861_, lean_object* v_a_3862_, lean_object* v_b_3863_, lean_object* v_c_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___redArg(v_upperBound_3857_, v___x_3858_, v___x_3859_, v_a_3862_, v_b_3863_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6___boxed(lean_object* v_upperBound_3871_, lean_object* v___x_3872_, lean_object* v___x_3873_, lean_object* v_inst_3874_, lean_object* v_R_3875_, lean_object* v_a_3876_, lean_object* v_b_3877_, lean_object* v_c_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
uint8_t v___x_43381__boxed_3884_; lean_object* v_res_3885_; 
v___x_43381__boxed_3884_ = lean_unbox(v___x_3873_);
v_res_3885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__6(v_upperBound_3871_, v___x_3872_, v___x_43381__boxed_3884_, v_inst_3874_, v_R_3875_, v_a_3876_, v_b_3877_, v_c_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v___x_3872_);
lean_dec(v_upperBound_3871_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1(lean_object* v_00_u03b2_3886_, lean_object* v_x_3887_, lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1___redArg(v_x_3887_, v_x_3888_, v_x_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3891_, lean_object* v_x_3892_, size_t v_x_3893_, size_t v_x_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___redArg(v_x_3892_, v_x_3893_, v_x_3894_, v_x_3895_, v_x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3898_, lean_object* v_x_3899_, lean_object* v_x_3900_, lean_object* v_x_3901_, lean_object* v_x_3902_, lean_object* v_x_3903_){
_start:
{
size_t v_x_43417__boxed_3904_; size_t v_x_43418__boxed_3905_; lean_object* v_res_3906_; 
v_x_43417__boxed_3904_ = lean_unbox_usize(v_x_3900_);
lean_dec(v_x_3900_);
v_x_43418__boxed_3905_ = lean_unbox_usize(v_x_3901_);
lean_dec(v_x_3901_);
v_res_3906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5(v_00_u03b2_3898_, v_x_3899_, v_x_43417__boxed_3904_, v_x_43418__boxed_3905_, v_x_3902_, v_x_3903_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13(lean_object* v_00_u03b2_3907_, lean_object* v_n_3908_, lean_object* v_k_3909_, lean_object* v_v_3910_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13___redArg(v_n_3908_, v_k_3909_, v_v_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14(lean_object* v_00_u03b2_3912_, size_t v_depth_3913_, lean_object* v_keys_3914_, lean_object* v_vals_3915_, lean_object* v_heq_3916_, lean_object* v_i_3917_, lean_object* v_entries_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___redArg(v_depth_3913_, v_keys_3914_, v_vals_3915_, v_i_3917_, v_entries_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14___boxed(lean_object* v_00_u03b2_3920_, lean_object* v_depth_3921_, lean_object* v_keys_3922_, lean_object* v_vals_3923_, lean_object* v_heq_3924_, lean_object* v_i_3925_, lean_object* v_entries_3926_){
_start:
{
size_t v_depth_boxed_3927_; lean_object* v_res_3928_; 
v_depth_boxed_3927_ = lean_unbox_usize(v_depth_3921_);
lean_dec(v_depth_3921_);
v_res_3928_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__14(v_00_u03b2_3920_, v_depth_boxed_3927_, v_keys_3922_, v_vals_3923_, v_heq_3924_, v_i_3925_, v_entries_3926_);
lean_dec_ref(v_vals_3923_);
lean_dec_ref(v_keys_3922_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14(lean_object* v_00_u03b2_3929_, lean_object* v_x_3930_, lean_object* v_x_3931_, lean_object* v_x_3932_, lean_object* v_x_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__1_spec__1_spec__5_spec__13_spec__14___redArg(v_x_3930_, v_x_3931_, v_x_3932_, v_x_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0(lean_object* v_failK_3935_, lean_object* v_as_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
if (lean_obj_tag(v_as_3936_) == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
lean_dec_ref(v_failK_3935_);
v___x_3942_ = lean_box(0);
v___x_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
return v___x_3943_;
}
else
{
lean_object* v_head_3944_; lean_object* v_tail_3945_; lean_object* v___x_3946_; 
v_head_3944_ = lean_ctor_get(v_as_3936_, 0);
lean_inc(v_head_3944_);
v_tail_3945_ = lean_ctor_get(v_as_3936_, 1);
lean_inc(v_tail_3945_);
lean_dec_ref(v_as_3936_);
lean_inc_ref(v_failK_3935_);
v___x_3946_ = l_Lean_Meta_Monotonicity_solveMono(v_failK_3935_, v_head_3944_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_dec_ref(v___x_3946_);
v_as_3936_ = v_tail_3945_;
goto _start;
}
else
{
lean_dec(v_tail_3945_);
lean_dec_ref(v_failK_3935_);
return v___x_3946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMono(lean_object* v_failK_3948_, lean_object* v_goal_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3955_; 
lean_inc_ref(v_failK_3948_);
v___x_3955_ = l_Lean_Meta_Monotonicity_solveMonoStep(v_failK_3948_, v_goal_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref(v___x_3955_);
v___x_3957_ = l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0(v_failK_3948_, v_a_3956_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
return v___x_3957_;
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec_ref(v_failK_3948_);
v_a_3958_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3955_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3955_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_solveMono___boxed(lean_object* v_failK_3966_, lean_object* v_goal_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_Meta_Monotonicity_solveMono(v_failK_3966_, v_goal_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0___boxed(lean_object* v_failK_3974_, lean_object* v_as_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_List_forM___at___00Lean_Meta_Monotonicity_solveMono_spec__0(v_failK_3974_, v_as_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0(lean_object* v___x_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3984_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v_a_3993_; lean_object* v___x_3994_; 
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_a_3993_);
lean_dec_ref(v___x_3992_);
v___x_3994_ = l_Lean_Meta_Monotonicity_solveMonoStep(v___x_3982_, v_a_3993_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3996_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref(v___x_3994_);
v___x_3996_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3995_, v___y_3984_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4004_; 
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; 
v_unused_4005_ = lean_ctor_get(v___x_3996_, 0);
lean_dec(v_unused_4005_);
v___x_3998_ = v___x_3996_;
v_isShared_3999_ = v_isSharedCheck_4004_;
goto v_resetjp_3997_;
}
else
{
lean_dec(v___x_3996_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4004_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_4000_ = lean_box(0);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 0, v___x_4000_);
v___x_4002_ = v___x_3998_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
else
{
return v___x_3996_;
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3994_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3994_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec_ref(v___x_3982_);
v_a_4014_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3992_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3992_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0___boxed(lean_object* v___x_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___lam__0(v___x_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg(lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___f_4045_; lean_object* v___x_4046_; 
v___f_4045_ = ((lean_object*)(l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___closed__1));
v___x_4046_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4045_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___redArg___boxed(lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_Meta_Monotonicity_evalMonotonicity___redArg(v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity(lean_object* v___stx_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_Meta_Monotonicity_evalMonotonicity___redArg(v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___boxed(lean_object* v___stx_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_Meta_Monotonicity_evalMonotonicity(v___stx_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec_ref(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v___stx_4068_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1(){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4090_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4091_ = ((lean_object*)(l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__0));
v___x_4092_ = ((lean_object*)(l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___closed__2));
v___x_4093_ = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_evalMonotonicity___boxed), 10, 0);
v___x_4094_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4090_, v___x_4091_, v___x_4092_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1___boxed(lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Meta_Monotonicity_evalMonotonicity___regBuiltin_Lean_Meta_Monotonicity_evalMonotonicity__1();
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4128_; uint8_t v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Monotonicity_solveMonoStep_spec__5___closed__2));
v___x_4129_ = 0;
v___x_4130_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Monotonicity_0__initFn___closed__9_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_));
v___x_4131_ = l_Lean_registerTraceClass(v___x_4128_, v___x_4129_, v___x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2____boxed(lean_object* v_a_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l___private_Lean_Elab_Tactic_Monotonicity_0__initFn_00___x40_Lean_Elab_Tactic_Monotonicity_67824763____hygCtx___hyg_2_();
return v_res_4133_;
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
